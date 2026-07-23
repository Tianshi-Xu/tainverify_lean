/- Distributed bootstrap for the next Layer-2 reconstruction slice.
   This file deliberately uses only distributed node algebra after importing the
   completed Layer-1 MoE boundary; no post-MoE ring reconstruction is used. -/
import denote.yoco_goals.Layer1TokenDependencyCone
import denote.yoco_goals.DistributedMigrationGears

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 10000000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/- Graph certificates are kept separate from the tensor algebra below.  This
   keeps every use of the distributed evaluator concrete and auditable. -/
private theorem l2d_reshape (g : GraphDecl) (init : Store) (k r i o hd : Nat)
    (tl : List Nat) (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_reshape", ins := [i], outs := [o], params := hd :: tl })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributed g init o =
      fw_view (hd :: tl) (denoteGraphDistributed g init i) :=
  distributed_reduce1 g init k _ i o (fw_view (hd :: tl)) hk hn (by simp)
    (fun s => applyNode_fw_reshape_out g s r i o (hd :: tl)) hdn hdw hpn hpw

private theorem l2d_view (g : GraphDecl) (init : Store) (k r i o hd : Nat)
    (tl : List Nat) (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_view", ins := [i], outs := [o], params := hd :: tl })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributed g init o =
      fw_view (hd :: tl) (denoteGraphDistributed g init i) :=
  distributed_reduce1 g init k _ i o (fw_view (hd :: tl)) hk hn (by simp)
    (fun s => applyNode_fw_view_out g s r hd tl i o) hdn hdw hpn hpw

private theorem l2d_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_mix_precision_linear", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributed g init o =
      fw_linear (denoteGraphDistributed g init x) (denoteGraphDistributed g init w) :=
  distributed_reduce2 g init k _ x w o fw_linear hk hn (by simp)
    (fun s => applyNode_fw_mix_precision_linear_out_1p g s r x w o)
    hdn hdw hpn hpx hpw

private theorem l2d_per_head_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_per_head_mix_precision_linear", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributed g init o =
      fw_per_head_linear (denoteGraphDistributed g init x) (denoteGraphDistributed g init w) :=
  distributed_reduce2 g init k _ x w o fw_per_head_linear hk hn (by simp)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out g s r x w o [])
    hdn hdw hpn hpx hpw

private theorem l2d_chunk (g : GraphDecl) (init : Store) (k r i o d : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.ChunkPrim", ins := [i], outs := [o], params := [d] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributed g init o =
      chunkPrimDimN d g.numRanks r (denoteGraphDistributed g init i) :=
  distributed_reduce1 g init k _ i o (fun t => chunkPrimDimN d g.numRanks r t)
    hk hn (by simp) (fun s => applyNode_chunkPrimDimN_out g s r i o d) hdn hdw hpn hpw

private theorem l2d_sigmoid (g : GraphDecl) (init : Store) (k r i o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_sigmoid", ins := [i], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributed g init o = fw_sigmoid (denoteGraphDistributed g init i) :=
  distributed_reduce1 g init k _ i o fw_sigmoid hk hn (by simp)
    (fun s => applyNode_fw_sigmoid_out g s r i o []) hdn hdw hpn hpw

private theorem l2d_swiglu (g : GraphDecl) (init : Store) (k r x y o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_swiglu", ins := [x, y], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpy : ∀ n ∈ g.nodes.drop k, y ∉ n.outs) :
    denoteGraphDistributed g init o =
      fw_swiglu (denoteGraphDistributed g init x) (denoteGraphDistributed g init y) :=
  distributed_reduce2 g init k _ x y o fw_swiglu hk hn (by simp)
    (fun s => applyNode_fw_swiglu_out g s r x y o []) hdn hdw hpn hpx hpy

private theorem l2d_mul (g : GraphDecl) (init : Store) (k r x y o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_mul", ins := [x, y], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpy : ∀ n ∈ g.nodes.drop k, y ∉ n.outs) :
    denoteGraphDistributed g init o =
      elemwiseMul (denoteGraphDistributed g init x) (denoteGraphDistributed g init y) :=
  distributed_reduce2 g init k _ x y o elemwiseMul hk hn (by simp)
    (fun s => applyNode_fw_mul_out g s r x y o) hdn hdw hpn hpx hpy

/-! ### First expert-input branch after the Layer-1 MoE bootstrap -/

/-- 4769 is the position-2 fanout of 4759 followed by its identity reshape.
The completed 4768 theorem is available from `Layer1TokenDependencyCone`; this
proof only ports the two concrete nodes that produce 4769. -/
theorem recon_intermediateGoal_4769_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4769
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have h4759 := recon_intermediateGoal_4759_distributed initSM initPM hSM hPM hInit
  have hv4759 : denoteGraphDistributed sm initSM 4759 =
      denoteGraphDistributed pm initPM 4759 :=
    oneTp_valeq intermediateGoal_4759 _ _ 4759 rfl rfl rfl rfl h4759
  have hs4759 : (denoteGraphDistributed sm initSM 4759).shape = [4096, 1024] := h4759.1
  have s7475 : denoteGraphDistributed sm initSM 7475 =
      id (denoteGraphDistributed sm initSM 4759) :=
    distributed_reduce1 sm initSM 57
      { rank := 0, op := "OpName.FW_multiref", ins := [4759],
        outs := [7467, 7471, 7475, 7479, 7483], params := [5] }
      4759 7475 id (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out sm s 0 4759 7467 7471 7475 7479 7483
        (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p11905 : denoteGraphDistributed pm initPM 11905 =
      id (denoteGraphDistributed pm initPM 4759) :=
    distributed_reduce1 pm initPM 166
      { rank := 1, op := "OpName.FW_multiref", ins := [4759],
        outs := [11903, 11904, 11905, 11906, 11907], params := [5] }
      4759 11905 id (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos2_out pm s 1 4759 11903 11904 11905 11906 11907
        (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s7475 p11905
  have hs7475 : (denoteGraphDistributed sm initSM 7475).shape = [4096, 1024] := by
    rw [s7475]
    exact hs4759
  have rSM : denoteGraphDistributed sm initSM 4769 =
      fw_view [4096, 1024] (denoteGraphDistributed sm initSM 7475) :=
    distributed_reduce1 sm initSM 59
      { rank := 0, op := "OpName.FW_reshape", ins := [7475], outs := [4769],
        params := [4096, 1024] }
      7475 4769 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_reshape_out sm s 0 7475 4769 [4096, 1024])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraphDistributed pm initPM 4769 =
      fw_view [4096, 1024] (denoteGraphDistributed pm initPM 11905) :=
    distributed_reduce1 pm initPM 174
      { rank := 1, op := "OpName.FW_reshape", ins := [11905], outs := [4769],
        params := [4096, 1024] }
      11905 4769 (fw_view [4096, 1024]) (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_reshape_out pm s 1 11905 4769 [4096, 1024])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraphDistributed sm initSM 4769 =
      denoteGraphDistributed pm initPM 4769 := by
    rw [rSM, rPM, s7475, p11905, hv4759]
  have hshape : (denoteGraphDistributed sm initSM 4769).shape = [4096, 1024] := by
    rw [rSM, fw_view_id_shape [4096, 1024] _ hs7475]
    exact hs7475
  exact wrap_1tp_gen (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM)
    intermediateGoal_4769 4769 [4096, 1024] rfl rfl rfl rfl rfl rfl hval hshape

/-- 4771 is the expert-0 projection.  Its weight is recovered directly from
`hInit` and lifted through both distributed graphs by never-written facts. -/
theorem recon_intermediateGoal_4771_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4771
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have h4769 := recon_intermediateGoal_4769_distributed initSM initPM hSM hPM hInit
  have hv4769 : denoteGraphDistributed sm initSM 4769 =
      denoteGraphDistributed pm initPM 4769 :=
    oneTp_valeq intermediateGoal_4769 _ _ 4769 rfl rfl rfl rfl h4769
  have hs4769 : (denoteGraphDistributed sm initSM 4769).shape = [4096, 1024] := h4769.1
  have hw4770 : denoteGraphDistributed sm initSM 4770 =
      denoteGraphDistributed pm initPM 4770 :=
    distributed_init_singleton_value initSM initPM hInit initGoal_4770
      (by native_decide) 4770 rfl rfl rfl rfl layer1_sm_nodes_nonempty
      (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hsw4770 : (denoteGraphDistributed sm initSM 4770).shape = [1, 1024] :=
    distributed_init_singleton_shape initSM initPM hInit initGoal_4770
      (by native_decide) 4770 [1, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have rSM : denoteGraphDistributed sm initSM 4771 =
      fw_linear (denoteGraphDistributed sm initSM 4769)
        (denoteGraphDistributed sm initSM 4770) :=
    distributed_reduce2 sm initSM 63
      { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4769, 4770], outs := [4771] }
      4769 4770 4771 fw_linear (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p sm s 0 4769 4770 4771)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rPM : denoteGraphDistributed pm initPM 4771 =
      fw_linear (denoteGraphDistributed pm initPM 4769)
        (denoteGraphDistributed pm initPM 4770) :=
    distributed_reduce2 pm initPM 180
      { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4769, 4770], outs := [4771] }
      4769 4770 4771 fw_linear (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_mix_precision_linear_out_1p pm s 1 4769 4770 4771)
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have hval : denoteGraphDistributed sm initSM 4771 =
      denoteGraphDistributed pm initPM 4771 := by
    rw [rSM, rPM, hv4769, hw4770]
  have hshape : (denoteGraphDistributed sm initSM 4771).shape = [4096, 1] := by
    rw [rSM]
    exact fw_linear_2d_shape 4096 1024 1 _ _ hs4769 hsw4770
  exact wrap_1tp_gen (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM)
    intermediateGoal_4771 4771 [4096, 1] rfl rfl rfl rfl rfl rfl hval hshape

/-- 4772 is the identity view of the expert-0 projection. -/
theorem recon_intermediateGoal_4772_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4772
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have h4771 := recon_intermediateGoal_4771_distributed initSM initPM hSM hPM hInit
  have hv4771 : denoteGraphDistributed sm initSM 4771 =
      denoteGraphDistributed pm initPM 4771 :=
    oneTp_valeq intermediateGoal_4771 _ _ 4771 rfl rfl rfl rfl h4771
  have rSM : denoteGraphDistributed sm initSM 4772 =
      fw_view [4096, 1] (denoteGraphDistributed sm initSM 4771) :=
    distributed_reduce1 sm initSM 67
      { rank := 0, op := "OpName.FW_view", ins := [4771], outs := [4772], params := [4096, 1] }
      4771 4772 (fw_view [4096, 1]) (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_view_out sm s 0 4096 [1] 4771 4772)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rPM : denoteGraphDistributed pm initPM 4772 =
      fw_view [4096, 1] (denoteGraphDistributed pm initPM 4771) :=
    distributed_reduce1 pm initPM 188
      { rank := 1, op := "OpName.FW_view", ins := [4771], outs := [4772], params := [4096, 1] }
      4771 4772 (fw_view [4096, 1]) (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_view_out pm s 1 4096 [1] 4771 4772)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraphDistributed sm initSM 4772 =
      denoteGraphDistributed pm initPM 4772 := by
    rw [rSM, rPM, hv4771]
  have hshape : (denoteGraphDistributed sm initSM 4772).shape = [4096, 1] := by
    rw [rSM]
    rfl
  exact wrap_1tp_gen (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM)
    intermediateGoal_4772 4772 [4096, 1] rfl rfl rfl rfl rfl rfl hval hshape

/-! ### Replicated expert projections feeding SwiGLU -/

/-- The two replicated `[4096,512]` inputs of SwiGLU.  Graph certificates are
kept here so subsequent theorems contain only gather algebra. -/
private theorem l2d_swiglu_sources (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraphDistributed sm initSM 4777 = denoteGraphDistributed pm initPM 4777 ∧
    (denoteGraphDistributed sm initSM 4777).shape = [4096, 512] ∧
    denoteGraphDistributed sm initSM 4781 = denoteGraphDistributed pm initPM 4781 ∧
    (denoteGraphDistributed sm initSM 4781).shape = [4096, 512] := by
  have h4759 := recon_intermediateGoal_4759_distributed initSM initPM hSM hPM hInit
  have hv4759 : denoteGraphDistributed sm initSM 4759 = denoteGraphDistributed pm initPM 4759 :=
    oneTp_valeq intermediateGoal_4759 _ _ 4759 rfl rfl rfl rfl h4759
  have hs4759 : (denoteGraphDistributed sm initSM 4759).shape = [4096, 1024] := h4759.1
  have s7479 : denoteGraphDistributed sm initSM 7479 = denoteGraphDistributed sm initSM 4759 := by
    have h := distributed_reduce1 sm initSM 57
      { rank := 0, op := "OpName.FW_multiref", ins := [4759], outs := [7467, 7471, 7475, 7479, 7483], params := [5] }
      4759 7479 id (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out sm s 0 4759 7467 7471 7475 7479 7483 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    simpa only [id_eq] using h
  have p11906 : denoteGraphDistributed pm initPM 11906 = denoteGraphDistributed pm initPM 4759 := by
    have h := distributed_reduce1 pm initPM 166
      { rank := 1, op := "OpName.FW_multiref", ins := [4759], outs := [11903, 11904, 11905, 11906, 11907], params := [5] }
      4759 11906 id (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos3_out pm s 1 4759 11903 11904 11905 11906 11907 (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    simpa only [id_eq] using h
  have s7483 : denoteGraphDistributed sm initSM 7483 = denoteGraphDistributed sm initSM 4759 := by
    have h := distributed_reduce1 sm initSM 57
      { rank := 0, op := "OpName.FW_multiref", ins := [4759], outs := [7467, 7471, 7475, 7479, 7483], params := [5] }
      4759 7483 id (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out sm s 0 4759 7467 7471 7475 7479 7483 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    simpa only [id_eq] using h
  have p11907 : denoteGraphDistributed pm initPM 11907 = denoteGraphDistributed pm initPM 4759 := by
    have h := distributed_reduce1 pm initPM 166
      { rank := 1, op := "OpName.FW_multiref", ins := [4759], outs := [11903, 11904, 11905, 11906, 11907], params := [5] }
      4759 11907 id (by native_decide) (by native_decide) (by decide)
      (fun s => applyNode_fw_multiref5_at_pos4_out pm s 1 4759 11903 11904 11905 11906 11907 (by decide) (by decide) (by decide) (by decide))
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    simpa only [id_eq] using h
  have rs4774 := l2d_reshape sm initSM 60 0 7479 4774 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rp4774 := l2d_reshape pm initPM 175 1 11906 4774 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rs4778 := l2d_reshape sm initSM 61 0 7483 4778 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rp4778 := l2d_reshape pm initPM 176 1 11907 4778 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hv4774 : denoteGraphDistributed sm initSM 4774 = denoteGraphDistributed pm initPM 4774 := by
    rw [rs4774, rp4774, s7479, p11906, hv4759]
  have hv4778 : denoteGraphDistributed sm initSM 4778 = denoteGraphDistributed pm initPM 4778 := by
    rw [rs4778, rp4778, s7483, p11907, hv4759]
  have hs4774 : (denoteGraphDistributed sm initSM 4774).shape = [4096, 1024] := by rw [rs4774]; rfl
  have hs4778 : (denoteGraphDistributed sm initSM 4778).shape = [4096, 1024] := by rw [rs4778]; rfl
  have hw4775 := distributed_init_singleton_value initSM initPM hInit initGoal_4775 (by native_decide) 4775
    rfl rfl rfl rfl layer1_sm_nodes_nonempty (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hsw4775 := distributed_init_singleton_shape initSM initPM hInit initGoal_4775 (by native_decide) 4775
    [512, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hw4779 := distributed_init_singleton_value initSM initPM hInit initGoal_4779 (by native_decide) 4779
    rfl rfl rfl rfl layer1_sm_nodes_nonempty (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hsw4779 := distributed_init_singleton_shape initSM initPM hInit initGoal_4779 (by native_decide) 4779
    [512, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have rs4776 := l2d_linear sm initSM 64 0 4774 4775 4776 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rp4776 := l2d_linear pm initPM 182 1 4774 4775 4776 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rs4780 := l2d_linear sm initSM 65 0 4778 4779 4780 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rp4780 := l2d_linear pm initPM 184 1 4778 4779 4780 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hv4776 : denoteGraphDistributed sm initSM 4776 = denoteGraphDistributed pm initPM 4776 := by rw [rs4776, rp4776, hv4774, hw4775]
  have hv4780 : denoteGraphDistributed sm initSM 4780 = denoteGraphDistributed pm initPM 4780 := by rw [rs4780, rp4780, hv4778, hw4779]
  have hs4776 : (denoteGraphDistributed sm initSM 4776).shape = [4096, 512] := by
    rw [rs4776]; exact fw_linear_2d_shape 4096 1024 512 _ _ hs4774 hsw4775
  have hs4780 : (denoteGraphDistributed sm initSM 4780).shape = [4096, 512] := by
    rw [rs4780]; exact fw_linear_2d_shape 4096 1024 512 _ _ hs4778 hsw4779
  have rs4777 := l2d_view sm initSM 68 0 4776 4777 4096 [512] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rp4777 := l2d_view pm initPM 190 1 4776 4777 4096 [512] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rs4781 := l2d_view sm initSM 69 0 4780 4781 4096 [512] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rp4781 := l2d_view pm initPM 192 1 4780 4781 4096 [512] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [rs4777, rp4777, hv4776]
  · rw [rs4777]; rfl
  · rw [rs4781, rp4781, hv4780]
  · rw [rs4781]; rfl

/-! ### Dim-0 two-rank gather cascade -/

private theorem l2d_sigmoid_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4773)
      (denoteGraphDistributed pm initPM 7691) (denoteGraphDistributed pm initPM 7692)
      [4096, 1] [2048, 1] := by
  have h4772 := recon_intermediateGoal_4772_distributed initSM initPM hSM hPM hInit
  have hv4772 := oneTp_valeq intermediateGoal_4772 _ _ 4772 rfl rfl rfl rfl h4772
  have hs4772 : (denoteGraphDistributed sm initSM 4772).shape = [4096, 1] := h4772.1
  have hp4772 : (denoteGraphDistributed pm initPM 4772).shape = [4096, 1] := by rw [← hv4772]; exact hs4772
  have c0 := l2d_chunk pm initPM 195 0 4772 7689 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c1 := l2d_chunk pm initPM 196 1 4772 7690 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 7689).shape = [2048, 1] := by
    rw [c0, chunkPrimDimN_shape 0 pm.numRanks 0 _ [4096, 1] hp4772 (by native_decide)]; rfl
  have hs1 : (denoteGraphDistributed pm initPM 7690).shape = [2048, 1] := by
    rw [c1, chunkPrimDimN_shape 0 pm.numRanks 1 _ [4096, 1] hp4772 (by native_decide)]; rfl
  have hrec : denoteGraphDistributed pm initPM 4772 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 7689, denoteGraphDistributed pm initPM 7690] := by
    rw [c0, c1]
    exact (allGather0_reconstruct_chunks_2d 2048 1 (by omega) (by omega) _ hp4772).symm
  have rs := l2d_sigmoid sm initSM 71 0 4772 4773 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_sigmoid pm initPM 203 0 7689 7691 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_sigmoid pm initPM 204 1 7690 7692 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, hv4772, hrec,
      fw_sigmoid_allGather0_commute_2 _ _ 2048 1 (by omega) (by omega) hs0 hs1, r0, r1]
  · rw [rs, fw_sigmoid_shape]; exact hs4772
  · rw [r0, fw_sigmoid_shape]; exact hs0
  · rw [r1, fw_sigmoid_shape]; exact hs1

theorem recon_intermediateGoal_4773_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4773
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  exact Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4773 4773 7691 7692
    [4096, 1] [2048, 1] rfl rfl rfl rfl rfl rfl
    (l2d_sigmoid_rel initSM initPM hSM hPM hInit)

private theorem l2d_swiglu_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4782)
      (denoteGraphDistributed pm initPM 7729) (denoteGraphDistributed pm initPM 7730)
      [4096, 512] [2048, 512] := by
  obtain ⟨hv77, hs77, hv81, hs81⟩ := l2d_swiglu_sources initSM initPM hSM hPM hInit
  have hp77 : (denoteGraphDistributed pm initPM 4777).shape = [4096, 512] := by rw [← hv77]; exact hs77
  have hp81 : (denoteGraphDistributed pm initPM 4781).shape = [4096, 512] := by rw [← hv81]; exact hs81
  have c70 := l2d_chunk pm initPM 197 0 4777 7707 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c71 := l2d_chunk pm initPM 198 1 4777 7708 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c10 := l2d_chunk pm initPM 199 0 4781 7725 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c11 := l2d_chunk pm initPM 200 1 4781 7726 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs70 : (denoteGraphDistributed pm initPM 7707).shape = [2048, 512] := by
    rw [c70, chunkPrimDimN_shape 0 pm.numRanks 0 _ [4096, 512] hp77 (by native_decide)]; rfl
  have hs71 : (denoteGraphDistributed pm initPM 7708).shape = [2048, 512] := by
    rw [c71, chunkPrimDimN_shape 0 pm.numRanks 1 _ [4096, 512] hp77 (by native_decide)]; rfl
  have hs10 : (denoteGraphDistributed pm initPM 7725).shape = [2048, 512] := by
    rw [c10, chunkPrimDimN_shape 0 pm.numRanks 0 _ [4096, 512] hp81 (by native_decide)]; rfl
  have hs11 : (denoteGraphDistributed pm initPM 7726).shape = [2048, 512] := by
    rw [c11, chunkPrimDimN_shape 0 pm.numRanks 1 _ [4096, 512] hp81 (by native_decide)]; rfl
  have rec77 : denoteGraphDistributed pm initPM 4777 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 7707, denoteGraphDistributed pm initPM 7708] := by
    rw [c70, c71]; exact (allGather0_reconstruct_chunks_2d 2048 512 (by omega) (by omega) _ hp77).symm
  have rec81 : denoteGraphDistributed pm initPM 4781 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 7725, denoteGraphDistributed pm initPM 7726] := by
    rw [c10, c11]; exact (allGather0_reconstruct_chunks_2d 2048 512 (by omega) (by omega) _ hp81).symm
  have rs := l2d_swiglu sm initSM 72 0 4777 4781 4782 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_swiglu pm initPM 205 0 7707 7725 7729 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_swiglu pm initPM 206 1 7708 7726 7730 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, hv77, hv81, rec77, rec81,
      fw_swiglu_allGather0_commute_2 _ _ _ _ 2048 512 (by omega) (by omega)
        hs70 hs71 hs10 hs11, r0, r1]
  · rw [rs]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs81
  · rw [r0]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs10
  · rw [r1]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs11

theorem recon_intermediateGoal_4782_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4782
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  exact Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4782 4782 7729 7730
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l2d_swiglu_rel initSM initPM hSM hPM hInit)

private theorem l2d_reshape4783_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4783)
      (denoteGraphDistributed pm initPM 7731) (denoteGraphDistributed pm initPM 7732)
      [4096, 512] [2048, 512] := by
  have h82 := l2d_swiglu_rel initSM initPM hSM hPM hInit
  have rs := l2d_reshape sm initSM 73 0 4782 4783 4096 [512] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_reshape pm initPM 207 0 7729 7731 2048 [512] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_reshape pm initPM 208 1 7730 7732 2048 [512] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h82.value, show ([4096, 512] : Shape) = [2048 * 2, 512] from rfl,
      fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) h82.shard0_shape h82.shard1_shape,
      r0, r1]
  · rw [rs]; rfl
  · rw [r0]; rfl
  · rw [r1]; rfl

theorem recon_intermediateGoal_4783_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4783
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  exact Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4783 4783 7731 7732
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l2d_reshape4783_rel initSM initPM hSM hPM hInit)

private theorem l2d_linear4785_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4785)
      (denoteGraphDistributed pm initPM 7737) (denoteGraphDistributed pm initPM 7738)
      [4096, 1024] [2048, 1024] := by
  have h83 := l2d_reshape4783_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4784 (by native_decide) 4784
    rfl rfl rfl rfl layer1_sm_nodes_nonempty (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hsw := distributed_init_singleton_shape initSM initPM hInit initGoal_4784 (by native_decide) 4784
    [1024, 512] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4784).shape = [1024, 512] := by rw [← hw]; exact hsw
  have rs := l2d_linear sm initSM 74 0 4783 4784 4785 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_linear pm initPM 209 0 7731 4784 7737 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_linear pm initPM 210 1 7732 4784 7738 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h83.value, hw,
      fw_linear_allGather0_commute_2_of _ _ _ 2048 512 1024 (by omega) (by omega) (by omega)
        h83.shard0_shape h83.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 512 1024 _ _ h83.full_shape hsw
  · rw [r0]; exact fw_linear_2d_shape 2048 512 1024 _ _ h83.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 512 1024 _ _ h83.shard1_shape hpw

theorem recon_intermediateGoal_4785_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4785
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  exact Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4785 4785 7737 7738
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_linear4785_rel initSM initPM hSM hPM hInit)

private theorem l2d_view4786_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4786)
      (denoteGraphDistributed pm initPM 7747) (denoteGraphDistributed pm initPM 7748)
      [4096, 1024] [2048, 1024] := by
  have h85 := l2d_linear4785_rel initSM initPM hSM hPM hInit
  have rs := l2d_view sm initSM 75 0 4785 4786 4096 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_view pm initPM 211 0 7737 7747 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_view pm initPM 212 1 7738 7748 2048 [1024] (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h85.value, show ([4096, 1024] : Shape) = [2048 * 2, 1024] from rfl,
      fw_view_allGather0_commute_2_of _ _ 2048 1024 (by omega) h85.shard0_shape h85.shard1_shape,
      r0, r1]
  · rw [rs]; rfl
  · rw [r0]; rfl
  · rw [r1]; rfl

theorem recon_intermediateGoal_4786_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4786
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  exact Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4786 4786 7747 7748
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_view4786_rel initSM initPM hSM hPM hInit)

theorem recon_intermediateGoal_4787_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4787
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have hS := l2d_sigmoid_rel initSM initPM hSM hPM hInit
  have hV := l2d_view4786_rel initSM initPM hSM hPM hInit
  have rs := l2d_mul sm initSM 76 0 4773 4786 4787 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_mul pm initPM 213 0 7691 7747 7751 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_mul pm initPM 214 1 7692 7748 7752 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraphDistributed sm initSM 4787 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 7751, denoteGraphDistributed pm initPM 7752] := by
    rw [rs, hS.value, hV.value,
      fw_mul_allGather0_commute_2_of_broadcast _ _ _ _ 2048 1024
        (by omega) (by omega) (by decide) (by decide) (by decide)
        hS.shard0_shape hS.shard1_shape hV.shard0_shape hV.shard1_shape,
      r0, r1]
  have mulShape : ∀ (x y : Tensor) (a : Nat),
      x.shape = [a, 1] → y.shape = [a, 1024] → (elemwiseMul x y).shape = [a, 1024] := by
    intro x y a hx hy
    show outShape2 x y = [a, 1024]
    unfold outShape2
    rw [hx, hy]
    show (max a a) :: (1024 : Nat) :: [] = [a, 1024]
    rw [Nat.max_self]
  have rel : Gather2Rel (denoteGraphDistributed sm initSM 4787)
      (denoteGraphDistributed pm initPM 7751) (denoteGraphDistributed pm initPM 7752)
      [4096, 1024] [2048, 1024] := by
    refine ⟨hval, ?_, ?_, ?_, by decide⟩
    · rw [rs]; exact mulShape _ _ 4096 hS.full_shape hV.full_shape
    · rw [r0]; exact mulShape _ _ 2048 hS.shard0_shape hV.shard0_shape
    · rw [r1]; exact mulShape _ _ 2048 hS.shard1_shape hV.shard1_shape
  exact Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4787 4787 7751 7752
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl rel

#print axioms recon_intermediateGoal_4787_distributed

/-! ### Residual, norm, and per-head tail (pure distributed evaluator) -/

private theorem l2d_add (g : GraphDecl) (init : Store) (k r x y o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_add", ins := [x, y], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpy : ∀ n ∈ g.nodes.drop k, y ∉ n.outs) :
    denoteGraphDistributed g init o =
      elemwiseAdd (denoteGraphDistributed g init x) (denoteGraphDistributed g init y) :=
  distributed_reduce2 g init k _ x y o elemwiseAdd hk hn (by simp)
    (fun s => applyNode_fw_add2_out g s r x y o) hdn hdw hpn hpx hpy

private theorem l2d_float (g : GraphDecl) (init : Store) (k r i o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_float", ins := [i], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributed g init o = denoteGraphDistributed g init i := by
  have h := distributed_reduce1 g init k _ i o id hk hn (by simp)
    (fun s => applyNode_fw_float_out g s r i o []) hdn hdw hpn hpw
  simpa only [id_eq] using h

private theorem l2d_rms (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_rms_norm", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributed g init o =
      fw_rms_norm (denoteGraphDistributed g init x) (denoteGraphDistributed g init w) :=
  distributed_reduce2 g init k _ x w o fw_rms_norm hk hn (by simp)
    (fun s => applyNode_fw_rms_norm_out_1p g s r x w o) hdn hdw hpn hpx hpw

private theorem l2d_perhead (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_per_head_mix_precision_linear", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributed g init o =
      fw_per_head_linear (denoteGraphDistributed g init x) (denoteGraphDistributed g init w) :=
  distributed_reduce2 g init k _ x w o fw_per_head_linear hk hn (by simp)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out g s r x w o [])
    hdn hdw hpn hpx hpw

private theorem l2d_goal7460_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7460)
      (denoteGraphDistributed pm initPM 12011) (denoteGraphDistributed pm initPM 12012)
      [4096, 1024] [2048, 1024] := by
  have h57 := recon_intermediateGoal_4757_distributed initSM initPM hSM hPM hInit
  have hv57 := oneTp_valeq intermediateGoal_4757 _ _ 4757 rfl rfl rfl rfl h57
  have hs57 : (denoteGraphDistributed sm initSM 4757).shape = [4096, 1024] := h57.1
  have ss := distributed_reduce1 sm initSM 55
    { rank := 0, op := "OpName.FW_multiref", ins := [4757], outs := [7456, 7460], params := [2] }
    4757 7460 id (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_fw_multiref2_second_out' sm s 0 4757 7456 7460 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have sp := distributed_reduce1 pm initPM 160
    { rank := 1, op := "OpName.FW_multiref", ins := [4757], outs := [11889, 11890], params := [2] }
    4757 11890 id (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_fw_multiref2_second_out' pm s 1 4757 11889 11890 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ss sp
  have hp : (denoteGraphDistributed pm initPM 11890).shape = [4096, 1024] := by
    rw [sp, ← hv57]; exact hs57
  have c0 := l2d_chunk pm initPM 162 0 11890 12011 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c1 := l2d_chunk pm initPM 164 1 11890 12012 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 12011).shape = [2048, 1024] := by
    rw [c0, chunkPrimDimN_shape 0 pm.numRanks 0 _ [4096, 1024] hp (by native_decide)]; rfl
  have hs1 : (denoteGraphDistributed pm initPM 12012).shape = [2048, 1024] := by
    rw [c1, chunkPrimDimN_shape 0 pm.numRanks 1 _ [4096, 1024] hp (by native_decide)]; rfl
  refine ⟨?_, ?_, hs0, hs1, by decide⟩
  · rw [ss, hv57, ← sp, c0, c1]
    exact (allGather0_reconstruct_chunks_2d 2048 1024 (by omega) (by omega) _ hp).symm
  · rw [ss]; exact hs57

private theorem l2d_add4788_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4788)
      (denoteGraphDistributed pm initPM 7755) (denoteGraphDistributed pm initPM 7756)
      [4096, 1024] [2048, 1024] := by
  have h68 := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_4768 4768 7677 7678
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4768_distributed initSM initPM hSM hPM hInit)
  have h87 := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_4787 4787 7751 7752
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4787_distributed initSM initPM hSM hPM hInit)
  have rs := l2d_add sm initSM 77 0 4768 4787 4788 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_add pm initPM 215 0 7677 7751 7755 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_add pm initPM 216 1 7678 7752 7756 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h68.value, h87.value,
      fw_add_allGather0_commute_2_2048_1024 _ _ _ _ h68.shard0_shape h68.shard1_shape
        h87.shard0_shape h87.shard1_shape, r0, r1]
  · rw [rs]; exact elemwiseAdd_shape_of_shapes _ _ [4096, 1024] h68.full_shape h87.full_shape
  · rw [r0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h68.shard0_shape h87.shard0_shape
  · rw [r1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h68.shard1_shape h87.shard1_shape

theorem recon_intermediateGoal_4788_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4788
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4788 4788 7755 7756
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_add4788_rel initSM initPM hSM hPM hInit)

private theorem l2d_float4789_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4789)
      (denoteGraphDistributed pm initPM 7761) (denoteGraphDistributed pm initPM 7762)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_add4788_rel initSM initPM hSM hPM hInit
  have rs := l2d_float sm initSM 78 0 4788 4789 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_float pm initPM 217 0 7755 7761 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_float pm initPM 218 1 7756 7762 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  exact ⟨by rw [rs, h.value, r0, r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

theorem recon_intermediateGoal_4789_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4789
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4789 4789 7761 7762
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_float4789_rel initSM initPM hSM hPM hInit)

private theorem l2d_add4790_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4790)
      (denoteGraphDistributed pm initPM 7765) (denoteGraphDistributed pm initPM 7766)
      [4096, 1024] [2048, 1024] := by
  have ha := l2d_goal7460_rel initSM initPM hSM hPM hInit
  have hb := l2d_float4789_rel initSM initPM hSM hPM hInit
  have rs := l2d_add sm initSM 79 0 7460 4789 4790 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_add pm initPM 219 0 12011 7761 7765 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_add pm initPM 220 1 12012 7762 7766 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, ha.value, hb.value,
      fw_add_allGather0_commute_2_2048_1024 _ _ _ _ ha.shard0_shape ha.shard1_shape
        hb.shard0_shape hb.shard1_shape, r0, r1]
  · rw [rs]; exact elemwiseAdd_shape_of_shapes _ _ [4096, 1024] ha.full_shape hb.full_shape
  · rw [r0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] ha.shard0_shape hb.shard0_shape
  · rw [r1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] ha.shard1_shape hb.shard1_shape

theorem recon_intermediateGoal_4790_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4790
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4790 4790 7765 7766
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_add4790_rel initSM initPM hSM hPM hInit)

private theorem l2d_rms4792_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4792)
      (denoteGraphDistributed pm initPM 7769) (denoteGraphDistributed pm initPM 7770)
      [4096, 1024] [2048, 1024] := by
  have h90 := l2d_add4790_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 80
    { rank := 0, op := "OpName.FW_multiref", ins := [4790], outs := [7487, 7491], params := [2] }
    4790 7487 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out sm st 0 4790 7487 7491)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 221
    { rank := 0, op := "OpName.FW_multiref", ins := [7765], outs := [14701, 14705], params := [2] }
    7765 14701 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 0 7765 14701 14705)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 222
    { rank := 1, op := "OpName.FW_multiref", ins := [7766], outs := [14709, 14713], params := [2] }
    7766 14709 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 1 7766 14709 14713)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4791 (by native_decide) 4791
    rfl rfl rfl rfl layer1_sm_nodes_nonempty (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have rs := l2d_rms sm initSM 81 0 7487 4791 4792 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_rms pm initPM 223 0 14701 4791 7769 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_rms pm initPM 224 1 14709 4791 7770 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 14701).shape = [2048, 1024] := by rw [p0]; exact h90.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 14709).shape = [2048, 1024] := by rw [p1]; exact h90.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h90.value, ← p0, ← p1, hw,
      fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs0 hs1, r0, r1]
  · rw [rs]; exact fw_rms_norm_shape2 _ _ 4096 1024 (by rw [s]; exact h90.full_shape)
  · rw [r0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs0
  · rw [r1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs1

theorem recon_intermediateGoal_4792_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4792
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4792 4792 7769 7770
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_rms4792_rel initSM initPM hSM hPM hInit)

private theorem l2d_perhead_gather (x x0 x1 w out out0 out1 : Tensor)
    (heads : Nat) (hx : Gather2Rel x x0 x1 [4096, 1024] [2048, 1024])
    (hw : w.shape = [heads, 64, 1024])
    (hn : out = fw_per_head_linear x w)
    (hn0 : out0 = fw_per_head_linear x0 w)
    (hn1 : out1 = fw_per_head_linear x1 w)
    (hh : 0 < heads) :
    Gather2Rel out out0 out1 [4096, heads, 64] [2048, heads, 64] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hn, hn0, hn1, hx.value,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 heads 64
        (by omega) (by omega) hh (by omega) hx.shard0_shape hx.shard1_shape hw]
  · rw [hn]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 heads 64 hx.full_shape hw
  · rw [hn0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 heads 64 hx.shard0_shape hw
  · rw [hn1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 heads 64 hx.shard1_shape hw
  · intro heq
    have := congrArg List.length heq
    norm_num at this

private theorem l2d_q4794_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4794)
      (denoteGraphDistributed pm initPM 7771) (denoteGraphDistributed pm initPM 7772)
      [4096, 16, 64] [2048, 16, 64] := by
  have h92 := l2d_rms4792_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 82
    { rank := 0, op := "OpName.FW_multiref", ins := [4792], outs := [7496, 7500, 7504], params := [3] }
    4792 7496 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' sm st 0 4792 7496 7500 7504)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 225
    { rank := 0, op := "OpName.FW_multiref", ins := [7769], outs := [14718, 14722, 14726], params := [3] }
    7769 14718 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' pm st 0 7769 14718 14722 14726)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 226
    { rank := 1, op := "OpName.FW_multiref", ins := [7770], outs := [14731, 14735, 14739], params := [3] }
    7770 14731 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' pm st 1 7770 14731 14735 14739)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have src : Gather2Rel (denoteGraphDistributed sm initSM 7496)
      (denoteGraphDistributed pm initPM 14718) (denoteGraphDistributed pm initPM 14731)
      [4096, 1024] [2048, 1024] := by
    refine ⟨by rw [s, h92.value, p0, p1], by rw [s]; exact h92.full_shape,
      by rw [p0]; exact h92.shard0_shape, by rw [p1]; exact h92.shard1_shape, by decide⟩
  have hwv := distributed_init_singleton_value initSM initPM hInit initGoal_4793 (by native_decide) 4793
    rfl rfl rfl rfl layer1_sm_nodes_nonempty (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4793 (by native_decide) 4793
    [16, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4793).shape = [16, 64, 1024] := by rw [← hwv]; exact hws
  have rs := l2d_perhead sm initSM 83 0 7496 4793 4794 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_perhead pm initPM 227 0 14718 4793 7771 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_perhead pm initPM 230 1 14731 4793 7772 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  apply l2d_perhead_gather _ _ _ (denoteGraphDistributed pm initPM 4793) _ _ _ 16 src hpw
  · rw [rs, hwv]
  · exact r0
  · exact r1
  · omega

theorem recon_intermediateGoal_4794_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4794
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4794 4794 7771 7772
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl
    (l2d_q4794_rel initSM initPM hSM hPM hInit)

private theorem l2d_k4796_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4796)
      (denoteGraphDistributed pm initPM 7783) (denoteGraphDistributed pm initPM 7784)
      [4096, 4, 64] [2048, 4, 64] := by
  have h92 := l2d_rms4792_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 82
    { rank := 0, op := "OpName.FW_multiref", ins := [4792], outs := [7496, 7500, 7504], params := [3] }
    4792 7500 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' sm st 0 4792 7496 7500 7504 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 225
    { rank := 0, op := "OpName.FW_multiref", ins := [7769], outs := [14718, 14722, 14726], params := [3] }
    7769 14722 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' pm st 0 7769 14718 14722 14726 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 226
    { rank := 1, op := "OpName.FW_multiref", ins := [7770], outs := [14731, 14735, 14739], params := [3] }
    7770 14735 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' pm st 1 7770 14731 14735 14739 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have src : Gather2Rel (denoteGraphDistributed sm initSM 7500)
      (denoteGraphDistributed pm initPM 14722) (denoteGraphDistributed pm initPM 14735)
      [4096, 1024] [2048, 1024] := by
    refine ⟨by rw [s, h92.value, p0, p1], by rw [s]; exact h92.full_shape,
      by rw [p0]; exact h92.shard0_shape, by rw [p1]; exact h92.shard1_shape, by decide⟩
  have hwv := distributed_init_singleton_value initSM initPM hInit initGoal_4795 (by native_decide) 4795
    rfl rfl rfl rfl layer1_sm_nodes_nonempty (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4795 (by native_decide) 4795
    [4, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4795).shape = [4, 64, 1024] := by rw [← hwv]; exact hws
  have rs := l2d_perhead sm initSM 84 0 7500 4795 4796 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_perhead pm initPM 228 0 14722 4795 7783 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_perhead pm initPM 231 1 14735 4795 7784 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  apply l2d_perhead_gather _ _ _ (denoteGraphDistributed pm initPM 4795) _ _ _ 4 src hpw
  · rw [rs, hwv]
  · exact r0
  · exact r1
  · omega

theorem recon_intermediateGoal_4796_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4796
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4796 4796 7783 7784
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l2d_k4796_rel initSM initPM hSM hPM hInit)

private theorem l2d_v4798_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4798)
      (denoteGraphDistributed pm initPM 7793) (denoteGraphDistributed pm initPM 7794)
      [4096, 4, 64] [2048, 4, 64] := by
  have h92 := l2d_rms4792_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 82
    { rank := 0, op := "OpName.FW_multiref", ins := [4792], outs := [7496, 7500, 7504], params := [3] }
    4792 7504 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' sm st 0 4792 7496 7500 7504 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 225
    { rank := 0, op := "OpName.FW_multiref", ins := [7769], outs := [14718, 14722, 14726], params := [3] }
    7769 14726 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' pm st 0 7769 14718 14722 14726 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 226
    { rank := 1, op := "OpName.FW_multiref", ins := [7770], outs := [14731, 14735, 14739], params := [3] }
    7770 14739 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' pm st 1 7770 14731 14735 14739 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have src : Gather2Rel (denoteGraphDistributed sm initSM 7504)
      (denoteGraphDistributed pm initPM 14726) (denoteGraphDistributed pm initPM 14739)
      [4096, 1024] [2048, 1024] := by
    refine ⟨by rw [s, h92.value, p0, p1], by rw [s]; exact h92.full_shape,
      by rw [p0]; exact h92.shard0_shape, by rw [p1]; exact h92.shard1_shape, by decide⟩
  have hwv := distributed_init_singleton_value initSM initPM hInit initGoal_4797 (by native_decide) 4797
    rfl rfl rfl rfl layer1_sm_nodes_nonempty (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4797 (by native_decide) 4797
    [4, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4797).shape = [4, 64, 1024] := by rw [← hwv]; exact hws
  have rs := l2d_perhead sm initSM 85 0 7504 4797 4798 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_perhead pm initPM 229 0 14726 4797 7793 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_perhead pm initPM 232 1 14739 4797 7794 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  apply l2d_perhead_gather _ _ _ (denoteGraphDistributed pm initPM 4797) _ _ _ 4 src hpw
  · rw [rs, hwv]
  · exact r0
  · exact r1
  · omega

theorem recon_intermediateGoal_4798_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4798
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4798 4798 7793 7794
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l2d_v4798_rel initSM initPM hSM hPM hInit)

#print axioms recon_intermediateGoal_4798_distributed

private theorem l2d_rotary_cache (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraphDistributed sm initSM 4691 = denoteGraphDistributed pm initPM 11855 := by
  have hbase := distributed_init_singleton_value initSM initPM hInit initGoal_4691
    (by native_decide) 4691 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hcopy : denoteGraphDistributed pm initPM 11855 = id (denoteGraphDistributed pm initPM 4691) :=
    distributed_reduce1 pm initPM 14
      { rank := 1, op := "OpName.FW_multiref", ins := [4691],
        outs := (List.range 12).map (fun r => 11853 + r),
        params := [((List.range 12).map (fun r => 11853 + r)).length] }
      4691 11855 id (by native_decide) (by native_decide) (by decide)
      (fun s => by
        rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm s _ (by decide) (by decide)]
        rw [applyNode_fw_multiref_mem_out pm s 1 4691
          ((List.range 12).map (fun r => 11853 + r)) 11855 (by native_decide), id_eq])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  rw [hcopy, id_eq]
  exact hbase

set_option maxHeartbeats 8000000 in
private theorem l2d_rotary_rels (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4800)
      (denoteGraphDistributed pm initPM 7805) (denoteGraphDistributed pm initPM 7806)
      [4096, 16, 64] [2048, 16, 64] ∧
    Gather2Rel (denoteGraphDistributed sm initSM 4801)
      (denoteGraphDistributed pm initPM 7807) (denoteGraphDistributed pm initPM 7808)
      [4096, 4, 64] [2048, 4, 64] := by
  have hq := l2d_q4794_rel initSM initPM hSM hPM hInit
  have hk := l2d_k4796_rel initSM initPM hSM hPM hInit
  have hcache := l2d_rotary_cache initSM initPM hInit
  have hpos := distributed_init_singleton_value initSM initPM hInit initGoal_4799 (by native_decide) 4799
    rfl rfl rfl rfl layer1_sm_nodes_nonempty (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hspos := distributed_init_singleton_shape initSM initPM hInit initGoal_4799 (by native_decide) 4799
    [4096] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have c0 := l2d_chunk pm initPM 2 0 4799 7803 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c1 := l2d_chunk pm initPM 15 1 4799 7804 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c0' : denoteGraphDistributed pm initPM 7803 =
      chunkPrimDimN 0 2 0 (denoteGraphDistributed pm initPM 4799) := c0
  have c1' : denoteGraphDistributed pm initPM 7804 =
      chunkPrimDimN 0 2 1 (denoteGraphDistributed pm initPM 4799) := c1
  have qSM : denoteGraphDistributed sm initSM 4800 =
      (fw_rotary_embedding (denoteGraphDistributed sm initSM 4691)
        (denoteGraphDistributed sm initSM 4799) (denoteGraphDistributed sm initSM 4794)
        (denoteGraphDistributed sm initSM 4796) 16 4).1 := by
    rw [distributed_node_core sm initSM 86
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4799, 4794, 4796],
        outs := [4800, 4801], params := [16, 4] } 4800
      (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring sm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read sm initSM 86 4691 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 86 4799 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 86 4794 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 86 4796 (by native_decide) (by native_decide)]
  have kSM : denoteGraphDistributed sm initSM 4801 =
      (fw_rotary_embedding (denoteGraphDistributed sm initSM 4691)
        (denoteGraphDistributed sm initSM 4799) (denoteGraphDistributed sm initSM 4794)
        (denoteGraphDistributed sm initSM 4796) 16 4).2 := by
    rw [distributed_node_core sm initSM 86
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4799, 4794, 4796],
        outs := [4800, 4801], params := [16, 4] } 4801
      (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring sm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 4691 4799 4794 4796 4800 4801 (by decide),
      distributed_prefix_read sm initSM 86 4691 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 86 4799 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 86 4794 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 86 4796 (by native_decide) (by native_decide)]
  have q0 : denoteGraphDistributed pm initPM 7805 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11855)
        (denoteGraphDistributed pm initPM 7803) (denoteGraphDistributed pm initPM 7771)
        (denoteGraphDistributed pm initPM 7783) 16 4).1 := by
    rw [distributed_node_core pm initPM 233
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11855, 7803, 7771, 7783],
        outs := [7805, 7807], params := [16, 4] } 7805
      (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read pm initPM 233 11855 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 233 7803 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 233 7771 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 233 7783 (by native_decide) (by native_decide)]
  have k0 : denoteGraphDistributed pm initPM 7807 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11855)
        (denoteGraphDistributed pm initPM 7803) (denoteGraphDistributed pm initPM 7771)
        (denoteGraphDistributed pm initPM 7783) 16 4).2 := by
    rw [distributed_node_core pm initPM 233
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11855, 7803, 7771, 7783],
        outs := [7805, 7807], params := [16, 4] } 7807
      (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11855 7803 7771 7783 7805 7807 (by decide),
      distributed_prefix_read pm initPM 233 11855 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 233 7803 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 233 7771 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 233 7783 (by native_decide) (by native_decide)]
  have q1 : denoteGraphDistributed pm initPM 7806 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11855)
        (denoteGraphDistributed pm initPM 7804) (denoteGraphDistributed pm initPM 7772)
        (denoteGraphDistributed pm initPM 7784) 16 4).1 := by
    rw [distributed_node_core pm initPM 234
      { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11855, 7804, 7772, 7784],
        outs := [7806, 7808], params := [16, 4] } 7806
      (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read pm initPM 234 11855 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 234 7804 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 234 7772 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 234 7784 (by native_decide) (by native_decide)]
  have k1 : denoteGraphDistributed pm initPM 7808 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11855)
        (denoteGraphDistributed pm initPM 7804) (denoteGraphDistributed pm initPM 7772)
        (denoteGraphDistributed pm initPM 7784) 16 4).2 := by
    rw [distributed_node_core pm initPM 234
      { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11855, 7804, 7772, 7784],
        outs := [7806, 7808], params := [16, 4] } 7808
      (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11855 7804 7772 7784 7806 7808 (by decide),
      distributed_prefix_read pm initPM 234 11855 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 234 7804 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 234 7772 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 234 7784 (by native_decide) (by native_decide)]
  have qval : denoteGraphDistributed sm initSM 4800 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 7805, denoteGraphDistributed pm initPM 7806] := by
    rw [qSM]
    simp only [fw_rotary_embedding]
    rw [hq.value,
      fw_rotary_apply_allGather0_commute_2_1d (denoteGraphDistributed sm initSM 4691)
        (denoteGraphDistributed sm initSM 4799) (denoteGraphDistributed pm initPM 7771)
        (denoteGraphDistributed pm initPM 7772) 2048 16 64 (by omega) (by omega) (by omega)
        hspos hq.shard0_shape hq.shard1_shape,
      hcache, hpos, ← c0', ← c1', q0, q1]
    simp only [fw_rotary_embedding]
  have kval : denoteGraphDistributed sm initSM 4801 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 7807, denoteGraphDistributed pm initPM 7808] := by
    rw [kSM]
    simp only [fw_rotary_embedding]
    rw [hk.value,
      fw_rotary_apply_allGather0_commute_2_1d (denoteGraphDistributed sm initSM 4691)
        (denoteGraphDistributed sm initSM 4799) (denoteGraphDistributed pm initPM 7783)
        (denoteGraphDistributed pm initPM 7784) 2048 4 64 (by omega) (by omega) (by omega)
        hspos hk.shard0_shape hk.shard1_shape,
      hcache, hpos, ← c0', ← c1', k0, k1]
    simp only [fw_rotary_embedding]
  have qs0 : (denoteGraphDistributed pm initPM 7805).shape = [2048, 16, 64] := by
    rw [q0]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hq.shard0_shape
  have qs1 : (denoteGraphDistributed pm initPM 7806).shape = [2048, 16, 64] := by
    rw [q1]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hq.shard1_shape
  have ks0 : (denoteGraphDistributed pm initPM 7807).shape = [2048, 4, 64] := by
    rw [k0]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hk.shard0_shape
  have ks1 : (denoteGraphDistributed pm initPM 7808).shape = [2048, 4, 64] := by
    rw [k1]; simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hk.shard1_shape
  refine ⟨⟨qval, ?_, qs0, qs1, by decide⟩, ⟨kval, ?_, ks0, ks1, by decide⟩⟩
  · rw [qval, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [qs0])]
    rfl
  · rw [kval, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [ks0])]
    rfl

theorem recon_intermediateGoal_4800_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4800
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4800 4800 7805 7806
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl
    (l2d_rotary_rels initSM initPM hSM hPM hInit).1

theorem recon_intermediateGoal_4801_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4801
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4801 4801 7807 7808
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l2d_rotary_rels initSM initPM hSM hPM hInit).2

#print axioms recon_intermediateGoal_4800_distributed
#print axioms recon_intermediateGoal_4801_distributed

private def layer2SmSliding : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [4800, 4801, 4798, 4802, 4803], outs := [4804],
    params := [16, 4, 64, 64, 1, 512] }
private def layer2PmSliding0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [7805, 7807, 7793, 4802, 4803], outs := [7809],
    params := [16, 4, 64, 64, 1, 512] }
private def layer2PmSliding1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window",
    ins := [7806, 7808, 7794, 4802, 4803], outs := [7810],
    params := [16, 4, 64, 64, 1, 512] }

-- Keep graph and replica-order certificates split from the tensor proof.
set_option maxRecDepth 1000000 in
private theorem layer2_sm_node87 : sm.nodes[87]'(by native_decide) = layer2SmSliding := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer2_pm_node235 : pm.nodes[235]'(by native_decide) = layer2PmSliding0 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer2_pm_node236 : pm.nodes[236]'(by native_decide) = layer2PmSliding1 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer2_sm_buddy_sliding :
    ringAttnBuddies sm layer2SmSliding = [layer2SmSliding] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer2_pm_buddy_sliding0 :
    ringAttnBuddies pm layer2PmSliding0 = [layer2PmSliding0, layer2PmSliding1] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer2_pm_buddy_sliding1 :
    ringAttnBuddies pm layer2PmSliding1 = [layer2PmSliding0, layer2PmSliding1] := by native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
theorem recon_intermediateGoal_4804_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4804
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  -- Consume precisely the already-proved distributed Q/K/V boundaries.
  have gq := recon_intermediateGoal_4800_distributed initSM initPM hSM hPM hInit
  have gk := recon_intermediateGoal_4801_distributed initSM initPM hSM hPM hInit
  have gv := recon_intermediateGoal_4798_distributed initSM initPM hSM hPM hInit
  have gqshape : (denoteGraphDistributed sm initSM 4800).shape = [4096, 16, 64] := by
    simpa only [intermediateGoal_4800] using gq.1
  have gkshape : (denoteGraphDistributed sm initSM 4801).shape = [4096, 4, 64] := by
    simpa only [intermediateGoal_4801] using gk.1
  have gvshape : (denoteGraphDistributed sm initSM 4798).shape = [4096, 4, 64] := by
    simpa only [intermediateGoal_4798] using gv.1
  have q := (l2d_rotary_rels initSM initPM hSM hPM hInit).1
  have k := (l2d_rotary_rels initSM initPM hSM hPM hInit).2
  have v := l2d_v4798_rel initSM initPM hSM hPM hInit
  have hcu4802 := distributed_init_singleton_value initSM initPM hInit initGoal_4802
    (by native_decide) 4802 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hcu4803 := distributed_init_singleton_value initSM initPM hInit initGoal_4803
    (by native_decide) 4803 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  let fs := (sm.nodes.take 87).foldl (applyNodeDistributed sm) initSM
  let fp := (pm.nodes.take 235).foldl (applyNodeDistributed pm) initPM
  let fp' := (pm.nodes.take 236).foldl (applyNodeDistributed pm) initPM
  have bs (t : Tid) (hn : ∀ n ∈ sm.nodes.drop 87, n.outs ≠ [])
      (hw : ∀ n ∈ sm.nodes.drop 87, t ∉ n.outs) : fs t = denoteGraphDistributed sm initSM t :=
    distributed_prefix_read sm initSM 87 t hn hw
  have bp (t : Tid) (hn : ∀ n ∈ pm.nodes.drop 235, n.outs ≠ [])
      (hw : ∀ n ∈ pm.nodes.drop 235, t ∉ n.outs) : fp t = denoteGraphDistributed pm initPM t :=
    distributed_prefix_read pm initPM 235 t hn hw
  have hqfull : fs 4800 = allGatherPrimDimN 0 2 0 [fp 7805, fp 7806] := by
    rw [bs 4800 (by native_decide) (by native_decide),
      bp 7805 (by native_decide) (by native_decide),
      bp 7806 (by native_decide) (by native_decide)]
    exact q.value
  have hkfull : fs 4801 = allGatherPrimDimN 0 2 0 [fp 7807, fp 7808] := by
    rw [bs 4801 (by native_decide) (by native_decide),
      bp 7807 (by native_decide) (by native_decide),
      bp 7808 (by native_decide) (by native_decide)]
    exact k.value
  have hvfull : fs 4798 = allGatherPrimDimN 0 2 0 [fp 7793, fp 7794] := by
    rw [bs 4798 (by native_decide) (by native_decide),
      bp 7793 (by native_decide) (by native_decide),
      bp 7794 (by native_decide) (by native_decide)]
    exact v.value
  have hqpos : 0 < (fs (layer2SmSliding.ins.getD 0 0)).shape.length := by
    show 0 < (fs 4800).shape.length
    rw [bs 4800 (by native_decide) (by native_decide), gqshape]
    decide
  have hkpos : 0 < (fs (layer2SmSliding.ins.getD 1 0)).shape.length := by
    show 0 < (fs 4801).shape.length
    rw [bs 4801 (by native_decide) (by native_decide), gkshape]
    decide
  have hvpos : 0 < (fs (layer2SmSliding.ins.getD 2 0)).shape.length := by
    show 0 < (fs 4798).shape.length
    rw [bs 4798 (by native_decide) (by native_decide), gvshape]
    decide
  have hcuQ : fs 4802 = fp 4802 := by
    rw [bs 4802 (by native_decide) (by native_decide),
      bp 4802 (by native_decide) (by native_decide), hcu4802]
  have hcuK : fs 4803 = fp 4803 := by
    rw [bs 4803 (by native_decide) (by native_decide),
      bp 4803 (by native_decide) (by native_decide), hcu4803]
  have e7805 : fp 7805 = fp' 7805 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 7805 235 236
      (by omega) (by native_decide) (by native_decide)).symm
  have e7806 : fp 7806 = fp' 7806 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 7806 235 236
      (by omega) (by native_decide) (by native_decide)).symm
  have e7807 : fp 7807 = fp' 7807 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 7807 235 236
      (by omega) (by native_decide) (by native_decide)).symm
  have e7808 : fp 7808 = fp' 7808 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 7808 235 236
      (by omega) (by native_decide) (by native_decide)).symm
  have e7793 : fp 7793 = fp' 7793 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 7793 235 236
      (by omega) (by native_decide) (by native_decide)).symm
  have e7794 : fp 7794 = fp' 7794 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 7794 235 236
      (by omega) (by native_decide) (by native_decide)).symm
  have e4802 : fp 4802 = fp' 4802 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 4802 235 236
      (by omega) (by native_decide) (by native_decide)).symm
  have e4803 : fp 4803 = fp' 4803 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 4803 235 236
      (by omega) (by native_decide) (by native_decide)).symm
  have bridge : applyNodeRingAttn_sliding_window pm fp layer2PmSliding1 =
      applyNodeRingAttn_sliding_window pm fp' layer2PmSliding1 := by
    apply attn_sw_store_congr
    · rw [layer2_pm_buddy_sliding1]; intro m hm; fin_cases hm
      · exact e7805
      · exact e7806
    · rw [layer2_pm_buddy_sliding1]; intro m hm; fin_cases hm
      · exact e7807
      · exact e7808
    · rw [layer2_pm_buddy_sliding1]; intro m hm; fin_cases hm
      · exact e7793
      · exact e7794
    · exact e4802
    · exact e4803
  have rSM : denoteGraphDistributed sm initSM 4804 =
      applyNodeRingAttn_sliding_window sm fs layer2SmSliding := by
    rw [distributed_node_core sm initSM 87 layer2SmSliding 4804 (by native_decide)
      layer2_sm_node87 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out sm _ 0 4800 4801 4798 4802 4803 4804
      [16, 4, 64, 64, 1, 512]
  have rP0 : denoteGraphDistributed pm initPM 7809 =
      applyNodeRingAttn_sliding_window pm fp layer2PmSliding0 := by
    rw [distributed_node_core pm initPM 235 layer2PmSliding0 7809 (by native_decide)
      layer2_pm_node235 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out pm _ 0 7805 7807 7793 4802 4803 7809
      [16, 4, 64, 64, 1, 512]
  have rP1 : denoteGraphDistributed pm initPM 7810 =
      applyNodeRingAttn_sliding_window pm fp' layer2PmSliding1 := by
    rw [distributed_node_core pm initPM 236 layer2PmSliding1 7810 (by native_decide)
      layer2_pm_node236 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out pm _ 1 7806 7808 7794 4802 4803 7810
      [16, 4, 64, 64, 1, 512]
  have hfull : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 7805, fp 7806])
      (allGatherPrimDimN 0 2 0 [fp 7807, fp 7808])
      (allGatherPrimDimN 0 2 0 [fp 7793, fp 7794])
      (fp 4802) (fp 4803) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3, ← hqfull,
      bs 4800 (by native_decide) (by native_decide), gqshape]
    rfl
  have hfull' : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 7805, fp' 7806])
      (allGatherPrimDimN 0 2 0 [fp' 7807, fp' 7808])
      (allGatherPrimDimN 0 2 0 [fp' 7793, fp' 7794])
      (fp' 4802) (fp' 4803) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [← e7805, ← e7806, ← e7807, ← e7808, ← e7793, ← e7794,
      ← e4802, ← e4803]
    exact hfull
  exact recon_attn_sliding_window_2tp_distributed initSM initPM intermediateGoal_4804
    layer2SmSliding layer2PmSliding0 layer2PmSliding1 fs fp fp' 4804 7809 7810
    2048 16 64 (by omega) (by omega) (by omega) rSM rP0 rP1 bridge
    layer2_sm_buddy_sliding layer2_pm_buddy_sliding0 layer2_pm_buddy_sliding1
    (by native_decide) (by native_decide) hqpos hkpos hvpos hqfull hkfull hvfull
    hcuQ hcuK rfl rfl rfl rfl hfull hfull' rfl rfl rfl rfl rfl rfl

#print axioms recon_intermediateGoal_4804_distributed

/-! ### Post-attention residual tail (pure distributed evaluator) -/

private theorem l2d_reshape4805_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4805)
      (denoteGraphDistributed pm initPM 7811) (denoteGraphDistributed pm initPM 7812)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_4804 4804 7809 7810
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4804_distributed initSM initPM hSM hPM hInit)
  have rs := l2d_reshape sm initSM 88 0 4804 4805 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l2d_reshape pm initPM 237 0 7809 7811 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l2d_reshape pm initPM 238 1 7810 7812 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine ⟨?_, by rw [rs]; rfl, by rw [r0]; rfl, by rw [r1]; rfl, by decide⟩
  rw [rs, h.value, r0, r1]
  exact fw_view_allGather0_reshape_16_64_2_g12 _ _ h.shard0_shape h.shard1_shape

theorem recon_intermediateGoal_4805_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4805
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4805 4805 7811 7812
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_reshape4805_rel initSM initPM hSM hPM hInit)

private theorem l2d_reshape4806_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4806)
      (denoteGraphDistributed pm initPM 7817) (denoteGraphDistributed pm initPM 7818)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_reshape4805_rel initSM initPM hSM hPM hInit
  have rs := l2d_reshape sm initSM 89 0 4805 4806 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l2d_reshape pm initPM 239 0 7811 7817 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l2d_reshape pm initPM 240 1 7812 7818 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 4806 = denoteGraphDistributed sm initSM 4805 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 7817 = denoteGraphDistributed pm initPM 7811 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 7818 = denoteGraphDistributed pm initPM 7812 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, e0, e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

theorem recon_intermediateGoal_4806_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4806
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4806 4806 7817 7818
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_reshape4806_rel initSM initPM hSM hPM hInit)

private theorem l2d_linear4808_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4808)
      (denoteGraphDistributed pm initPM 7821) (denoteGraphDistributed pm initPM 7822)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_reshape4806_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4807
    (by native_decide) 4807 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4807
    (by native_decide) 4807 [1024, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4807).shape = [1024, 1024] := by
    rw [← hw]; exact hws
  have rs := l2d_linear sm initSM 90 0 4806 4807 4808 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_linear pm initPM 241 0 7817 4807 7821 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_linear pm initPM 242 1 7818 4807 7822 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw,
      fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
        (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 1024 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 1024 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 1024 _ _ h.shard1_shape hpw

theorem recon_intermediateGoal_4808_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4808
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4808 4808 7821 7822
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_linear4808_rel initSM initPM hSM hPM hInit)

private theorem l2d_view4809_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4809)
      (denoteGraphDistributed pm initPM 7831) (denoteGraphDistributed pm initPM 7832)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_linear4808_rel initSM initPM hSM hPM hInit
  have rs := l2d_view sm initSM 91 0 4808 4809 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l2d_view pm initPM 243 0 7821 7831 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l2d_view pm initPM 244 1 7822 7832 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 4809 = denoteGraphDistributed sm initSM 4808 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 7831 = denoteGraphDistributed pm initPM 7821 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 7832 = denoteGraphDistributed pm initPM 7822 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, e0, e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

theorem recon_intermediateGoal_4809_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4809
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4809 4809 7831 7832
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_view4809_rel initSM initPM hSM hPM hInit)

private theorem l2d_float4810_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4810)
      (denoteGraphDistributed pm initPM 7835) (denoteGraphDistributed pm initPM 7836)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_view4809_rel initSM initPM hSM hPM hInit
  have rs := l2d_float sm initSM 92 0 4809 4810 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_float pm initPM 245 0 7831 7835 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_float pm initPM 246 1 7832 7836 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  exact ⟨by rw [rs, h.value, r0, r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

theorem recon_intermediateGoal_4810_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4810
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4810 4810 7835 7836
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_float4810_rel initSM initPM hSM hPM hInit)

private theorem l2d_carry7491_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7491)
      (denoteGraphDistributed pm initPM 14705) (denoteGraphDistributed pm initPM 14713)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_add4790_rel initSM initPM hSM hPM hInit
  have rs := distributed_reduce1 sm initSM 80
    { rank := 0, op := "OpName.FW_multiref", ins := [4790], outs := [7487, 7491], params := [2] }
    4790 7491 id (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_fw_multiref2_second_out' sm s 0 4790 7487 7491 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce1 pm initPM 221
    { rank := 0, op := "OpName.FW_multiref", ins := [7765], outs := [14701, 14705], params := [2] }
    7765 14705 id (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_fw_multiref2_second_out' pm s 0 7765 14701 14705 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce1 pm initPM 222
    { rank := 1, op := "OpName.FW_multiref", ins := [7766], outs := [14709, 14713], params := [2] }
    7766 14713 id (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_fw_multiref2_second_out' pm s 1 7766 14709 14713 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rs r0 r1
  exact ⟨by rw [rs, h.value, r0, r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

theorem recon_intermediateGoal_7491_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7491
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_7491 7491 14705 14713
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_carry7491_rel initSM initPM hSM hPM hInit)

private theorem l2d_add4811_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4811)
      (denoteGraphDistributed pm initPM 7839) (denoteGraphDistributed pm initPM 7840)
      [4096, 1024] [2048, 1024] := by
  have ha := l2d_carry7491_rel initSM initPM hSM hPM hInit
  have hb := l2d_float4810_rel initSM initPM hSM hPM hInit
  have rs := l2d_add sm initSM 93 0 7491 4810 4811 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_add pm initPM 247 0 14705 7835 7839 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_add pm initPM 248 1 14713 7836 7840 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, ha.value, hb.value,
      fw_add_allGather0_commute_2_2048_1024 _ _ _ _ ha.shard0_shape ha.shard1_shape
        hb.shard0_shape hb.shard1_shape, r0, r1]
  · rw [rs]; exact elemwiseAdd_shape_of_shapes _ _ [4096, 1024] ha.full_shape hb.full_shape
  · rw [r0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] ha.shard0_shape hb.shard0_shape
  · rw [r1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] ha.shard1_shape hb.shard1_shape

theorem recon_intermediateGoal_4811_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4811
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4811 4811 7839 7840
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_add4811_rel initSM initPM hSM hPM hInit)

/-! ### Layer-3 router entrance (pure distributed evaluator) -/

private theorem l2d_rms4813_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4813)
      (denoteGraphDistributed pm initPM 7843) (denoteGraphDistributed pm initPM 7844)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_add4811_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 94
    { rank := 0, op := "OpName.FW_multiref", ins := [4811], outs := [7508, 7512], params := [2] }
    4811 7508 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out sm st 0 4811 7508 7512)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 249
    { rank := 0, op := "OpName.FW_multiref", ins := [7839], outs := [14743, 14747], params := [2] }
    7839 14743 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 0 7839 14743 14747)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 250
    { rank := 1, op := "OpName.FW_multiref", ins := [7840], outs := [14751, 14755], params := [2] }
    7840 14751 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 1 7840 14751 14755)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4812
    (by native_decide) 4812 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have rs := l2d_rms sm initSM 95 0 7508 4812 4813 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_rms pm initPM 251 0 14743 4812 7843 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_rms pm initPM 252 1 14751 4812 7844 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 14743).shape = [2048, 1024] := by
    rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 14751).shape = [2048, 1024] := by
    rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs0 hs1,
      r0, r1]
  · rw [rs]; exact fw_rms_norm_shape2 _ _ 4096 1024 (by rw [s]; exact h.full_shape)
  · rw [r0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs0
  · rw [r1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs1

theorem recon_intermediateGoal_4813_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4813
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4813 4813 7843 7844
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_rms4813_rel initSM initPM hSM hPM hInit)

private theorem l2d_float4814_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4814)
      (denoteGraphDistributed pm initPM 7845) (denoteGraphDistributed pm initPM 7846)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_rms4813_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 96
    { rank := 0, op := "OpName.FW_multiref", ins := [4813],
      outs := [7519, 7523, 7527, 7531, 7535], params := [5] }
    4813 7519 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref_first_out' sm st 0 4 4813 7519 [7523, 7527, 7531, 7535])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 253
    { rank := 0, op := "OpName.FW_multiref", ins := [7843],
      outs := [14762, 14766, 14770, 14774, 14778], params := [5] }
    7843 14762 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref_first_out' pm st 0 4 7843 14762 [14766, 14770, 14774, 14778])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 254
    { rank := 1, op := "OpName.FW_multiref", ins := [7844],
      outs := [14785, 14789, 14793, 14797, 14801], params := [5] }
    7844 14785 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref_first_out' pm st 1 4 7844 14785 [14789, 14793, 14797, 14801])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have rs := l2d_float sm initSM 97 0 7519 4814 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_float pm initPM 255 0 14762 7845 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_float pm initPM 259 1 14785 7846 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  exact ⟨by rw [rs, s, h.value, ← p0, ← p1, r0, r1],
    by rw [rs, s]; exact h.full_shape, by rw [r0, p0]; exact h.shard0_shape,
    by rw [r1, p1]; exact h.shard1_shape, by decide⟩

theorem recon_intermediateGoal_4814_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4814
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4814 4814 7845 7846
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_float4814_rel initSM initPM hSM hPM hInit)

private theorem l2d_logits4816_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4816)
      (denoteGraphDistributed pm initPM 7851) (denoteGraphDistributed pm initPM 7852)
      [4096, 64] [2048, 64] := by
  have h := l2d_float4814_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4815
    (by native_decide) 4815 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4815
    (by native_decide) 4815 [64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4815).shape = [64, 1024] := by
    rw [← hw]; exact hws
  have rs := distributed_reduce2 sm initSM 101
    { rank := 0, op := "OpName.FW_norm_linear", ins := [4814, 4815], outs := [4816] }
    4814 4815 4816 fw_norm_linear (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_norm_linear_out sm st 0 4814 4815 4816)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce2 pm initPM 263
    { rank := 0, op := "OpName.FW_norm_linear", ins := [7845, 4815], outs := [7851] }
    7845 4815 7851 fw_norm_linear (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_norm_linear_out pm st 0 7845 4815 7851)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce2 pm initPM 267
    { rank := 1, op := "OpName.FW_norm_linear", ins := [7846, 4815], outs := [7852] }
    7846 4815 7852 fw_norm_linear (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_norm_linear_out pm st 1 7846 4815 7852)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw,
      fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64
        (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw,
      r0, r1]
  · rw [rs]; exact fw_norm_linear_2d_shape 4096 1024 64 _ _ (by decide) h.full_shape hws
  · rw [r0]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) h.shard0_shape hpw
  · rw [r1]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) h.shard1_shape hpw

theorem recon_intermediateGoal_4816_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4816
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4816 4816 7851 7852
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl
    (l2d_logits4816_rel initSM initPM hSM hPM hInit)

private theorem l2d_topk4817_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4817)
      (denoteGraphDistributed pm initPM 7853) (denoteGraphDistributed pm initPM 7854)
      [4096, 64] [2048, 64] := by
  have h := l2d_logits4816_rel initSM initPM hSM hPM hInit
  let ss := (sm.nodes.take 105).foldl (applyNodeDistributed sm) initSM
  let p0s := (pm.nodes.take 271).foldl (applyNodeDistributed pm) initPM
  let p1s := (pm.nodes.take 275).foldl (applyNodeDistributed pm) initPM
  have es : ss 4816 = denoteGraphDistributed sm initSM 4816 :=
    foldl_take_distributed_eq sm initSM 4816 105 (by native_decide) (by native_decide)
  have e0 : p0s 7851 = denoteGraphDistributed pm initPM 7851 :=
    foldl_take_distributed_eq pm initPM 7851 271 (by native_decide) (by native_decide)
  have e1 : p1s 7852 = denoteGraphDistributed pm initPM 7852 :=
    foldl_take_distributed_eq pm initPM 7852 275 (by native_decide) (by native_decide)
  have hs : (ss 4816).shape.reverse.head? = some 64 := by rw [es, h.full_shape]; rfl
  have h0 : (p0s 7851).shape.reverse.head? = some 64 := by rw [e0, h.shard0_shape]; rfl
  have h1 : (p1s 7852).shape.reverse.head? = some 64 := by rw [e1, h.shard1_shape]; rfl
  have rs := distributed_reduce_fixed_one sm initSM 105
    { rank := 0, op := "OpName.FW_topk_routing", ins := [4816], outs := [4817, 4818, 4819], params := [8, 1] }
    4816 4817 (fun t => (fw_topk_routing t 8 64).1)
    (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_fst sm ss 0 4816 4817 4818 4819 hs)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce_fixed_one pm initPM 271
    { rank := 0, op := "OpName.FW_topk_routing", ins := [7851], outs := [7853, 7855, 7857], params := [8, 1] }
    7851 7853 (fun t => (fw_topk_routing t 8 64).1)
    (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_fst pm p0s 0 7851 7853 7855 7857 h0)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce_fixed_one pm initPM 275
    { rank := 1, op := "OpName.FW_topk_routing", ins := [7852], outs := [7854, 7856, 7858], params := [8, 1] }
    7852 7854 (fun t => (fw_topk_routing t 8 64).1)
    (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_fst pm p1s 1 7852 7854 7856 7858 h1)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value,
      fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64
        (by omega) (by omega) h.shard0_shape h.shard1_shape, r0, r1]
  · rw [rs]; exact fw_topk_routing_fst_shape _ 8 64 4096 (by rw [h.full_shape]; rfl)
  · rw [r0]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h.shard0_shape]; rfl)
  · rw [r1]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h.shard1_shape]; rfl)

theorem recon_intermediateGoal_4817_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4817
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4817 4817 7853 7854
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl
    (l2d_topk4817_rel initSM initPM hSM hPM hInit)

private theorem l2d_topk4818_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4818)
      (denoteGraphDistributed pm initPM 7855) (denoteGraphDistributed pm initPM 7856)
      [4096, 64] [2048, 64] := by
  have h := l2d_logits4816_rel initSM initPM hSM hPM hInit
  let ss := (sm.nodes.take 105).foldl (applyNodeDistributed sm) initSM
  let p0s := (pm.nodes.take 271).foldl (applyNodeDistributed pm) initPM
  let p1s := (pm.nodes.take 275).foldl (applyNodeDistributed pm) initPM
  have es : ss 4816 = denoteGraphDistributed sm initSM 4816 :=
    foldl_take_distributed_eq sm initSM 4816 105 (by native_decide) (by native_decide)
  have e0 : p0s 7851 = denoteGraphDistributed pm initPM 7851 :=
    foldl_take_distributed_eq pm initPM 7851 271 (by native_decide) (by native_decide)
  have e1 : p1s 7852 = denoteGraphDistributed pm initPM 7852 :=
    foldl_take_distributed_eq pm initPM 7852 275 (by native_decide) (by native_decide)
  have hs : (ss 4816).shape.reverse.head? = some 64 := by rw [es, h.full_shape]; rfl
  have h0 : (p0s 7851).shape.reverse.head? = some 64 := by rw [e0, h.shard0_shape]; rfl
  have h1 : (p1s 7852).shape.reverse.head? = some 64 := by rw [e1, h.shard1_shape]; rfl
  have rs := distributed_reduce_fixed_one sm initSM 105
    { rank := 0, op := "OpName.FW_topk_routing", ins := [4816], outs := [4817, 4818, 4819], params := [8, 1] }
    4816 4818 (fun t => (fw_topk_routing t 8 64).2.1)
    (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_snd sm ss 0 4816 4817 4818 4819 (by decide) hs)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce_fixed_one pm initPM 271
    { rank := 0, op := "OpName.FW_topk_routing", ins := [7851], outs := [7853, 7855, 7857], params := [8, 1] }
    7851 7855 (fun t => (fw_topk_routing t 8 64).2.1)
    (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_snd pm p0s 0 7851 7853 7855 7857 (by decide) h0)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce_fixed_one pm initPM 275
    { rank := 1, op := "OpName.FW_topk_routing", ins := [7852], outs := [7854, 7856, 7858], params := [8, 1] }
    7852 7856 (fun t => (fw_topk_routing t 8 64).2.1)
    (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_snd pm p1s 1 7852 7854 7856 7858 (by decide) h1)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value,
      fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 8 64
        (by omega) (by omega) h.shard0_shape h.shard1_shape, r0, r1]
  · rw [rs]; exact fw_topk_routing_snd_shape _ 8 64 4096 (by rw [h.full_shape]; rfl)
  · rw [r0]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [h.shard0_shape]; rfl)
  · rw [r1]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [h.shard1_shape]; rfl)

theorem recon_intermediateGoal_4818_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4818
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4818 4818 7855 7856
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl
    (l2d_topk4818_rel initSM initPM hSM hPM hInit)

/-! ### Layer-3 full-expert MoE boundary (pure distributed evaluator) -/

private theorem l2d_token7523_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7523)
      (denoteGraphDistributed pm initPM 14766) (denoteGraphDistributed pm initPM 14789)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_rms4813_rel initSM initPM hSM hPM hInit
  have rs := distributed_reduce1 sm initSM 96
    { rank := 0, op := "OpName.FW_multiref", ins := [4813],
      outs := [7519, 7523, 7527, 7531, 7535], params := [5] }
    4813 7523 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos1_out sm st 0 4813 7519 7523 7527 7531 7535
      (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce1 pm initPM 253
    { rank := 0, op := "OpName.FW_multiref", ins := [7843],
      outs := [14762, 14766, 14770, 14774, 14778], params := [5] }
    7843 14766 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos1_out pm st 0 7843 14762 14766 14770 14774 14778
      (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce1 pm initPM 254
    { rank := 1, op := "OpName.FW_multiref", ins := [7844],
      outs := [14785, 14789, 14793, 14797, 14801], params := [5] }
    7844 14789 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos1_out pm st 1 7844 14785 14789 14793 14797 14801
      (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rs r0 r1
  exact ⟨by rw [rs, h.value, r0, r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

theorem recon_intermediateGoal_7523_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7523
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_7523 7523 14766 14789
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_token7523_rel initSM initPM hSM hPM hInit)

private def layer3SmMoe : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [7523, 4817, 4818, 4820, 4821], outs := [4822], params := [64, 0, 64, 8] }
private def layer3PmMoe0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [14766, 7853, 7855, 7859, 7861], outs := [7863], params := [64, 0, 32, 8] }
private def layer3PmMoe1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm",
    ins := [14789, 7854, 7856, 7860, 7862], outs := [7864], params := [64, 32, 64, 8] }

set_option maxRecDepth 1000000 in
private theorem layer3_sm_node109 : sm.nodes[109]'(by native_decide) = layer3SmMoe := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer3_pm_node279 : pm.nodes[279]'(by native_decide) = layer3PmMoe0 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer3_pm_node282 : pm.nodes[282]'(by native_decide) = layer3PmMoe1 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer3_sm_buddies : sm.replicaBuddies layer3SmMoe = [layer3SmMoe] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer3_pm_buddies0 :
    pm.replicaBuddies layer3PmMoe0 = [layer3PmMoe0, layer3PmMoe1] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer3_pm_buddies1 :
    pm.replicaBuddies layer3PmMoe1 = [layer3PmMoe0, layer3PmMoe1] := by native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
theorem recon_intermediateGoal_4822_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4822
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have hi := l2d_token7523_rel initSM initPM hSM hPM hInit
  have hrp := l2d_topk4817_rel initSM initPM hSM hPM hInit
  have hrm := l2d_topk4818_rel initSM initPM hSM hPM hInit

  have hW13 := hInit initGoal_4820 (by native_decide)
  have hW2 := hInit initGoal_4821 (by native_decide)
  have hsW13 := hW13.2.1
  have hsW2 := hW2.2.1
  simp only [initGoal_4820, List.map, List.cons.injEq, and_true] at hsW13
  simp only [initGoal_4821, List.map, List.cons.injEq, and_true] at hsW2
  have hsW13A : (denoteGraphDistributed pm initPM 7859).shape = [32, 1024, 1024] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 7859
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW13.1
  have hsW13B : (denoteGraphDistributed pm initPM 7860).shape = [32, 1024, 1024] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 7860
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW13.2
  have hsW2A : (denoteGraphDistributed pm initPM 7861).shape = [32, 1024, 512] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 7861
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW2.1
  have hsW2B : (denoteGraphDistributed pm initPM 7862).shape = [32, 1024, 512] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 7862
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW2.2
  have hbrW13 : denoteGraphDistributed sm initSM 4820 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 7859, denoteGraphDistributed pm initPM 7860] := by
    have hv := hW13.2.2
    rw [reconstructForGoal_of_not_replicated initGoal_4820 pm.numRanks _ rfl] at hv
    simp only [initGoal_4820, List.map] at hv
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
      (by rw [hsW13.1]; decide)] at hv
    have ds : denoteGraphDistributed sm initSM 4820 = initSM 4820 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written sm sm.nodes initSM 4820
        layer1_sm_nodes_nonempty (by native_decide)
    have dp0 : denoteGraphDistributed pm initPM 7859 = initPM 7859 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 7859
        layer1_pm_nodes_nonempty (by native_decide)
    have dp1 : denoteGraphDistributed pm initPM 7860 = initPM 7860 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 7860
        layer1_pm_nodes_nonempty (by native_decide)
    rw [ds, dp0, dp1]
    exact hv
  have hbrW2 : denoteGraphDistributed sm initSM 4821 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 7861, denoteGraphDistributed pm initPM 7862] := by
    have hv := hW2.2.2
    rw [reconstructForGoal_of_not_replicated initGoal_4821 pm.numRanks _ rfl] at hv
    simp only [initGoal_4821, List.map] at hv
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
      (by rw [hsW2.1]; decide)] at hv
    have ds : denoteGraphDistributed sm initSM 4821 = initSM 4821 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written sm sm.nodes initSM 4821
        layer1_sm_nodes_nonempty (by native_decide)
    have dp0 : denoteGraphDistributed pm initPM 7861 = initPM 7861 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 7861
        layer1_pm_nodes_nonempty (by native_decide)
    have dp1 : denoteGraphDistributed pm initPM 7862 = initPM 7862 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 7862
        layer1_pm_nodes_nonempty (by native_decide)
    rw [ds, dp0, dp1]
    exact hv
  have hW13single : allGatherPrimDimN 0 1 0 [denoteGraphDistributed sm initSM 4820] =
      denoteGraphDistributed sm initSM 4820 := by
    have hs : (denoteGraphDistributed sm initSM 4820).shape = [64, 1024, 1024] := by
      rw [hbrW13, allGatherPrimDimN_shape 0 2 _ [32, 1024, 1024] (by simp [hsW13A])]
      simp [List.set]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hs]; decide)
  have hW2single : allGatherPrimDimN 0 1 0 [denoteGraphDistributed sm initSM 4821] =
      denoteGraphDistributed sm initSM 4821 := by
    have hs : (denoteGraphDistributed sm initSM 4821).shape = [64, 1024, 512] := by
      rw [hbrW2, allGatherPrimDimN_shape 0 2 _ [32, 1024, 512] (by simp [hsW2A])]
      simp [List.set]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hs]; decide)

  have hSMout : denoteGraphDistributed sm initSM 4822 =
      fw_all2all_moe_gmm_full (denoteGraphDistributed sm initSM 7523)
        (denoteGraphDistributed sm initSM 4817) (denoteGraphDistributed sm initSM 4818)
        [denoteGraphDistributed pm initPM 7859, denoteGraphDistributed pm initPM 7860]
        [denoteGraphDistributed pm initPM 7861, denoteGraphDistributed pm initPM 7862]
        64 8 (((10 : Nat) : Scalar)) := by
    have hk : 109 < sm.nodes.length := by native_decide
    rw [distributed_moe_reduce sm initSM 109 layer3SmMoe 4822 hk
      (show sm.nodes[109]'hk = layer3SmMoe from layer3_sm_node109)
      rfl rfl (by native_decide) (by native_decide)]
    unfold applyNodeFullExpertMoE_value
    rw [layer3_sm_buddies]
    simp only [layer3SmMoe, List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    rw [foldl_take_distributed_eq sm initSM 7523 109 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 4817 109 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 4818 109 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 4820 109 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 4821 109 (by native_decide) (by native_decide)]
    unfold fw_all2all_moe_gmm_full
    simp only [List.length_cons, List.length_nil]
    rw [hW13single, hW2single, hbrW13, hbrW2]
  have hP0 : denoteGraphDistributed pm initPM 7863 =
      fw_all2all_moe_gmm_full (denoteGraphDistributed pm initPM 14766)
        (denoteGraphDistributed pm initPM 7853) (denoteGraphDistributed pm initPM 7855)
        [denoteGraphDistributed pm initPM 7859, denoteGraphDistributed pm initPM 7860]
        [denoteGraphDistributed pm initPM 7861, denoteGraphDistributed pm initPM 7862]
        64 8 (((10 : Nat) : Scalar)) := by
    have hk : 279 < pm.nodes.length := by native_decide
    rw [distributed_moe_reduce pm initPM 279 layer3PmMoe0 7863 hk
      (show pm.nodes[279]'hk = layer3PmMoe0 from layer3_pm_node279)
      rfl rfl (by native_decide) (by native_decide)]
    unfold applyNodeFullExpertMoE_value
    rw [layer3_pm_buddies0]
    simp only [layer3PmMoe0, layer3PmMoe1, List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    rw [foldl_take_distributed_eq pm initPM 14766 279 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 7853 279 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 7855 279 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 7859 279 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 7860 279 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 7861 279 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 7862 279 (by native_decide) (by native_decide)]
  have hP1 : denoteGraphDistributed pm initPM 7864 =
      fw_all2all_moe_gmm_full (denoteGraphDistributed pm initPM 14789)
        (denoteGraphDistributed pm initPM 7854) (denoteGraphDistributed pm initPM 7856)
        [denoteGraphDistributed pm initPM 7859, denoteGraphDistributed pm initPM 7860]
        [denoteGraphDistributed pm initPM 7861, denoteGraphDistributed pm initPM 7862]
        64 8 (((10 : Nat) : Scalar)) := by
    have hk : 282 < pm.nodes.length := by native_decide
    rw [distributed_moe_reduce pm initPM 282 layer3PmMoe1 7864 hk
      (show pm.nodes[282]'hk = layer3PmMoe1 from layer3_pm_node282)
      rfl rfl (by native_decide) (by native_decide)]
    unfold applyNodeFullExpertMoE_value
    rw [layer3_pm_buddies1]
    simp only [layer3PmMoe0, layer3PmMoe1, List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    rw [foldl_take_distributed_eq pm initPM 14789 282 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 7854 282 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 7856 282 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 7859 282 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 7860 282 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 7861 282 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 7862 282 (by native_decide) (by native_decide)]

  have hc := fw_all2all_moe_gmm_full_split_commute_2
    (denoteGraphDistributed pm initPM 14766) (denoteGraphDistributed pm initPM 14789)
    (denoteGraphDistributed pm initPM 7853) (denoteGraphDistributed pm initPM 7854)
    (denoteGraphDistributed pm initPM 7855) (denoteGraphDistributed pm initPM 7856)
    (denoteGraphDistributed pm initPM 7859) (denoteGraphDistributed pm initPM 7860)
    (denoteGraphDistributed pm initPM 7861) (denoteGraphDistributed pm initPM 7862)
    2048 1024 32 8 1024 512 (((10 : Nat) : Scalar))
    (by omega) (by omega) (by omega) (by omega) (by omega) rfl
    hi.shard0_shape hi.shard1_shape hrp.shard0_shape hrp.shard1_shape
    hrm.shard0_shape hrm.shard1_shape hsW13A hsW13B hsW2A hsW2B
  have hval : denoteGraphDistributed sm initSM 4822 = allGatherPrimDimN 0 pm.numRanks 0
      [denoteGraphDistributed pm initPM 7863, denoteGraphDistributed pm initPM 7864] := by
    rw [hSMout, hi.value, hrp.value, hrm.value, hc, ← hP0, ← hP1,
      show pm.numRanks = 2 from rfl]
  have hsP0 : (denoteGraphDistributed pm initPM 7863).shape = [2048, 1024] := by
    rw [hP0]
    exact fw_all2all_moe_gmm_full_shape
      (input := denoteGraphDistributed pm initPM 14766)
      (rp := denoteGraphDistributed pm initPM 7853)
      (rm := denoteGraphDistributed pm initPM 7855)
      (w13s := [denoteGraphDistributed pm initPM 7859, denoteGraphDistributed pm initPM 7860])
      (w2s := [denoteGraphDistributed pm initPM 7861, denoteGraphDistributed pm initPM 7862])
      (numExp := 64) (topK := 8) (swigluLimit := (((10 : Nat) : Scalar)))
      (lDim := 2048) (hModel := 1024)
      (by rw [hi.shard0_shape]; rfl) (by rw [hi.shard0_shape]; rfl)
  have hsP1 : (denoteGraphDistributed pm initPM 7864).shape = [2048, 1024] := by
    rw [hP1]
    exact fw_all2all_moe_gmm_full_shape
      (input := denoteGraphDistributed pm initPM 14789)
      (rp := denoteGraphDistributed pm initPM 7854)
      (rm := denoteGraphDistributed pm initPM 7856)
      (w13s := [denoteGraphDistributed pm initPM 7859, denoteGraphDistributed pm initPM 7860])
      (w2s := [denoteGraphDistributed pm initPM 7861, denoteGraphDistributed pm initPM 7862])
      (numExp := 64) (topK := 8) (swigluLimit := (((10 : Nat) : Scalar)))
      (lDim := 2048) (hModel := 1024)
      (by rw [hi.shard1_shape]; rfl) (by rw [hi.shard1_shape]; rfl)
  have hsSM : (denoteGraphDistributed sm initSM 4822).shape = [4096, 1024] := by
    rw [hval, show pm.numRanks = 2 from rfl,
      allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsP0])]
    simp [List.set]
  exact wrap_2tp_allGather_gen _ _ intermediateGoal_4822 4822 7863 7864
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    hval hsSM hsP0 hsP1

/-! ### Layer-3 gate/expert side branches (pure distributed evaluator) -/

private theorem l2d_reshape4823_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4823)
      (denoteGraphDistributed pm initPM 7865) (denoteGraphDistributed pm initPM 7866)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_rms4813_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 96
    { rank := 0, op := "OpName.FW_multiref", ins := [4813],
      outs := [7519, 7523, 7527, 7531, 7535], params := [5] }
    4813 7527 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos2_out sm st 0 4813 7519 7523 7527 7531 7535
      (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 253
    { rank := 0, op := "OpName.FW_multiref", ins := [7843],
      outs := [14762, 14766, 14770, 14774, 14778], params := [5] }
    7843 14770 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos2_out pm st 0 7843 14762 14766 14770 14774 14778
      (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 254
    { rank := 1, op := "OpName.FW_multiref", ins := [7844],
      outs := [14785, 14789, 14793, 14797, 14801], params := [5] }
    7844 14793 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos2_out pm st 1 7844 14785 14789 14793 14797 14801
      (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have rs := l2d_reshape sm initSM 98 0 7527 4823 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l2d_reshape pm initPM 256 0 14770 7865 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l2d_reshape pm initPM 260 1 14793 7866 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 4823 = denoteGraphDistributed sm initSM 7527 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ (by rw [s]; exact h.full_shape)]
  have e0 : denoteGraphDistributed pm initPM 7865 = denoteGraphDistributed pm initPM 14770 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ (by rw [p0]; exact h.shard0_shape)]
  have e1 : denoteGraphDistributed pm initPM 7866 = denoteGraphDistributed pm initPM 14793 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ (by rw [p1]; exact h.shard1_shape)]
  exact ⟨by rw [es, s, h.value, ← p0, ← p1, ← e0, ← e1], by rw [es, s]; exact h.full_shape,
    by rw [e0, p0]; exact h.shard0_shape, by rw [e1, p1]; exact h.shard1_shape, by decide⟩

theorem recon_intermediateGoal_4823_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4823
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4823 4823 7865 7866
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_reshape4823_rel initSM initPM hSM hPM hInit)

private theorem l2d_reshape4828_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4828)
      (denoteGraphDistributed pm initPM 7879) (denoteGraphDistributed pm initPM 7880)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_rms4813_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 96
    { rank := 0, op := "OpName.FW_multiref", ins := [4813], outs := [7519, 7523, 7527, 7531, 7535], params := [5] }
    4813 7531 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos3_out sm st 0 4813 7519 7523 7527 7531 7535
      (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 253
    { rank := 0, op := "OpName.FW_multiref", ins := [7843], outs := [14762, 14766, 14770, 14774, 14778], params := [5] }
    7843 14774 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos3_out pm st 0 7843 14762 14766 14770 14774 14778
      (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 254
    { rank := 1, op := "OpName.FW_multiref", ins := [7844], outs := [14785, 14789, 14793, 14797, 14801], params := [5] }
    7844 14797 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos3_out pm st 1 7844 14785 14789 14793 14797 14801
      (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have rs := l2d_reshape sm initSM 99 0 7531 4828 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_reshape pm initPM 257 0 14774 7879 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_reshape pm initPM 261 1 14797 7880 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 4828 = denoteGraphDistributed sm initSM 7531 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ (by rw [s]; exact h.full_shape)]
  have e0 : denoteGraphDistributed pm initPM 7879 = denoteGraphDistributed pm initPM 14774 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ (by rw [p0]; exact h.shard0_shape)]
  have e1 : denoteGraphDistributed pm initPM 7880 = denoteGraphDistributed pm initPM 14797 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ (by rw [p1]; exact h.shard1_shape)]
  exact ⟨by rw [es, s, h.value, ← p0, ← p1, ← e0, ← e1], by rw [es, s]; exact h.full_shape,
    by rw [e0, p0]; exact h.shard0_shape, by rw [e1, p1]; exact h.shard1_shape, by decide⟩

theorem recon_intermediateGoal_4828_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4828
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4828 4828 7879 7880
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_reshape4828_rel initSM initPM hSM hPM hInit)

private theorem l2d_reshape4832_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4832)
      (denoteGraphDistributed pm initPM 7897) (denoteGraphDistributed pm initPM 7898)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_rms4813_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 96
    { rank := 0, op := "OpName.FW_multiref", ins := [4813], outs := [7519, 7523, 7527, 7531, 7535], params := [5] }
    4813 7535 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos4_out sm st 0 4813 7519 7523 7527 7531 7535
      (by decide) (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 253
    { rank := 0, op := "OpName.FW_multiref", ins := [7843], outs := [14762, 14766, 14770, 14774, 14778], params := [5] }
    7843 14778 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos4_out pm st 0 7843 14762 14766 14770 14774 14778
      (by decide) (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 254
    { rank := 1, op := "OpName.FW_multiref", ins := [7844], outs := [14785, 14789, 14793, 14797, 14801], params := [5] }
    7844 14801 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos4_out pm st 1 7844 14785 14789 14793 14797 14801
      (by decide) (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have rs := l2d_reshape sm initSM 100 0 7535 4832 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_reshape pm initPM 258 0 14778 7897 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_reshape pm initPM 262 1 14801 7898 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 4832 = denoteGraphDistributed sm initSM 7535 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ (by rw [s]; exact h.full_shape)]
  have e0 : denoteGraphDistributed pm initPM 7897 = denoteGraphDistributed pm initPM 14778 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ (by rw [p0]; exact h.shard0_shape)]
  have e1 : denoteGraphDistributed pm initPM 7898 = denoteGraphDistributed pm initPM 14801 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ (by rw [p1]; exact h.shard1_shape)]
  exact ⟨by rw [es, s, h.value, ← p0, ← p1, ← e0, ← e1], by rw [es, s]; exact h.full_shape,
    by rw [e0, p0]; exact h.shard0_shape, by rw [e1, p1]; exact h.shard1_shape, by decide⟩

theorem recon_intermediateGoal_4832_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4832
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4832 4832 7897 7898
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_reshape4832_rel initSM initPM hSM hPM hInit)

private theorem l2d_linear4825_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4825)
      (denoteGraphDistributed pm initPM 7869) (denoteGraphDistributed pm initPM 7870)
      [4096, 1] [2048, 1] := by
  have h := l2d_reshape4823_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4824
    (by native_decide) 4824 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4824
    (by native_decide) 4824 [1, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4824).shape = [1, 1024] := by rw [← hw]; exact hws
  have rs := l2d_linear sm initSM 102 0 4823 4824 4825
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_linear pm initPM 264 0 7865 4824 7869
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_linear pm initPM 268 1 7866 4824 7870
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 1 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 1 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 1 _ _ h.shard1_shape hpw

theorem recon_intermediateGoal_4825_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4825
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4825 4825 7869 7870
    [4096, 1] [2048, 1] rfl rfl rfl rfl rfl rfl
    (l2d_linear4825_rel initSM initPM hSM hPM hInit)

private theorem l2d_linear4830_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4830)
      (denoteGraphDistributed pm initPM 7883) (denoteGraphDistributed pm initPM 7884)
      [4096, 512] [2048, 512] := by
  have h := l2d_reshape4828_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4829
    (by native_decide) 4829 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4829
    (by native_decide) 4829 [512, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4829).shape = [512, 1024] := by rw [← hw]; exact hws
  have rs := l2d_linear sm initSM 103 0 4828 4829 4830
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_linear pm initPM 265 0 7879 4829 7883
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_linear pm initPM 269 1 7880 4829 7884
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 512 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 512 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 512 _ _ h.shard1_shape hpw

theorem recon_intermediateGoal_4830_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4830
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4830 4830 7883 7884
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l2d_linear4830_rel initSM initPM hSM hPM hInit)

private theorem l2d_linear4834_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4834)
      (denoteGraphDistributed pm initPM 7901) (denoteGraphDistributed pm initPM 7902)
      [4096, 512] [2048, 512] := by
  have h := l2d_reshape4832_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4833
    (by native_decide) 4833 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4833
    (by native_decide) 4833 [512, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4833).shape = [512, 1024] := by rw [← hw]; exact hws
  have rs := l2d_linear sm initSM 104 0 4832 4833 4834
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_linear pm initPM 266 0 7897 4833 7901
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_linear pm initPM 270 1 7898 4833 7902
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 512 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 512 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 512 _ _ h.shard1_shape hpw

theorem recon_intermediateGoal_4834_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4834
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4834 4834 7901 7902
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l2d_linear4834_rel initSM initPM hSM hPM hInit)

private theorem l2d_view4826_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4826)
      (denoteGraphDistributed pm initPM 7875) (denoteGraphDistributed pm initPM 7876)
      [4096, 1] [2048, 1] := by
  have h := l2d_linear4825_rel initSM initPM hSM hPM hInit
  have rs := l2d_view sm initSM 106 0 4825 4826 4096 [1]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l2d_view pm initPM 272 0 7869 7875 2048 [1]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l2d_view pm initPM 276 1 7870 7876 2048 [1]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 4826 = denoteGraphDistributed sm initSM 4825 := by
    rw [rs, fw_view_id_shape [4096, 1] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 7875 = denoteGraphDistributed pm initPM 7869 := by
    rw [r0, fw_view_id_shape [2048, 1] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 7876 = denoteGraphDistributed pm initPM 7870 := by
    rw [r1, fw_view_id_shape [2048, 1] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

theorem recon_intermediateGoal_4826_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4826
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4826 4826 7875 7876
    [4096, 1] [2048, 1] rfl rfl rfl rfl rfl rfl
    (l2d_view4826_rel initSM initPM hSM hPM hInit)

private theorem l2d_view4831_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4831)
      (denoteGraphDistributed pm initPM 7893) (denoteGraphDistributed pm initPM 7894)
      [4096, 512] [2048, 512] := by
  have h := l2d_linear4830_rel initSM initPM hSM hPM hInit
  have rs := l2d_view sm initSM 107 0 4830 4831 4096 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l2d_view pm initPM 273 0 7883 7893 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l2d_view pm initPM 277 1 7884 7894 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 4831 = denoteGraphDistributed sm initSM 4830 := by
    rw [rs, fw_view_id_shape [4096, 512] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 7893 = denoteGraphDistributed pm initPM 7883 := by
    rw [r0, fw_view_id_shape [2048, 512] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 7894 = denoteGraphDistributed pm initPM 7884 := by
    rw [r1, fw_view_id_shape [2048, 512] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

theorem recon_intermediateGoal_4831_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4831
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4831 4831 7893 7894
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l2d_view4831_rel initSM initPM hSM hPM hInit)

private theorem l2d_view4835_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4835)
      (denoteGraphDistributed pm initPM 7911) (denoteGraphDistributed pm initPM 7912)
      [4096, 512] [2048, 512] := by
  have h := l2d_linear4834_rel initSM initPM hSM hPM hInit
  have rs := l2d_view sm initSM 108 0 4834 4835 4096 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l2d_view pm initPM 274 0 7901 7911 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l2d_view pm initPM 278 1 7902 7912 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 4835 = denoteGraphDistributed sm initSM 4834 := by
    rw [rs, fw_view_id_shape [4096, 512] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 7911 = denoteGraphDistributed pm initPM 7901 := by
    rw [r0, fw_view_id_shape [2048, 512] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 7912 = denoteGraphDistributed pm initPM 7902 := by
    rw [r1, fw_view_id_shape [2048, 512] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

theorem recon_intermediateGoal_4835_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4835
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4835 4835 7911 7912
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l2d_view4835_rel initSM initPM hSM hPM hInit)

/-! ### Layer-3 MoE postprocessing and cross-block residual tail -/

private theorem l2d_sigmoid4827_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4827)
      (denoteGraphDistributed pm initPM 7877) (denoteGraphDistributed pm initPM 7878)
      [4096, 1] [2048, 1] := by
  have h := l2d_view4826_rel initSM initPM hSM hPM hInit
  have rs := l2d_sigmoid sm initSM 110 0 4826 4827 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_sigmoid pm initPM 280 0 7875 7877 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_sigmoid pm initPM 283 1 7876 7878 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, fw_sigmoid_allGather0_commute_2 _ _ 2048 1
      (by omega) (by omega) h.shard0_shape h.shard1_shape, r0, r1]
  · rw [rs, fw_sigmoid_shape]; exact h.full_shape
  · rw [r0, fw_sigmoid_shape]; exact h.shard0_shape
  · rw [r1, fw_sigmoid_shape]; exact h.shard1_shape

theorem recon_intermediateGoal_4827_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4827
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4827 4827 7877 7878
    [4096, 1] [2048, 1] rfl rfl rfl rfl rfl rfl
    (l2d_sigmoid4827_rel initSM initPM hSM hPM hInit)

private theorem l2d_swiglu4836_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4836)
      (denoteGraphDistributed pm initPM 7915) (denoteGraphDistributed pm initPM 7916)
      [4096, 512] [2048, 512] := by
  have hx := l2d_view4831_rel initSM initPM hSM hPM hInit
  have hy := l2d_view4835_rel initSM initPM hSM hPM hInit
  have rs := l2d_swiglu sm initSM 111 0 4831 4835 4836 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_swiglu pm initPM 281 0 7893 7911 7915 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_swiglu pm initPM 284 1 7894 7912 7916 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, hx.value, hy.value,
      fw_swiglu_allGather0_commute_2 _ _ _ _ 2048 512 (by omega) (by omega)
        hx.shard0_shape hx.shard1_shape hy.shard0_shape hy.shard1_shape, r0, r1]
  · rw [rs]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hy.full_shape
  · rw [r0]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hy.shard0_shape
  · rw [r1]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hy.shard1_shape

theorem recon_intermediateGoal_4836_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4836
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4836 4836 7915 7916
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l2d_swiglu4836_rel initSM initPM hSM hPM hInit)

private theorem l2d_reshape4837_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4837)
      (denoteGraphDistributed pm initPM 7917) (denoteGraphDistributed pm initPM 7918)
      [4096, 512] [2048, 512] := by
  have h := l2d_swiglu4836_rel initSM initPM hSM hPM hInit
  have rs := l2d_reshape sm initSM 112 0 4836 4837 4096 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l2d_reshape pm initPM 285 0 7915 7917 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l2d_reshape pm initPM 286 1 7916 7918 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, show ([4096, 512] : Shape) = [2048 * 2, 512] from rfl,
      fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) h.shard0_shape h.shard1_shape,
      r0, r1]
  · rw [rs]; rfl
  · rw [r0]; rfl
  · rw [r1]; rfl

theorem recon_intermediateGoal_4837_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4837
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4837 4837 7917 7918
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l2d_reshape4837_rel initSM initPM hSM hPM hInit)

private theorem l2d_linear4839_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4839)
      (denoteGraphDistributed pm initPM 7923) (denoteGraphDistributed pm initPM 7924)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_reshape4837_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4838
    (by native_decide) 4838 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4838
    (by native_decide) 4838 [1024, 512] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4838).shape = [1024, 512] := by
    rw [← hw]; exact hws
  have rs := l2d_linear sm initSM 113 0 4837 4838 4839 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_linear pm initPM 287 0 7917 4838 7923 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_linear pm initPM 288 1 7918 4838 7924 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw,
      fw_linear_allGather0_commute_2_of _ _ _ 2048 512 1024 (by omega) (by omega) (by omega)
        h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 512 1024 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 512 1024 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 512 1024 _ _ h.shard1_shape hpw

theorem recon_intermediateGoal_4839_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4839
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4839 4839 7923 7924
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_linear4839_rel initSM initPM hSM hPM hInit)

private theorem l2d_view4840_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4840)
      (denoteGraphDistributed pm initPM 7933) (denoteGraphDistributed pm initPM 7934)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_linear4839_rel initSM initPM hSM hPM hInit
  have rs := l2d_view sm initSM 114 0 4839 4840 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l2d_view pm initPM 289 0 7923 7933 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l2d_view pm initPM 290 1 7924 7934 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, show ([4096, 1024] : Shape) = [2048 * 2, 1024] from rfl,
      fw_view_allGather0_commute_2_of _ _ 2048 1024 (by omega) h.shard0_shape h.shard1_shape,
      r0, r1]
  · rw [rs]; rfl
  · rw [r0]; rfl
  · rw [r1]; rfl

theorem recon_intermediateGoal_4840_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4840
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4840 4840 7933 7934
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_view4840_rel initSM initPM hSM hPM hInit)

private theorem l2d_mul4841_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4841)
      (denoteGraphDistributed pm initPM 7937) (denoteGraphDistributed pm initPM 7938)
      [4096, 1024] [2048, 1024] := by
  have hs := l2d_sigmoid4827_rel initSM initPM hSM hPM hInit
  have hv := l2d_view4840_rel initSM initPM hSM hPM hInit
  have rs := l2d_mul sm initSM 115 0 4827 4840 4841 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_mul pm initPM 291 0 7877 7933 7937 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_mul pm initPM 292 1 7878 7934 7938 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have mulShape : ∀ (x y : Tensor) (a : Nat),
      x.shape = [a, 1] → y.shape = [a, 1024] → (elemwiseMul x y).shape = [a, 1024] := by
    intro x y a hx hy
    show outShape2 x y = [a, 1024]
    unfold outShape2
    rw [hx, hy]
    show (max a a) :: (1024 : Nat) :: [] = [a, 1024]
    rw [Nat.max_self]
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, hs.value, hv.value,
      fw_mul_allGather0_commute_2_of_broadcast _ _ _ _ 2048 1024
        (by omega) (by omega) (by decide) (by decide) (by decide)
        hs.shard0_shape hs.shard1_shape hv.shard0_shape hv.shard1_shape, r0, r1]
  · rw [rs]; exact mulShape _ _ 4096 hs.full_shape hv.full_shape
  · rw [r0]; exact mulShape _ _ 2048 hs.shard0_shape hv.shard0_shape
  · rw [r1]; exact mulShape _ _ 2048 hs.shard1_shape hv.shard1_shape

theorem recon_intermediateGoal_4841_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4841
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4841 4841 7937 7938
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_mul4841_rel initSM initPM hSM hPM hInit)

private theorem l2d_add4842_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4842)
      (denoteGraphDistributed pm initPM 7941) (denoteGraphDistributed pm initPM 7942)
      [4096, 1024] [2048, 1024] := by
  have ha := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_4822 4822 7863 7864
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4822_distributed initSM initPM hSM hPM hInit)
  have hb := l2d_mul4841_rel initSM initPM hSM hPM hInit
  have rs := l2d_add sm initSM 116 0 4822 4841 4842 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_add pm initPM 293 0 7863 7937 7941 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_add pm initPM 294 1 7864 7938 7942 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, ha.value, hb.value,
      fw_add_allGather0_commute_2_2048_1024 _ _ _ _ ha.shard0_shape ha.shard1_shape
        hb.shard0_shape hb.shard1_shape, r0, r1]
  · rw [rs]; exact elemwiseAdd_shape_of_shapes _ _ [4096, 1024] ha.full_shape hb.full_shape
  · rw [r0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] ha.shard0_shape hb.shard0_shape
  · rw [r1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] ha.shard1_shape hb.shard1_shape

theorem recon_intermediateGoal_4842_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4842
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4842 4842 7941 7942
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_add4842_rel initSM initPM hSM hPM hInit)

private theorem l2d_goal7512_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7512)
      (denoteGraphDistributed pm initPM 14747) (denoteGraphDistributed pm initPM 14755)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_4811 4811 7839 7840
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4811_distributed initSM initPM hSM hPM hInit)
  have rs := distributed_reduce1 sm initSM 94
    { rank := 0, op := "OpName.FW_multiref", ins := [4811], outs := [7508, 7512], params := [2] }
    4811 7512 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' sm st 0 4811 7508 7512 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce1 pm initPM 249
    { rank := 0, op := "OpName.FW_multiref", ins := [7839], outs := [14743, 14747], params := [2] }
    7839 14747 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 0 7839 14743 14747 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce1 pm initPM 250
    { rank := 1, op := "OpName.FW_multiref", ins := [7840], outs := [14751, 14755], params := [2] }
    7840 14755 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 1 7840 14751 14755 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rs r0 r1
  exact ⟨by rw [rs, h.value, r0, r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

theorem recon_intermediateGoal_7512_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7512
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_7512 7512 14747 14755
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_goal7512_rel initSM initPM hSM hPM hInit)

private theorem l2d_float4843_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4843)
      (denoteGraphDistributed pm initPM 7947) (denoteGraphDistributed pm initPM 7948)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_add4842_rel initSM initPM hSM hPM hInit
  have rs := l2d_float sm initSM 117 0 4842 4843 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_float pm initPM 295 0 7941 7947 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_float pm initPM 296 1 7942 7948 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  exact ⟨by rw [rs, h.value, r0, r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

theorem recon_intermediateGoal_4843_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4843
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4843 4843 7947 7948
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_float4843_rel initSM initPM hSM hPM hInit)

private theorem l2d_add4844_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4844)
      (denoteGraphDistributed pm initPM 7951) (denoteGraphDistributed pm initPM 7952)
      [4096, 1024] [2048, 1024] := by
  have ha := l2d_goal7512_rel initSM initPM hSM hPM hInit
  have hb := l2d_float4843_rel initSM initPM hSM hPM hInit
  have rs := l2d_add sm initSM 118 0 7512 4843 4844 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_add pm initPM 297 0 14747 7947 7951 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_add pm initPM 298 1 14755 7948 7952 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, ha.value, hb.value,
      fw_add_allGather0_commute_2_2048_1024 _ _ _ _ ha.shard0_shape ha.shard1_shape
        hb.shard0_shape hb.shard1_shape, r0, r1]
  · rw [rs]; exact elemwiseAdd_shape_of_shapes _ _ [4096, 1024] ha.full_shape hb.full_shape
  · rw [r0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] ha.shard0_shape hb.shard0_shape
  · rw [r1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] ha.shard1_shape hb.shard1_shape

theorem recon_intermediateGoal_4844_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4844
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4844 4844 7951 7952
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_add4844_rel initSM initPM hSM hPM hInit)

/-! ### Layer-4 pre-attention normalization and Q/K/V projections -/

private theorem l2d_carry7539_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7539)
      (denoteGraphDistributed pm initPM 14805) (denoteGraphDistributed pm initPM 14813)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_add4844_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 119
    { rank := 0, op := "OpName.FW_multiref", ins := [4844], outs := [7539, 7543], params := [2] }
    4844 7539 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out sm st 0 4844 7539 7543)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 299
    { rank := 0, op := "OpName.FW_multiref", ins := [7951], outs := [14805, 14809], params := [2] }
    7951 14805 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 0 7951 14805 14809)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 300
    { rank := 1, op := "OpName.FW_multiref", ins := [7952], outs := [14813, 14817], params := [2] }
    7952 14813 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 1 7952 14813 14817)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  exact ⟨by rw [s, h.value, p0, p1], by rw [s]; exact h.full_shape,
    by rw [p0]; exact h.shard0_shape, by rw [p1]; exact h.shard1_shape, by decide⟩

private theorem l2d_rms4846_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4846)
      (denoteGraphDistributed pm initPM 7955) (denoteGraphDistributed pm initPM 7956)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_carry7539_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4845
    (by native_decide) 4845 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4845
    (by native_decide) 4845 [1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4845).shape = [1024] := by rw [← hw]; exact hws
  have rs := l2d_rms sm initSM 120 0 7539 4845 4846 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_rms pm initPM 301 0 14805 4845 7955 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_rms pm initPM 302 1 14813 4845 7956 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw,
      fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega)
        h.shard0_shape h.shard1_shape, r0, r1]
  · rw [rs]; exact fw_rms_norm_shape2 _ _ 4096 1024 h.full_shape
  · rw [r0]; exact fw_rms_norm_shape2 _ _ 2048 1024 h.shard0_shape
  · rw [r1]; exact fw_rms_norm_shape2 _ _ 2048 1024 h.shard1_shape

/-- Distributed 2-TP reconstruction of layer-4 pre-attention RMSNorm 4846. -/
theorem recon_intermediateGoal_4846_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4846
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4846 4846 7955 7956
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_rms4846_rel initSM initPM hSM hPM hInit)

private theorem l2d_carry7548_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7548)
      (denoteGraphDistributed pm initPM 14822) (denoteGraphDistributed pm initPM 14835)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_rms4846_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 121
    { rank := 0, op := "OpName.FW_multiref", ins := [4846], outs := [7548, 7552, 7556], params := [3] }
    4846 7548 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' sm st 0 4846 7548 7552 7556)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 303
    { rank := 0, op := "OpName.FW_multiref", ins := [7955], outs := [14822, 14826, 14830], params := [3] }
    7955 14822 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' pm st 0 7955 14822 14826 14830)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 304
    { rank := 1, op := "OpName.FW_multiref", ins := [7956], outs := [14835, 14839, 14843], params := [3] }
    7956 14835 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' pm st 1 7956 14835 14839 14843)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  exact ⟨by rw [s, h.value, p0, p1], by rw [s]; exact h.full_shape,
    by rw [p0]; exact h.shard0_shape, by rw [p1]; exact h.shard1_shape, by decide⟩

private theorem l2d_carry7552_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7552)
      (denoteGraphDistributed pm initPM 14826) (denoteGraphDistributed pm initPM 14839)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_rms4846_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 121
    { rank := 0, op := "OpName.FW_multiref", ins := [4846], outs := [7548, 7552, 7556], params := [3] }
    4846 7552 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' sm st 0 4846 7548 7552 7556 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 303
    { rank := 0, op := "OpName.FW_multiref", ins := [7955], outs := [14822, 14826, 14830], params := [3] }
    7955 14826 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' pm st 0 7955 14822 14826 14830 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 304
    { rank := 1, op := "OpName.FW_multiref", ins := [7956], outs := [14835, 14839, 14843], params := [3] }
    7956 14839 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' pm st 1 7956 14835 14839 14843 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  exact ⟨by rw [s, h.value, p0, p1], by rw [s]; exact h.full_shape,
    by rw [p0]; exact h.shard0_shape, by rw [p1]; exact h.shard1_shape, by decide⟩

private theorem l2d_carry7556_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7556)
      (denoteGraphDistributed pm initPM 14830) (denoteGraphDistributed pm initPM 14843)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_rms4846_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 121
    { rank := 0, op := "OpName.FW_multiref", ins := [4846], outs := [7548, 7552, 7556], params := [3] }
    4846 7556 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' sm st 0 4846 7548 7552 7556 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 303
    { rank := 0, op := "OpName.FW_multiref", ins := [7955], outs := [14822, 14826, 14830], params := [3] }
    7955 14830 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' pm st 0 7955 14822 14826 14830 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 304
    { rank := 1, op := "OpName.FW_multiref", ins := [7956], outs := [14835, 14839, 14843], params := [3] }
    7956 14843 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' pm st 1 7956 14835 14839 14843 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  exact ⟨by rw [s, h.value, p0, p1], by rw [s]; exact h.full_shape,
    by rw [p0]; exact h.shard0_shape, by rw [p1]; exact h.shard1_shape, by decide⟩

private theorem l2d_q4848_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4848)
      (denoteGraphDistributed pm initPM 7957) (denoteGraphDistributed pm initPM 7958)
      [4096, 16, 64] [2048, 16, 64] := by
  have h := l2d_carry7548_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4847
    (by native_decide) 4847 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4847
    (by native_decide) 4847 [16, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4847).shape = [16, 64, 1024] := by rw [← hw]; exact hws
  have rs := l2d_per_head_linear sm initSM 122 0 7548 4847 4848 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_per_head_linear pm initPM 305 0 14822 4847 7957 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_per_head_linear pm initPM 308 1 14835 4847 7958 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 16 64
        (by omega) (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw,
      r0, r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 16 64 h.full_shape hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 h.shard0_shape hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 h.shard1_shape hpw

/-- Distributed 2-TP reconstruction of the layer-4 Q projection 4848. -/
theorem recon_intermediateGoal_4848_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4848
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4848 4848 7957 7958
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl
    (l2d_q4848_rel initSM initPM hSM hPM hInit)

private theorem l2d_k4850_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4850)
      (denoteGraphDistributed pm initPM 7969) (denoteGraphDistributed pm initPM 7970)
      [4096, 4, 64] [2048, 4, 64] := by
  have h := l2d_carry7552_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4849
    (by native_decide) 4849 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4849
    (by native_decide) 4849 [4, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4849).shape = [4, 64, 1024] := by rw [← hw]; exact hws
  have rs := l2d_per_head_linear sm initSM 123 0 7552 4849 4850 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_per_head_linear pm initPM 306 0 14826 4849 7969 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_per_head_linear pm initPM 309 1 14839 4849 7970 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw,
      r0, r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64 h.full_shape hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 h.shard0_shape hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 h.shard1_shape hpw

/-- Distributed 2-TP reconstruction of the layer-4 K projection 4850. -/
theorem recon_intermediateGoal_4850_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4850
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4850 4850 7969 7970
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l2d_k4850_rel initSM initPM hSM hPM hInit)

private theorem l2d_v4852_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4852)
      (denoteGraphDistributed pm initPM 7979) (denoteGraphDistributed pm initPM 7980)
      [4096, 4, 64] [2048, 4, 64] := by
  have h := l2d_carry7556_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4851
    (by native_decide) 4851 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4851
    (by native_decide) 4851 [4, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4851).shape = [4, 64, 1024] := by rw [← hw]; exact hws
  have rs := l2d_per_head_linear sm initSM 124 0 7556 4851 4852 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_per_head_linear pm initPM 307 0 14830 4851 7979 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_per_head_linear pm initPM 310 1 14843 4851 7980 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw,
      r0, r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64 h.full_shape hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 h.shard0_shape hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 h.shard1_shape hpw

/-- Distributed 2-TP reconstruction of the layer-4 V projection 4852. -/
theorem recon_intermediateGoal_4852_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4852
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4852 4852 7979 7980
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l2d_v4852_rel initSM initPM hSM hPM hInit)

/-- Distributed cache agreement for the fourth PM rotary-cache replica. -/
private theorem l2d_rotary_cache_11856 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraphDistributed sm initSM 4691 = denoteGraphDistributed pm initPM 11856 := by
  have hbase := distributed_init_singleton_value initSM initPM hInit initGoal_4691
    (by native_decide) 4691 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hcopy : denoteGraphDistributed pm initPM 11856 = id (denoteGraphDistributed pm initPM 4691) :=
    distributed_reduce1 pm initPM 14
      { rank := 1, op := "OpName.FW_multiref", ins := [4691],
        outs := (List.range 12).map (fun r => 11853 + r),
        params := [((List.range 12).map (fun r => 11853 + r)).length] }
      4691 11856 id (by native_decide) (by native_decide) (by decide)
      (fun s => by
        rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm s _ (by decide) (by decide)]
        rw [applyNode_fw_multiref_mem_out pm s 1 4691
          ((List.range 12).map (fun r => 11853 + r)) 11856 (by native_decide), id_eq])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  rw [hcopy, id_eq]
  exact hbase

set_option maxHeartbeats 8000000 in
private theorem l2d_rotary4854_4855_rels (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4854)
      (denoteGraphDistributed pm initPM 7991) (denoteGraphDistributed pm initPM 7992)
      [4096, 16, 64] [2048, 16, 64] ∧
    Gather2Rel (denoteGraphDistributed sm initSM 4855)
      (denoteGraphDistributed pm initPM 7993) (denoteGraphDistributed pm initPM 7994)
      [4096, 4, 64] [2048, 4, 64] := by
  have hq := l2d_q4848_rel initSM initPM hSM hPM hInit
  have hk := l2d_k4850_rel initSM initPM hSM hPM hInit
  have hcache := l2d_rotary_cache_11856 initSM initPM hInit
  have hpos := distributed_init_singleton_value initSM initPM hInit initGoal_4853
    (by native_decide) 4853 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hspos := distributed_init_singleton_shape initSM initPM hInit initGoal_4853
    (by native_decide) 4853 [4096] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have c0 := l2d_chunk pm initPM 3 0 4853 7989 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c1 := l2d_chunk pm initPM 16 1 4853 7990 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c0' : denoteGraphDistributed pm initPM 7989 = chunkPrimDimN 0 2 0 (denoteGraphDistributed pm initPM 4853) := c0
  have c1' : denoteGraphDistributed pm initPM 7990 = chunkPrimDimN 0 2 1 (denoteGraphDistributed pm initPM 4853) := c1
  have qSM : denoteGraphDistributed sm initSM 4854 =
      (fw_rotary_embedding (denoteGraphDistributed sm initSM 4691) (denoteGraphDistributed sm initSM 4853)
        (denoteGraphDistributed sm initSM 4848) (denoteGraphDistributed sm initSM 4850) 16 4).1 := by
    rw [distributed_node_core sm initSM 125
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4853, 4848, 4850], outs := [4854, 4855], params := [16, 4] }
      4854 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring sm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read sm initSM 125 4691 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 125 4853 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 125 4848 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 125 4850 (by native_decide) (by native_decide)]
  have kSM : denoteGraphDistributed sm initSM 4855 =
      (fw_rotary_embedding (denoteGraphDistributed sm initSM 4691) (denoteGraphDistributed sm initSM 4853)
        (denoteGraphDistributed sm initSM 4848) (denoteGraphDistributed sm initSM 4850) 16 4).2 := by
    rw [distributed_node_core sm initSM 125
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4853, 4848, 4850], outs := [4854, 4855], params := [16, 4] }
      4855 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring sm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 4691 4853 4848 4850 4854 4855 (by decide),
      distributed_prefix_read sm initSM 125 4691 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 125 4853 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 125 4848 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 125 4850 (by native_decide) (by native_decide)]
  have q0 : denoteGraphDistributed pm initPM 7991 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11856) (denoteGraphDistributed pm initPM 7989)
        (denoteGraphDistributed pm initPM 7957) (denoteGraphDistributed pm initPM 7969) 16 4).1 := by
    rw [distributed_node_core pm initPM 311
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11856, 7989, 7957, 7969], outs := [7991, 7993], params := [16, 4] }
      7991 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide), applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read pm initPM 311 11856 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 311 7989 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 311 7957 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 311 7969 (by native_decide) (by native_decide)]
  have k0 : denoteGraphDistributed pm initPM 7993 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11856) (denoteGraphDistributed pm initPM 7989)
        (denoteGraphDistributed pm initPM 7957) (denoteGraphDistributed pm initPM 7969) 16 4).2 := by
    rw [distributed_node_core pm initPM 311
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11856, 7989, 7957, 7969], outs := [7991, 7993], params := [16, 4] }
      7993 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11856 7989 7957 7969 7991 7993 (by decide),
      distributed_prefix_read pm initPM 311 11856 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 311 7989 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 311 7957 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 311 7969 (by native_decide) (by native_decide)]
  have q1 : denoteGraphDistributed pm initPM 7992 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11856) (denoteGraphDistributed pm initPM 7990)
        (denoteGraphDistributed pm initPM 7958) (denoteGraphDistributed pm initPM 7970) 16 4).1 := by
    rw [distributed_node_core pm initPM 312
      { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11856, 7990, 7958, 7970], outs := [7992, 7994], params := [16, 4] }
      7992 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide), applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read pm initPM 312 11856 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 312 7990 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 312 7958 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 312 7970 (by native_decide) (by native_decide)]
  have k1 : denoteGraphDistributed pm initPM 7994 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11856) (denoteGraphDistributed pm initPM 7990)
        (denoteGraphDistributed pm initPM 7958) (denoteGraphDistributed pm initPM 7970) 16 4).2 := by
    rw [distributed_node_core pm initPM 312
      { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11856, 7990, 7958, 7970], outs := [7992, 7994], params := [16, 4] }
      7994 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11856 7990 7958 7970 7992 7994 (by decide),
      distributed_prefix_read pm initPM 312 11856 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 312 7990 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 312 7958 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 312 7970 (by native_decide) (by native_decide)]
  have qval : denoteGraphDistributed sm initSM 4854 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 7991, denoteGraphDistributed pm initPM 7992] := by
    rw [qSM]; simp only [fw_rotary_embedding]
    rw [hq.value, fw_rotary_apply_allGather0_commute_2_1d (denoteGraphDistributed sm initSM 4691)
      (denoteGraphDistributed sm initSM 4853) (denoteGraphDistributed pm initPM 7957)
      (denoteGraphDistributed pm initPM 7958) 2048 16 64 (by omega) (by omega) (by omega)
      hspos hq.shard0_shape hq.shard1_shape, hcache, hpos, ← c0', ← c1', q0, q1]
    simp only [fw_rotary_embedding]
  have kval : denoteGraphDistributed sm initSM 4855 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 7993, denoteGraphDistributed pm initPM 7994] := by
    rw [kSM]; simp only [fw_rotary_embedding]
    rw [hk.value, fw_rotary_apply_allGather0_commute_2_1d (denoteGraphDistributed sm initSM 4691)
      (denoteGraphDistributed sm initSM 4853) (denoteGraphDistributed pm initPM 7969)
      (denoteGraphDistributed pm initPM 7970) 2048 4 64 (by omega) (by omega) (by omega)
      hspos hk.shard0_shape hk.shard1_shape, hcache, hpos, ← c0', ← c1', k0, k1]
    simp only [fw_rotary_embedding]
  have qs0 : (denoteGraphDistributed pm initPM 7991).shape = [2048, 16, 64] := by
    rw [q0]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hq.shard0_shape
  have qs1 : (denoteGraphDistributed pm initPM 7992).shape = [2048, 16, 64] := by
    rw [q1]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hq.shard1_shape
  have ks0 : (denoteGraphDistributed pm initPM 7993).shape = [2048, 4, 64] := by
    rw [k0]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hk.shard0_shape
  have ks1 : (denoteGraphDistributed pm initPM 7994).shape = [2048, 4, 64] := by
    rw [k1]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hk.shard1_shape
  refine ⟨⟨qval, ?_, qs0, qs1, by decide⟩, ⟨kval, ?_, ks0, ks1, by decide⟩⟩
  · rw [qval, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [qs0])]; rfl
  · rw [kval, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [ks0])]; rfl

/-- Distributed 2-TP reconstruction of the layer-4 rotary Q output. -/
theorem recon_intermediateGoal_4854_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4854
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4854 4854 7991 7992
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl
    (l2d_rotary4854_4855_rels initSM initPM hSM hPM hInit).1

/-- Distributed 2-TP reconstruction of the layer-4 rotary K output. -/
theorem recon_intermediateGoal_4855_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4855
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4855 4855 7993 7994
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l2d_rotary4854_4855_rels initSM initPM hSM hPM hInit).2

private def layer4SmSliding : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [4854, 4855, 4852, 4856, 4857], outs := [4858],
    params := [16, 4, 64, 64, 1, 512] }
private def layer4PmSliding0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [7991, 7993, 7979, 4856, 4857], outs := [7995],
    params := [16, 4, 64, 64, 1, 512] }
private def layer4PmSliding1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window",
    ins := [7992, 7994, 7980, 4856, 4857], outs := [7996],
    params := [16, 4, 64, 64, 1, 512] }

-- Keep graph and replica-order certificates separate from the tensor proof.
set_option maxRecDepth 1000000 in
private theorem layer4_sm_node126 : sm.nodes[126]'(by native_decide) = layer4SmSliding := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer4_pm_node313 : pm.nodes[313]'(by native_decide) = layer4PmSliding0 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer4_pm_node314 : pm.nodes[314]'(by native_decide) = layer4PmSliding1 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer4_sm_buddy_sliding :
    ringAttnBuddies sm layer4SmSliding = [layer4SmSliding] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer4_pm_buddy_sliding0 :
    ringAttnBuddies pm layer4PmSliding0 = [layer4PmSliding0, layer4PmSliding1] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer4_pm_buddy_sliding1 :
    ringAttnBuddies pm layer4PmSliding1 = [layer4PmSliding0, layer4PmSliding1] := by native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
/-- Pure-distributed 2-TP reconstruction of the layer-4 sliding-attention output. -/
theorem recon_intermediateGoal_4858_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4858
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have gq := recon_intermediateGoal_4854_distributed initSM initPM hSM hPM hInit
  have gk := recon_intermediateGoal_4855_distributed initSM initPM hSM hPM hInit
  have gv := recon_intermediateGoal_4852_distributed initSM initPM hSM hPM hInit
  have gqshape : (denoteGraphDistributed sm initSM 4854).shape = [4096, 16, 64] := by
    simpa only [intermediateGoal_4854] using gq.1
  have gkshape : (denoteGraphDistributed sm initSM 4855).shape = [4096, 4, 64] := by
    simpa only [intermediateGoal_4855] using gk.1
  have gvshape : (denoteGraphDistributed sm initSM 4852).shape = [4096, 4, 64] := by
    simpa only [intermediateGoal_4852] using gv.1
  have q := (l2d_rotary4854_4855_rels initSM initPM hSM hPM hInit).1
  have k := (l2d_rotary4854_4855_rels initSM initPM hSM hPM hInit).2
  have v := l2d_v4852_rel initSM initPM hSM hPM hInit
  have hcu4856 := distributed_init_singleton_value initSM initPM hInit initGoal_4856
    (by native_decide) 4856 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hcu4857 := distributed_init_singleton_value initSM initPM hInit initGoal_4857
    (by native_decide) 4857 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  let fs := (sm.nodes.take 126).foldl (applyNodeDistributed sm) initSM
  let fp := (pm.nodes.take 313).foldl (applyNodeDistributed pm) initPM
  let fp' := (pm.nodes.take 314).foldl (applyNodeDistributed pm) initPM
  have bs (t : Tid) (hn : ∀ n ∈ sm.nodes.drop 126, n.outs ≠ [])
      (hw : ∀ n ∈ sm.nodes.drop 126, t ∉ n.outs) : fs t = denoteGraphDistributed sm initSM t :=
    distributed_prefix_read sm initSM 126 t hn hw
  have bp (t : Tid) (hn : ∀ n ∈ pm.nodes.drop 313, n.outs ≠ [])
      (hw : ∀ n ∈ pm.nodes.drop 313, t ∉ n.outs) : fp t = denoteGraphDistributed pm initPM t :=
    distributed_prefix_read pm initPM 313 t hn hw
  have hqfull : fs 4854 = allGatherPrimDimN 0 2 0 [fp 7991, fp 7992] := by
    rw [bs 4854 (by native_decide) (by native_decide),
      bp 7991 (by native_decide) (by native_decide),
      bp 7992 (by native_decide) (by native_decide)]
    exact q.value
  have hkfull : fs 4855 = allGatherPrimDimN 0 2 0 [fp 7993, fp 7994] := by
    rw [bs 4855 (by native_decide) (by native_decide),
      bp 7993 (by native_decide) (by native_decide),
      bp 7994 (by native_decide) (by native_decide)]
    exact k.value
  have hvfull : fs 4852 = allGatherPrimDimN 0 2 0 [fp 7979, fp 7980] := by
    rw [bs 4852 (by native_decide) (by native_decide),
      bp 7979 (by native_decide) (by native_decide),
      bp 7980 (by native_decide) (by native_decide)]
    exact v.value
  have hqpos : 0 < (fs (layer4SmSliding.ins.getD 0 0)).shape.length := by
    show 0 < (fs 4854).shape.length
    rw [bs 4854 (by native_decide) (by native_decide), gqshape]
    decide
  have hkpos : 0 < (fs (layer4SmSliding.ins.getD 1 0)).shape.length := by
    show 0 < (fs 4855).shape.length
    rw [bs 4855 (by native_decide) (by native_decide), gkshape]
    decide
  have hvpos : 0 < (fs (layer4SmSliding.ins.getD 2 0)).shape.length := by
    show 0 < (fs 4852).shape.length
    rw [bs 4852 (by native_decide) (by native_decide), gvshape]
    decide
  have hcuQ : fs 4856 = fp 4856 := by
    rw [bs 4856 (by native_decide) (by native_decide),
      bp 4856 (by native_decide) (by native_decide), hcu4856]
  have hcuK : fs 4857 = fp 4857 := by
    rw [bs 4857 (by native_decide) (by native_decide),
      bp 4857 (by native_decide) (by native_decide), hcu4857]
  have e7991 : fp 7991 = fp' 7991 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 7991 313 314
      (by omega) (by native_decide) (by native_decide)).symm
  have e7992 : fp 7992 = fp' 7992 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 7992 313 314
      (by omega) (by native_decide) (by native_decide)).symm
  have e7993 : fp 7993 = fp' 7993 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 7993 313 314
      (by omega) (by native_decide) (by native_decide)).symm
  have e7994 : fp 7994 = fp' 7994 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 7994 313 314
      (by omega) (by native_decide) (by native_decide)).symm
  have e7979 : fp 7979 = fp' 7979 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 7979 313 314
      (by omega) (by native_decide) (by native_decide)).symm
  have e7980 : fp 7980 = fp' 7980 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 7980 313 314
      (by omega) (by native_decide) (by native_decide)).symm
  have e4856 : fp 4856 = fp' 4856 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 4856 313 314
      (by omega) (by native_decide) (by native_decide)).symm
  have e4857 : fp 4857 = fp' 4857 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 4857 313 314
      (by omega) (by native_decide) (by native_decide)).symm
  have bridge : applyNodeRingAttn_sliding_window pm fp layer4PmSliding1 =
      applyNodeRingAttn_sliding_window pm fp' layer4PmSliding1 := by
    apply attn_sw_store_congr
    · rw [layer4_pm_buddy_sliding1]; intro m hm; fin_cases hm
      · exact e7991
      · exact e7992
    · rw [layer4_pm_buddy_sliding1]; intro m hm; fin_cases hm
      · exact e7993
      · exact e7994
    · rw [layer4_pm_buddy_sliding1]; intro m hm; fin_cases hm
      · exact e7979
      · exact e7980
    · exact e4856
    · exact e4857
  have rSM : denoteGraphDistributed sm initSM 4858 =
      applyNodeRingAttn_sliding_window sm fs layer4SmSliding := by
    rw [distributed_node_core sm initSM 126 layer4SmSliding 4858 (by native_decide)
      layer4_sm_node126 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out sm _ 0 4854 4855 4852 4856 4857 4858
      [16, 4, 64, 64, 1, 512]
  have rP0 : denoteGraphDistributed pm initPM 7995 =
      applyNodeRingAttn_sliding_window pm fp layer4PmSliding0 := by
    rw [distributed_node_core pm initPM 313 layer4PmSliding0 7995 (by native_decide)
      layer4_pm_node313 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out pm _ 0 7991 7993 7979 4856 4857 7995
      [16, 4, 64, 64, 1, 512]
  have rP1 : denoteGraphDistributed pm initPM 7996 =
      applyNodeRingAttn_sliding_window pm fp' layer4PmSliding1 := by
    rw [distributed_node_core pm initPM 314 layer4PmSliding1 7996 (by native_decide)
      layer4_pm_node314 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out pm _ 1 7992 7994 7980 4856 4857 7996
      [16, 4, 64, 64, 1, 512]
  have hfull : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 7991, fp 7992])
      (allGatherPrimDimN 0 2 0 [fp 7993, fp 7994])
      (allGatherPrimDimN 0 2 0 [fp 7979, fp 7980])
      (fp 4856) (fp 4857) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3, ← hqfull,
      bs 4854 (by native_decide) (by native_decide), gqshape]
    rfl
  have hfull' : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 7991, fp' 7992])
      (allGatherPrimDimN 0 2 0 [fp' 7993, fp' 7994])
      (allGatherPrimDimN 0 2 0 [fp' 7979, fp' 7980])
      (fp' 4856) (fp' 4857) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [← e7991, ← e7992, ← e7993, ← e7994, ← e7979, ← e7980,
      ← e4856, ← e4857]
    exact hfull
  exact recon_attn_sliding_window_2tp_distributed initSM initPM intermediateGoal_4858
    layer4SmSliding layer4PmSliding0 layer4PmSliding1 fs fp fp' 4858 7995 7996
    2048 16 64 (by omega) (by omega) (by omega) rSM rP0 rP1 bridge
    layer4_sm_buddy_sliding layer4_pm_buddy_sliding0 layer4_pm_buddy_sliding1
    (by native_decide) (by native_decide) hqpos hkpos hvpos hqfull hkfull hvfull
    hcuQ hcuK rfl rfl rfl rfl hfull hfull' rfl rfl rfl rfl rfl rfl

/-! ### Layer-4 post-attention residual cascade (pure distributed evaluator) -/

private theorem l2d_reshape4859_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4859)
      (denoteGraphDistributed pm initPM 7997) (denoteGraphDistributed pm initPM 7998)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_4858 4858 7995 7996
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4858_distributed initSM initPM hSM hPM hInit)
  have rs := l2d_reshape sm initSM 127 0 4858 4859 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l2d_reshape pm initPM 315 0 7995 7997 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l2d_reshape pm initPM 316 1 7996 7998 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine ⟨?_, by rw [rs]; rfl, by rw [r0]; rfl, by rw [r1]; rfl, by decide⟩
  rw [rs, h.value, r0, r1]
  exact fw_view_allGather0_reshape_16_64_2_g12 _ _ h.shard0_shape h.shard1_shape

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 attention reshape. -/
theorem recon_intermediateGoal_4859_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4859
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4859 4859 7997 7998
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_reshape4859_rel initSM initPM hSM hPM hInit)

private theorem l2d_reshape4860_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4860)
      (denoteGraphDistributed pm initPM 8003) (denoteGraphDistributed pm initPM 8004)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_reshape4859_rel initSM initPM hSM hPM hInit
  have rs := l2d_reshape sm initSM 128 0 4859 4860 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l2d_reshape pm initPM 317 0 7997 8003 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l2d_reshape pm initPM 318 1 7998 8004 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 4860 = denoteGraphDistributed sm initSM 4859 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 8003 = denoteGraphDistributed pm initPM 7997 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 8004 = denoteGraphDistributed pm initPM 7998 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, e0, e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 identity reshape. -/
theorem recon_intermediateGoal_4860_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4860
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4860 4860 8003 8004
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_reshape4860_rel initSM initPM hSM hPM hInit)

private theorem l2d_linear4862_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4862)
      (denoteGraphDistributed pm initPM 8007) (denoteGraphDistributed pm initPM 8008)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_reshape4860_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4861
    (by native_decide) 4861 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4861
    (by native_decide) 4861 [1024, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4861).shape = [1024, 1024] := by
    rw [← hw]; exact hws
  have rs := l2d_linear sm initSM 129 0 4860 4861 4862 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_linear pm initPM 319 0 8003 4861 8007 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_linear pm initPM 320 1 8004 4861 8008 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw,
      fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
        (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 1024 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 1024 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 1024 _ _ h.shard1_shape hpw

/-- Pure-distributed exact 2-TP reconstruction of the replicated-weight layer-4 linear. -/
theorem recon_intermediateGoal_4862_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4862
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4862 4862 8007 8008
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_linear4862_rel initSM initPM hSM hPM hInit)

private theorem l2d_view4863_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4863)
      (denoteGraphDistributed pm initPM 8017) (denoteGraphDistributed pm initPM 8018)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_linear4862_rel initSM initPM hSM hPM hInit
  have rs := l2d_view sm initSM 130 0 4862 4863 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l2d_view pm initPM 321 0 8007 8017 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l2d_view pm initPM 322 1 8008 8018 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 4863 = denoteGraphDistributed sm initSM 4862 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 8017 = denoteGraphDistributed pm initPM 8007 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 8018 = denoteGraphDistributed pm initPM 8008 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, e0, e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 identity view. -/
theorem recon_intermediateGoal_4863_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4863
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4863 4863 8017 8018
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_view4863_rel initSM initPM hSM hPM hInit)

private theorem l2d_float4864_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4864)
      (denoteGraphDistributed pm initPM 8021) (denoteGraphDistributed pm initPM 8022)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_view4863_rel initSM initPM hSM hPM hInit
  have rs := l2d_float sm initSM 131 0 4863 4864 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_float pm initPM 323 0 8017 8021 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_float pm initPM 324 1 8018 8022 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  exact ⟨by rw [rs, h.value, r0, r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 float node. -/
theorem recon_intermediateGoal_4864_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4864
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4864 4864 8021 8022
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_float4864_rel initSM initPM hSM hPM hInit)

private theorem l2d_carry7543_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7543)
      (denoteGraphDistributed pm initPM 14809) (denoteGraphDistributed pm initPM 14817)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_add4844_rel initSM initPM hSM hPM hInit
  have rs := distributed_reduce1 sm initSM 119
    { rank := 0, op := "OpName.FW_multiref", ins := [4844], outs := [7539, 7543], params := [2] }
    4844 7543 id (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_fw_multiref2_second_out' sm s 0 4844 7539 7543 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce1 pm initPM 299
    { rank := 0, op := "OpName.FW_multiref", ins := [7951], outs := [14805, 14809], params := [2] }
    7951 14809 id (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_fw_multiref2_second_out' pm s 0 7951 14805 14809 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce1 pm initPM 300
    { rank := 1, op := "OpName.FW_multiref", ins := [7952], outs := [14813, 14817], params := [2] }
    7952 14817 id (by native_decide) (by native_decide) (by decide)
    (fun s => applyNode_fw_multiref2_second_out' pm s 1 7952 14813 14817 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rs r0 r1
  exact ⟨by rw [rs, h.value, r0, r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 residual carry. -/
theorem recon_intermediateGoal_7543_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7543
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_7543 7543 14809 14817
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_carry7543_rel initSM initPM hSM hPM hInit)

private theorem l2d_add4865_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4865)
      (denoteGraphDistributed pm initPM 8025) (denoteGraphDistributed pm initPM 8026)
      [4096, 1024] [2048, 1024] := by
  have ha := l2d_carry7543_rel initSM initPM hSM hPM hInit
  have hb := l2d_float4864_rel initSM initPM hSM hPM hInit
  have rs := l2d_add sm initSM 132 0 7543 4864 4865 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_add pm initPM 325 0 14809 8021 8025 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_add pm initPM 326 1 14817 8022 8026 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, ha.value, hb.value,
      fw_add_allGather0_commute_2_2048_1024 _ _ _ _ ha.shard0_shape ha.shard1_shape
        hb.shard0_shape hb.shard1_shape, r0, r1]
  · rw [rs]; exact elemwiseAdd_shape_of_shapes _ _ [4096, 1024] ha.full_shape hb.full_shape
  · rw [r0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] ha.shard0_shape hb.shard0_shape
  · rw [r1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] ha.shard1_shape hb.shard1_shape

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 residual add. -/
theorem recon_intermediateGoal_4865_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4865
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4865 4865 8025 8026
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_add4865_rel initSM initPM hSM hPM hInit)

/-! ### Layer-4 router entrance (pure distributed evaluator) -/

private theorem l2d_rms4867_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4867)
      (denoteGraphDistributed pm initPM 8029) (denoteGraphDistributed pm initPM 8030)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_add4865_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 133
    { rank := 0, op := "OpName.FW_multiref", ins := [4865], outs := [7560, 7564], params := [2] }
    4865 7560 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out sm st 0 4865 7560 7564)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 327
    { rank := 0, op := "OpName.FW_multiref", ins := [8025], outs := [14847, 14851], params := [2] }
    8025 14847 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 0 8025 14847 14851)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 328
    { rank := 1, op := "OpName.FW_multiref", ins := [8026], outs := [14855, 14859], params := [2] }
    8026 14855 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 1 8026 14855 14859)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4866
    (by native_decide) 4866 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have rs := l2d_rms sm initSM 134 0 7560 4866 4867 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_rms pm initPM 329 0 14847 4866 8029 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_rms pm initPM 330 1 14855 4866 8030 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 14847).shape = [2048, 1024] := by
    rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 14855).shape = [2048, 1024] := by
    rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs0 hs1,
      r0, r1]
  · rw [rs]; exact fw_rms_norm_shape2 _ _ 4096 1024 (by rw [s]; exact h.full_shape)
  · rw [r0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs0
  · rw [r1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs1

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 router RMSNorm. -/
theorem recon_intermediateGoal_4867_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4867
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4867 4867 8029 8030
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_rms4867_rel initSM initPM hSM hPM hInit)

private theorem l2d_float4868_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4868)
      (denoteGraphDistributed pm initPM 8031) (denoteGraphDistributed pm initPM 8032)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_rms4867_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 135
    { rank := 0, op := "OpName.FW_multiref", ins := [4867],
      outs := [7571, 7575, 7579, 7583, 7587], params := [5] }
    4867 7571 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref_first_out' sm st 0 4 4867 7571 [7575, 7579, 7583, 7587])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 331
    { rank := 0, op := "OpName.FW_multiref", ins := [8029],
      outs := [14866, 14870, 14874, 14878, 14882], params := [5] }
    8029 14866 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref_first_out' pm st 0 4 8029 14866 [14870, 14874, 14878, 14882])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 332
    { rank := 1, op := "OpName.FW_multiref", ins := [8030],
      outs := [14889, 14893, 14897, 14901, 14905], params := [5] }
    8030 14889 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref_first_out' pm st 1 4 8030 14889 [14893, 14897, 14901, 14905])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have rs := l2d_float sm initSM 136 0 7571 4868 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_float pm initPM 333 0 14866 8031 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_float pm initPM 337 1 14889 8032 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  exact ⟨by rw [rs, s, h.value, ← p0, ← p1, r0, r1],
    by rw [rs, s]; exact h.full_shape, by rw [r0, p0]; exact h.shard0_shape,
    by rw [r1, p1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 router float. -/
theorem recon_intermediateGoal_4868_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4868
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4868 4868 8031 8032
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_float4868_rel initSM initPM hSM hPM hInit)

private theorem l2d_logits4870_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4870)
      (denoteGraphDistributed pm initPM 8037) (denoteGraphDistributed pm initPM 8038)
      [4096, 64] [2048, 64] := by
  have h := l2d_float4868_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4869
    (by native_decide) 4869 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4869
    (by native_decide) 4869 [64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4869).shape = [64, 1024] := by
    rw [← hw]; exact hws
  have rs := distributed_reduce2 sm initSM 140
    { rank := 0, op := "OpName.FW_norm_linear", ins := [4868, 4869], outs := [4870] }
    4868 4869 4870 fw_norm_linear (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_norm_linear_out sm st 0 4868 4869 4870)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce2 pm initPM 341
    { rank := 0, op := "OpName.FW_norm_linear", ins := [8031, 4869], outs := [8037] }
    8031 4869 8037 fw_norm_linear (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_norm_linear_out pm st 0 8031 4869 8037)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce2 pm initPM 345
    { rank := 1, op := "OpName.FW_norm_linear", ins := [8032, 4869], outs := [8038] }
    8032 4869 8038 fw_norm_linear (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_norm_linear_out pm st 1 8032 4869 8038)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw,
      fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64
        (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw,
      r0, r1]
  · rw [rs]; exact fw_norm_linear_2d_shape 4096 1024 64 _ _ (by decide) h.full_shape hws
  · rw [r0]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) h.shard0_shape hpw
  · rw [r1]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) h.shard1_shape hpw

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 router logits. -/
theorem recon_intermediateGoal_4870_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4870
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4870 4870 8037 8038
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl
    (l2d_logits4870_rel initSM initPM hSM hPM hInit)

private theorem l2d_topk4871_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4871)
      (denoteGraphDistributed pm initPM 8039) (denoteGraphDistributed pm initPM 8040)
      [4096, 64] [2048, 64] := by
  have h := l2d_logits4870_rel initSM initPM hSM hPM hInit
  let ss := (sm.nodes.take 144).foldl (applyNodeDistributed sm) initSM
  let p0s := (pm.nodes.take 349).foldl (applyNodeDistributed pm) initPM
  let p1s := (pm.nodes.take 353).foldl (applyNodeDistributed pm) initPM
  have es : ss 4870 = denoteGraphDistributed sm initSM 4870 :=
    foldl_take_distributed_eq sm initSM 4870 144 (by native_decide) (by native_decide)
  have e0 : p0s 8037 = denoteGraphDistributed pm initPM 8037 :=
    foldl_take_distributed_eq pm initPM 8037 349 (by native_decide) (by native_decide)
  have e1 : p1s 8038 = denoteGraphDistributed pm initPM 8038 :=
    foldl_take_distributed_eq pm initPM 8038 353 (by native_decide) (by native_decide)
  have hs : (ss 4870).shape.reverse.head? = some 64 := by rw [es, h.full_shape]; rfl
  have h0 : (p0s 8037).shape.reverse.head? = some 64 := by rw [e0, h.shard0_shape]; rfl
  have h1 : (p1s 8038).shape.reverse.head? = some 64 := by rw [e1, h.shard1_shape]; rfl
  have rs := distributed_reduce_fixed_one sm initSM 144
    { rank := 0, op := "OpName.FW_topk_routing", ins := [4870], outs := [4871, 4872, 4873], params := [8, 1] }
    4870 4871 (fun t => (fw_topk_routing t 8 64).1)
    (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_fst sm ss 0 4870 4871 4872 4873 hs)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce_fixed_one pm initPM 349
    { rank := 0, op := "OpName.FW_topk_routing", ins := [8037], outs := [8039, 8041, 8043], params := [8, 1] }
    8037 8039 (fun t => (fw_topk_routing t 8 64).1)
    (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_fst pm p0s 0 8037 8039 8041 8043 h0)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce_fixed_one pm initPM 353
    { rank := 1, op := "OpName.FW_topk_routing", ins := [8038], outs := [8040, 8042, 8044], params := [8, 1] }
    8038 8040 (fun t => (fw_topk_routing t 8 64).1)
    (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_fst pm p1s 1 8038 8040 8042 8044 h1)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value,
      fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64
        (by omega) (by omega) h.shard0_shape h.shard1_shape, r0, r1]
  · rw [rs]; exact fw_topk_routing_fst_shape _ 8 64 4096 (by rw [h.full_shape]; rfl)
  · rw [r0]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h.shard0_shape]; rfl)
  · rw [r1]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h.shard1_shape]; rfl)

/-- Pure-distributed exact 2-TP reconstruction of layer-4 routing probabilities. -/
theorem recon_intermediateGoal_4871_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4871
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4871 4871 8039 8040
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl
    (l2d_topk4871_rel initSM initPM hSM hPM hInit)

private theorem l2d_topk4872_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4872)
      (denoteGraphDistributed pm initPM 8041) (denoteGraphDistributed pm initPM 8042)
      [4096, 64] [2048, 64] := by
  have h := l2d_logits4870_rel initSM initPM hSM hPM hInit
  let ss := (sm.nodes.take 144).foldl (applyNodeDistributed sm) initSM
  let p0s := (pm.nodes.take 349).foldl (applyNodeDistributed pm) initPM
  let p1s := (pm.nodes.take 353).foldl (applyNodeDistributed pm) initPM
  have es : ss 4870 = denoteGraphDistributed sm initSM 4870 :=
    foldl_take_distributed_eq sm initSM 4870 144 (by native_decide) (by native_decide)
  have e0 : p0s 8037 = denoteGraphDistributed pm initPM 8037 :=
    foldl_take_distributed_eq pm initPM 8037 349 (by native_decide) (by native_decide)
  have e1 : p1s 8038 = denoteGraphDistributed pm initPM 8038 :=
    foldl_take_distributed_eq pm initPM 8038 353 (by native_decide) (by native_decide)
  have hs : (ss 4870).shape.reverse.head? = some 64 := by rw [es, h.full_shape]; rfl
  have h0 : (p0s 8037).shape.reverse.head? = some 64 := by rw [e0, h.shard0_shape]; rfl
  have h1 : (p1s 8038).shape.reverse.head? = some 64 := by rw [e1, h.shard1_shape]; rfl
  have rs := distributed_reduce_fixed_one sm initSM 144
    { rank := 0, op := "OpName.FW_topk_routing", ins := [4870], outs := [4871, 4872, 4873], params := [8, 1] }
    4870 4872 (fun t => (fw_topk_routing t 8 64).2.1)
    (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_snd sm ss 0 4870 4871 4872 4873 (by decide) hs)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce_fixed_one pm initPM 349
    { rank := 0, op := "OpName.FW_topk_routing", ins := [8037], outs := [8039, 8041, 8043], params := [8, 1] }
    8037 8041 (fun t => (fw_topk_routing t 8 64).2.1)
    (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_snd pm p0s 0 8037 8039 8041 8043 (by decide) h0)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce_fixed_one pm initPM 353
    { rank := 1, op := "OpName.FW_topk_routing", ins := [8038], outs := [8040, 8042, 8044], params := [8, 1] }
    8038 8042 (fun t => (fw_topk_routing t 8 64).2.1)
    (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_snd pm p1s 1 8038 8040 8042 8044 (by decide) h1)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value,
      fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 8 64
        (by omega) (by omega) h.shard0_shape h.shard1_shape, r0, r1]
  · rw [rs]; exact fw_topk_routing_snd_shape _ 8 64 4096 (by rw [h.full_shape]; rfl)
  · rw [r0]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [h.shard0_shape]; rfl)
  · rw [r1]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [h.shard1_shape]; rfl)

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 routing map. -/
theorem recon_intermediateGoal_4872_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4872
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4872 4872 8041 8042
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl
    (l2d_topk4872_rel initSM initPM hSM hPM hInit)

private theorem l2d_token7575_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7575)
      (denoteGraphDistributed pm initPM 14870) (denoteGraphDistributed pm initPM 14893)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_rms4867_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 135
    { rank := 0, op := "OpName.FW_multiref", ins := [4867],
      outs := [7571, 7575, 7579, 7583, 7587], params := [5] }
    4867 7575 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos1_out sm st 0 4867 7571 7575 7579 7583 7587
      (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 331
    { rank := 0, op := "OpName.FW_multiref", ins := [8029],
      outs := [14866, 14870, 14874, 14878, 14882], params := [5] }
    8029 14870 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos1_out pm st 0 8029 14866 14870 14874 14878 14882
      (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 332
    { rank := 1, op := "OpName.FW_multiref", ins := [8030],
      outs := [14889, 14893, 14897, 14901, 14905], params := [5] }
    8030 14893 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos1_out pm st 1 8030 14889 14893 14897 14901 14905
      (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  exact ⟨by rw [s, h.value, ← p0, ← p1], by rw [s]; exact h.full_shape,
    by rw [p0]; exact h.shard0_shape, by rw [p1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 MoE token input. -/
theorem recon_intermediateGoal_7575_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7575
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_7575 7575 14870 14893
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_token7575_rel initSM initPM hSM hPM hInit)

private def layer4SmMoe : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [7575, 4871, 4872, 4874, 4875], outs := [4876], params := [64, 0, 64, 8] }
private def layer4PmMoe0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [14870, 8039, 8041, 8045, 8047], outs := [8049], params := [64, 0, 32, 8] }
private def layer4PmMoe1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm",
    ins := [14893, 8040, 8042, 8046, 8048], outs := [8050], params := [64, 32, 64, 8] }

set_option maxRecDepth 1000000 in
private theorem layer4_sm_node148 : sm.nodes[148]'(by native_decide) = layer4SmMoe := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer4_pm_node357 : pm.nodes[357]'(by native_decide) = layer4PmMoe0 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer4_pm_node360 : pm.nodes[360]'(by native_decide) = layer4PmMoe1 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer4_sm_buddies : sm.replicaBuddies layer4SmMoe = [layer4SmMoe] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer4_pm_buddies0 :
    pm.replicaBuddies layer4PmMoe0 = [layer4PmMoe0, layer4PmMoe1] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer4_pm_buddies1 :
    pm.replicaBuddies layer4PmMoe1 = [layer4PmMoe0, layer4PmMoe1] := by native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
/-- Pure-distributed full-expert reconstruction of the layer-4 MoE boundary. -/
theorem recon_intermediateGoal_4876_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4876
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have hi := l2d_token7575_rel initSM initPM hSM hPM hInit
  have hrp := l2d_topk4871_rel initSM initPM hSM hPM hInit
  have hrm := l2d_topk4872_rel initSM initPM hSM hPM hInit

  have hW13 := hInit initGoal_4874 (by native_decide)
  have hW2 := hInit initGoal_4875 (by native_decide)
  have hsW13 := hW13.2.1
  have hsW2 := hW2.2.1
  simp only [initGoal_4874, List.map, List.cons.injEq, and_true] at hsW13
  simp only [initGoal_4875, List.map, List.cons.injEq, and_true] at hsW2
  have hsW13A : (denoteGraphDistributed pm initPM 8045).shape = [32, 1024, 1024] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8045
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW13.1
  have hsW13B : (denoteGraphDistributed pm initPM 8046).shape = [32, 1024, 1024] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8046
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW13.2
  have hsW2A : (denoteGraphDistributed pm initPM 8047).shape = [32, 1024, 512] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8047
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW2.1
  have hsW2B : (denoteGraphDistributed pm initPM 8048).shape = [32, 1024, 512] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8048
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW2.2
  have hbrW13 : denoteGraphDistributed sm initSM 4874 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 8045, denoteGraphDistributed pm initPM 8046] := by
    have hv := hW13.2.2
    rw [reconstructForGoal_of_not_replicated initGoal_4874 pm.numRanks _ rfl] at hv
    simp only [initGoal_4874, List.map] at hv
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
      (by rw [hsW13.1]; decide)] at hv
    have ds : denoteGraphDistributed sm initSM 4874 = initSM 4874 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written sm sm.nodes initSM 4874
        layer1_sm_nodes_nonempty (by native_decide)
    have dp0 : denoteGraphDistributed pm initPM 8045 = initPM 8045 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8045
        layer1_pm_nodes_nonempty (by native_decide)
    have dp1 : denoteGraphDistributed pm initPM 8046 = initPM 8046 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8046
        layer1_pm_nodes_nonempty (by native_decide)
    rw [ds, dp0, dp1]
    exact hv
  have hbrW2 : denoteGraphDistributed sm initSM 4875 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 8047, denoteGraphDistributed pm initPM 8048] := by
    have hv := hW2.2.2
    rw [reconstructForGoal_of_not_replicated initGoal_4875 pm.numRanks _ rfl] at hv
    simp only [initGoal_4875, List.map] at hv
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
      (by rw [hsW2.1]; decide)] at hv
    have ds : denoteGraphDistributed sm initSM 4875 = initSM 4875 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written sm sm.nodes initSM 4875
        layer1_sm_nodes_nonempty (by native_decide)
    have dp0 : denoteGraphDistributed pm initPM 8047 = initPM 8047 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8047
        layer1_pm_nodes_nonempty (by native_decide)
    have dp1 : denoteGraphDistributed pm initPM 8048 = initPM 8048 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8048
        layer1_pm_nodes_nonempty (by native_decide)
    rw [ds, dp0, dp1]
    exact hv
  have hW13single : allGatherPrimDimN 0 1 0 [denoteGraphDistributed sm initSM 4874] =
      denoteGraphDistributed sm initSM 4874 := by
    have hs : (denoteGraphDistributed sm initSM 4874).shape = [64, 1024, 1024] := by
      rw [hbrW13, allGatherPrimDimN_shape 0 2 _ [32, 1024, 1024] (by simp [hsW13A])]
      simp [List.set]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hs]; decide)
  have hW2single : allGatherPrimDimN 0 1 0 [denoteGraphDistributed sm initSM 4875] =
      denoteGraphDistributed sm initSM 4875 := by
    have hs : (denoteGraphDistributed sm initSM 4875).shape = [64, 1024, 512] := by
      rw [hbrW2, allGatherPrimDimN_shape 0 2 _ [32, 1024, 512] (by simp [hsW2A])]
      simp [List.set]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hs]; decide)

  have hSMout : denoteGraphDistributed sm initSM 4876 =
      fw_all2all_moe_gmm_full (denoteGraphDistributed sm initSM 7575)
        (denoteGraphDistributed sm initSM 4871) (denoteGraphDistributed sm initSM 4872)
        [denoteGraphDistributed pm initPM 8045, denoteGraphDistributed pm initPM 8046]
        [denoteGraphDistributed pm initPM 8047, denoteGraphDistributed pm initPM 8048]
        64 8 (((10 : Nat) : Scalar)) := by
    have hk : 148 < sm.nodes.length := by native_decide
    rw [distributed_moe_reduce sm initSM 148 layer4SmMoe 4876 hk
      (show sm.nodes[148]'hk = layer4SmMoe from layer4_sm_node148)
      rfl rfl (by native_decide) (by native_decide)]
    unfold applyNodeFullExpertMoE_value
    rw [layer4_sm_buddies]
    simp only [layer4SmMoe, List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    rw [foldl_take_distributed_eq sm initSM 7575 148 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 4871 148 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 4872 148 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 4874 148 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 4875 148 (by native_decide) (by native_decide)]
    unfold fw_all2all_moe_gmm_full
    simp only [List.length_cons, List.length_nil]
    rw [hW13single, hW2single, hbrW13, hbrW2]
  have hP0 : denoteGraphDistributed pm initPM 8049 =
      fw_all2all_moe_gmm_full (denoteGraphDistributed pm initPM 14870)
        (denoteGraphDistributed pm initPM 8039) (denoteGraphDistributed pm initPM 8041)
        [denoteGraphDistributed pm initPM 8045, denoteGraphDistributed pm initPM 8046]
        [denoteGraphDistributed pm initPM 8047, denoteGraphDistributed pm initPM 8048]
        64 8 (((10 : Nat) : Scalar)) := by
    have hk : 357 < pm.nodes.length := by native_decide
    rw [distributed_moe_reduce pm initPM 357 layer4PmMoe0 8049 hk
      (show pm.nodes[357]'hk = layer4PmMoe0 from layer4_pm_node357)
      rfl rfl (by native_decide) (by native_decide)]
    unfold applyNodeFullExpertMoE_value
    rw [layer4_pm_buddies0]
    simp only [layer4PmMoe0, layer4PmMoe1, List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    rw [foldl_take_distributed_eq pm initPM 14870 357 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8039 357 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8041 357 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8045 357 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8046 357 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8047 357 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8048 357 (by native_decide) (by native_decide)]
  have hP1 : denoteGraphDistributed pm initPM 8050 =
      fw_all2all_moe_gmm_full (denoteGraphDistributed pm initPM 14893)
        (denoteGraphDistributed pm initPM 8040) (denoteGraphDistributed pm initPM 8042)
        [denoteGraphDistributed pm initPM 8045, denoteGraphDistributed pm initPM 8046]
        [denoteGraphDistributed pm initPM 8047, denoteGraphDistributed pm initPM 8048]
        64 8 (((10 : Nat) : Scalar)) := by
    have hk : 360 < pm.nodes.length := by native_decide
    rw [distributed_moe_reduce pm initPM 360 layer4PmMoe1 8050 hk
      (show pm.nodes[360]'hk = layer4PmMoe1 from layer4_pm_node360)
      rfl rfl (by native_decide) (by native_decide)]
    unfold applyNodeFullExpertMoE_value
    rw [layer4_pm_buddies1]
    simp only [layer4PmMoe0, layer4PmMoe1, List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    rw [foldl_take_distributed_eq pm initPM 14893 360 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8040 360 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8042 360 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8045 360 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8046 360 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8047 360 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8048 360 (by native_decide) (by native_decide)]

  have hc := fw_all2all_moe_gmm_full_split_commute_2
    (denoteGraphDistributed pm initPM 14870) (denoteGraphDistributed pm initPM 14893)
    (denoteGraphDistributed pm initPM 8039) (denoteGraphDistributed pm initPM 8040)
    (denoteGraphDistributed pm initPM 8041) (denoteGraphDistributed pm initPM 8042)
    (denoteGraphDistributed pm initPM 8045) (denoteGraphDistributed pm initPM 8046)
    (denoteGraphDistributed pm initPM 8047) (denoteGraphDistributed pm initPM 8048)
    2048 1024 32 8 1024 512 (((10 : Nat) : Scalar))
    (by omega) (by omega) (by omega) (by omega) (by omega) rfl
    hi.shard0_shape hi.shard1_shape hrp.shard0_shape hrp.shard1_shape
    hrm.shard0_shape hrm.shard1_shape hsW13A hsW13B hsW2A hsW2B
  have hval : denoteGraphDistributed sm initSM 4876 = allGatherPrimDimN 0 pm.numRanks 0
      [denoteGraphDistributed pm initPM 8049, denoteGraphDistributed pm initPM 8050] := by
    rw [hSMout, hi.value, hrp.value, hrm.value, hc, ← hP0, ← hP1,
      show pm.numRanks = 2 from rfl]
  have hsP0 : (denoteGraphDistributed pm initPM 8049).shape = [2048, 1024] := by
    rw [hP0]
    exact fw_all2all_moe_gmm_full_shape
      (input := denoteGraphDistributed pm initPM 14870)
      (rp := denoteGraphDistributed pm initPM 8039)
      (rm := denoteGraphDistributed pm initPM 8041)
      (w13s := [denoteGraphDistributed pm initPM 8045, denoteGraphDistributed pm initPM 8046])
      (w2s := [denoteGraphDistributed pm initPM 8047, denoteGraphDistributed pm initPM 8048])
      (numExp := 64) (topK := 8) (swigluLimit := (((10 : Nat) : Scalar)))
      (lDim := 2048) (hModel := 1024)
      (by rw [hi.shard0_shape]; rfl) (by rw [hi.shard0_shape]; rfl)
  have hsP1 : (denoteGraphDistributed pm initPM 8050).shape = [2048, 1024] := by
    rw [hP1]
    exact fw_all2all_moe_gmm_full_shape
      (input := denoteGraphDistributed pm initPM 14893)
      (rp := denoteGraphDistributed pm initPM 8040)
      (rm := denoteGraphDistributed pm initPM 8042)
      (w13s := [denoteGraphDistributed pm initPM 8045, denoteGraphDistributed pm initPM 8046])
      (w2s := [denoteGraphDistributed pm initPM 8047, denoteGraphDistributed pm initPM 8048])
      (numExp := 64) (topK := 8) (swigluLimit := (((10 : Nat) : Scalar)))
      (lDim := 2048) (hModel := 1024)
      (by rw [hi.shard1_shape]; rfl) (by rw [hi.shard1_shape]; rfl)
  have hsSM : (denoteGraphDistributed sm initSM 4876).shape = [4096, 1024] := by
    rw [hval, show pm.numRanks = 2 from rfl,
      allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsP0])]
    simp [List.set]
  exact wrap_2tp_allGather_gen _ _ intermediateGoal_4876 4876 8049 8050
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    hval hsSM hsP0 hsP1

/-! ### Layer-4 gate/expert side branches (pure distributed evaluator) -/

private theorem l2d_reshape4877_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4877)
      (denoteGraphDistributed pm initPM 8051) (denoteGraphDistributed pm initPM 8052)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_rms4867_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 135
    { rank := 0, op := "OpName.FW_multiref", ins := [4867],
      outs := [7571, 7575, 7579, 7583, 7587], params := [5] }
    4867 7579 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos2_out sm st 0 4867 7571 7575 7579 7583 7587
      (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 331
    { rank := 0, op := "OpName.FW_multiref", ins := [8029],
      outs := [14866, 14870, 14874, 14878, 14882], params := [5] }
    8029 14874 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos2_out pm st 0 8029 14866 14870 14874 14878 14882
      (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 332
    { rank := 1, op := "OpName.FW_multiref", ins := [8030],
      outs := [14889, 14893, 14897, 14901, 14905], params := [5] }
    8030 14897 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos2_out pm st 1 8030 14889 14893 14897 14901 14905
      (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have rs := l2d_reshape sm initSM 137 0 7579 4877 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l2d_reshape pm initPM 334 0 14874 8051 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l2d_reshape pm initPM 338 1 14897 8052 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 4877 = denoteGraphDistributed sm initSM 7579 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ (by rw [s]; exact h.full_shape)]
  have e0 : denoteGraphDistributed pm initPM 8051 = denoteGraphDistributed pm initPM 14874 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ (by rw [p0]; exact h.shard0_shape)]
  have e1 : denoteGraphDistributed pm initPM 8052 = denoteGraphDistributed pm initPM 14897 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ (by rw [p1]; exact h.shard1_shape)]
  exact ⟨by rw [es, s, h.value, ← p0, ← p1, ← e0, ← e1], by rw [es, s]; exact h.full_shape,
    by rw [e0, p0]; exact h.shard0_shape, by rw [e1, p1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of the first layer-4 expert reshape. -/
theorem recon_intermediateGoal_4877_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4877
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4877 4877 8051 8052
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_reshape4877_rel initSM initPM hSM hPM hInit)

private theorem l2d_reshape4882_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4882)
      (denoteGraphDistributed pm initPM 8065) (denoteGraphDistributed pm initPM 8066)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_rms4867_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 135
    { rank := 0, op := "OpName.FW_multiref", ins := [4867], outs := [7571, 7575, 7579, 7583, 7587], params := [5] }
    4867 7583 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos3_out sm st 0 4867 7571 7575 7579 7583 7587
      (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 331
    { rank := 0, op := "OpName.FW_multiref", ins := [8029], outs := [14866, 14870, 14874, 14878, 14882], params := [5] }
    8029 14878 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos3_out pm st 0 8029 14866 14870 14874 14878 14882
      (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 332
    { rank := 1, op := "OpName.FW_multiref", ins := [8030], outs := [14889, 14893, 14897, 14901, 14905], params := [5] }
    8030 14901 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos3_out pm st 1 8030 14889 14893 14897 14901 14905
      (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have rs := l2d_reshape sm initSM 138 0 7583 4882 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_reshape pm initPM 335 0 14878 8065 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_reshape pm initPM 339 1 14901 8066 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 4882 = denoteGraphDistributed sm initSM 7583 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ (by rw [s]; exact h.full_shape)]
  have e0 : denoteGraphDistributed pm initPM 8065 = denoteGraphDistributed pm initPM 14878 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ (by rw [p0]; exact h.shard0_shape)]
  have e1 : denoteGraphDistributed pm initPM 8066 = denoteGraphDistributed pm initPM 14901 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ (by rw [p1]; exact h.shard1_shape)]
  exact ⟨by rw [es, s, h.value, ← p0, ← p1, ← e0, ← e1], by rw [es, s]; exact h.full_shape,
    by rw [e0, p0]; exact h.shard0_shape, by rw [e1, p1]; exact h.shard1_shape, by decide⟩

theorem recon_intermediateGoal_4882_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4882
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4882 4882 8065 8066
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_reshape4882_rel initSM initPM hSM hPM hInit)

private theorem l2d_reshape4886_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4886)
      (denoteGraphDistributed pm initPM 8083) (denoteGraphDistributed pm initPM 8084)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_rms4867_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 135
    { rank := 0, op := "OpName.FW_multiref", ins := [4867], outs := [7571, 7575, 7579, 7583, 7587], params := [5] }
    4867 7587 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos4_out sm st 0 4867 7571 7575 7579 7583 7587
      (by decide) (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 331
    { rank := 0, op := "OpName.FW_multiref", ins := [8029], outs := [14866, 14870, 14874, 14878, 14882], params := [5] }
    8029 14882 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos4_out pm st 0 8029 14866 14870 14874 14878 14882
      (by decide) (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 332
    { rank := 1, op := "OpName.FW_multiref", ins := [8030], outs := [14889, 14893, 14897, 14901, 14905], params := [5] }
    8030 14905 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos4_out pm st 1 8030 14889 14893 14897 14901 14905
      (by decide) (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have rs := l2d_reshape sm initSM 139 0 7587 4886 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_reshape pm initPM 336 0 14882 8083 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_reshape pm initPM 340 1 14905 8084 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 4886 = denoteGraphDistributed sm initSM 7587 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ (by rw [s]; exact h.full_shape)]
  have e0 : denoteGraphDistributed pm initPM 8083 = denoteGraphDistributed pm initPM 14882 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ (by rw [p0]; exact h.shard0_shape)]
  have e1 : denoteGraphDistributed pm initPM 8084 = denoteGraphDistributed pm initPM 14905 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ (by rw [p1]; exact h.shard1_shape)]
  exact ⟨by rw [es, s, h.value, ← p0, ← p1, ← e0, ← e1], by rw [es, s]; exact h.full_shape,
    by rw [e0, p0]; exact h.shard0_shape, by rw [e1, p1]; exact h.shard1_shape, by decide⟩

theorem recon_intermediateGoal_4886_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4886
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4886 4886 8083 8084
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_reshape4886_rel initSM initPM hSM hPM hInit)

private theorem l2d_linear4879_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4879)
      (denoteGraphDistributed pm initPM 8055) (denoteGraphDistributed pm initPM 8056)
      [4096, 1] [2048, 1] := by
  have h := l2d_reshape4877_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4878
    (by native_decide) 4878 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4878
    (by native_decide) 4878 [1, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4878).shape = [1, 1024] := by rw [← hw]; exact hws
  have rs := l2d_linear sm initSM 141 0 4877 4878 4879
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_linear pm initPM 342 0 8051 4878 8055
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_linear pm initPM 346 1 8052 4878 8056
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 1 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 1 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 1 _ _ h.shard1_shape hpw

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 scalar gate linear. -/
theorem recon_intermediateGoal_4879_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4879
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4879 4879 8055 8056
    [4096, 1] [2048, 1] rfl rfl rfl rfl rfl rfl
    (l2d_linear4879_rel initSM initPM hSM hPM hInit)

private theorem l2d_linear4884_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4884)
      (denoteGraphDistributed pm initPM 8069) (denoteGraphDistributed pm initPM 8070)
      [4096, 512] [2048, 512] := by
  have h := l2d_reshape4882_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4883
    (by native_decide) 4883 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4883
    (by native_decide) 4883 [512, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4883).shape = [512, 1024] := by rw [← hw]; exact hws
  have rs := l2d_linear sm initSM 142 0 4882 4883 4884
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_linear pm initPM 343 0 8065 4883 8069
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_linear pm initPM 347 1 8066 4883 8070
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 512 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 512 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 512 _ _ h.shard1_shape hpw

theorem recon_intermediateGoal_4884_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4884
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4884 4884 8069 8070
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l2d_linear4884_rel initSM initPM hSM hPM hInit)

private theorem l2d_linear4888_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4888)
      (denoteGraphDistributed pm initPM 8087) (denoteGraphDistributed pm initPM 8088)
      [4096, 512] [2048, 512] := by
  have h := l2d_reshape4886_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4887
    (by native_decide) 4887 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4887
    (by native_decide) 4887 [512, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4887).shape = [512, 1024] := by rw [← hw]; exact hws
  have rs := l2d_linear sm initSM 143 0 4886 4887 4888
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_linear pm initPM 344 0 8083 4887 8087
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_linear pm initPM 348 1 8084 4887 8088
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 512
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 512 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 512 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 512 _ _ h.shard1_shape hpw

theorem recon_intermediateGoal_4888_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4888
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4888 4888 8087 8088
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l2d_linear4888_rel initSM initPM hSM hPM hInit)

private theorem l2d_view4880_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4880)
      (denoteGraphDistributed pm initPM 8061) (denoteGraphDistributed pm initPM 8062)
      [4096, 1] [2048, 1] := by
  have h := l2d_linear4879_rel initSM initPM hSM hPM hInit
  have rs := l2d_view sm initSM 145 0 4879 4880 4096 [1]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l2d_view pm initPM 350 0 8055 8061 2048 [1]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l2d_view pm initPM 354 1 8056 8062 2048 [1]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 4880 = denoteGraphDistributed sm initSM 4879 := by
    rw [rs, fw_view_id_shape [4096, 1] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 8061 = denoteGraphDistributed pm initPM 8055 := by
    rw [r0, fw_view_id_shape [2048, 1] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 8062 = denoteGraphDistributed pm initPM 8056 := by
    rw [r1, fw_view_id_shape [2048, 1] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 scalar gate view. -/
theorem recon_intermediateGoal_4880_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4880
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4880 4880 8061 8062
    [4096, 1] [2048, 1] rfl rfl rfl rfl rfl rfl
    (l2d_view4880_rel initSM initPM hSM hPM hInit)

private theorem l2d_view4885_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4885)
      (denoteGraphDistributed pm initPM 8079) (denoteGraphDistributed pm initPM 8080)
      [4096, 512] [2048, 512] := by
  have h := l2d_linear4884_rel initSM initPM hSM hPM hInit
  have rs := l2d_view sm initSM 146 0 4884 4885 4096 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l2d_view pm initPM 351 0 8069 8079 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l2d_view pm initPM 355 1 8070 8080 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 4885 = denoteGraphDistributed sm initSM 4884 := by
    rw [rs, fw_view_id_shape [4096, 512] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 8079 = denoteGraphDistributed pm initPM 8069 := by
    rw [r0, fw_view_id_shape [2048, 512] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 8080 = denoteGraphDistributed pm initPM 8070 := by
    rw [r1, fw_view_id_shape [2048, 512] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

theorem recon_intermediateGoal_4885_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4885
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4885 4885 8079 8080
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l2d_view4885_rel initSM initPM hSM hPM hInit)

private theorem l2d_view4889_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4889)
      (denoteGraphDistributed pm initPM 8097) (denoteGraphDistributed pm initPM 8098)
      [4096, 512] [2048, 512] := by
  have h := l2d_linear4888_rel initSM initPM hSM hPM hInit
  have rs := l2d_view sm initSM 147 0 4888 4889 4096 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l2d_view pm initPM 352 0 8087 8097 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l2d_view pm initPM 356 1 8088 8098 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 4889 = denoteGraphDistributed sm initSM 4888 := by
    rw [rs, fw_view_id_shape [4096, 512] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 8097 = denoteGraphDistributed pm initPM 8087 := by
    rw [r0, fw_view_id_shape [2048, 512] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 8098 = denoteGraphDistributed pm initPM 8088 := by
    rw [r1, fw_view_id_shape [2048, 512] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

theorem recon_intermediateGoal_4889_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4889
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4889 4889 8097 8098
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l2d_view4889_rel initSM initPM hSM hPM hInit)

/-! ### Layer-4 gate/expert postprocessing (pure distributed evaluator) -/

private theorem l2d_sigmoid4881_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4881)
      (denoteGraphDistributed pm initPM 8063) (denoteGraphDistributed pm initPM 8064)
      [4096, 1] [2048, 1] := by
  have h := l2d_view4880_rel initSM initPM hSM hPM hInit
  have rs := l2d_sigmoid sm initSM 149 0 4880 4881 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_sigmoid pm initPM 358 0 8061 8063 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_sigmoid pm initPM 361 1 8062 8064 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, fw_sigmoid_allGather0_commute_2 _ _ 2048 1
      (by omega) (by omega) h.shard0_shape h.shard1_shape, r0, r1]
  · rw [rs, fw_sigmoid_shape]; exact h.full_shape
  · rw [r0, fw_sigmoid_shape]; exact h.shard0_shape
  · rw [r1, fw_sigmoid_shape]; exact h.shard1_shape

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 sigmoid gate. -/
theorem recon_intermediateGoal_4881_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4881
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4881 4881 8063 8064
    [4096, 1] [2048, 1] rfl rfl rfl rfl rfl rfl
    (l2d_sigmoid4881_rel initSM initPM hSM hPM hInit)

private theorem l2d_swiglu4890_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4890)
      (denoteGraphDistributed pm initPM 8101) (denoteGraphDistributed pm initPM 8102)
      [4096, 512] [2048, 512] := by
  have hx := l2d_view4885_rel initSM initPM hSM hPM hInit
  have hy := l2d_view4889_rel initSM initPM hSM hPM hInit
  have rs := l2d_swiglu sm initSM 150 0 4885 4889 4890 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_swiglu pm initPM 359 0 8079 8097 8101 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_swiglu pm initPM 362 1 8080 8098 8102 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, hx.value, hy.value,
      fw_swiglu_allGather0_commute_2 _ _ _ _ 2048 512 (by omega) (by omega)
        hx.shard0_shape hx.shard1_shape hy.shard0_shape hy.shard1_shape, r0, r1]
  · rw [rs]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hy.full_shape
  · rw [r0]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hy.shard0_shape
  · rw [r1]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hy.shard1_shape

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 SwiGLU output. -/
theorem recon_intermediateGoal_4890_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4890
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4890 4890 8101 8102
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l2d_swiglu4890_rel initSM initPM hSM hPM hInit)

private theorem l2d_reshape4891_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4891)
      (denoteGraphDistributed pm initPM 8103) (denoteGraphDistributed pm initPM 8104)
      [4096, 512] [2048, 512] := by
  have h := l2d_swiglu4890_rel initSM initPM hSM hPM hInit
  have rs := l2d_reshape sm initSM 151 0 4890 4891 4096 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l2d_reshape pm initPM 363 0 8101 8103 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l2d_reshape pm initPM 364 1 8102 8104 2048 [512]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, show ([4096, 512] : Shape) = [2048 * 2, 512] from rfl,
      fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) h.shard0_shape h.shard1_shape,
      r0, r1]
  · rw [rs]; rfl
  · rw [r0]; rfl
  · rw [r1]; rfl

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 SwiGLU reshape. -/
theorem recon_intermediateGoal_4891_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4891
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4891 4891 8103 8104
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l2d_reshape4891_rel initSM initPM hSM hPM hInit)

private theorem l2d_linear4893_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4893)
      (denoteGraphDistributed pm initPM 8109) (denoteGraphDistributed pm initPM 8110)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_reshape4891_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4892
    (by native_decide) 4892 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4892
    (by native_decide) 4892 [1024, 512] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4892).shape = [1024, 512] := by
    rw [← hw]; exact hws
  have rs := l2d_linear sm initSM 152 0 4891 4892 4893 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_linear pm initPM 365 0 8103 4892 8109 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_linear pm initPM 366 1 8104 4892 8110 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw,
      fw_linear_allGather0_commute_2_of _ _ _ 2048 512 1024 (by omega) (by omega) (by omega)
        h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 512 1024 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 512 1024 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 512 1024 _ _ h.shard1_shape hpw

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 expert output linear. -/
theorem recon_intermediateGoal_4893_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4893
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4893 4893 8109 8110
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_linear4893_rel initSM initPM hSM hPM hInit)

private theorem l2d_view4894_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4894)
      (denoteGraphDistributed pm initPM 8119) (denoteGraphDistributed pm initPM 8120)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_linear4893_rel initSM initPM hSM hPM hInit
  have rs := l2d_view sm initSM 153 0 4893 4894 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l2d_view pm initPM 367 0 8109 8119 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l2d_view pm initPM 368 1 8110 8120 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, show ([4096, 1024] : Shape) = [2048 * 2, 1024] from rfl,
      fw_view_allGather0_commute_2_of _ _ 2048 1024 (by omega) h.shard0_shape h.shard1_shape,
      r0, r1]
  · rw [rs]; rfl
  · rw [r0]; rfl
  · rw [r1]; rfl

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 expert output view. -/
theorem recon_intermediateGoal_4894_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4894
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4894 4894 8119 8120
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_view4894_rel initSM initPM hSM hPM hInit)

private theorem l2d_mul4895_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4895)
      (denoteGraphDistributed pm initPM 8123) (denoteGraphDistributed pm initPM 8124)
      [4096, 1024] [2048, 1024] := by
  have hs := l2d_sigmoid4881_rel initSM initPM hSM hPM hInit
  have hv := l2d_view4894_rel initSM initPM hSM hPM hInit
  have rs := l2d_mul sm initSM 154 0 4881 4894 4895 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_mul pm initPM 369 0 8063 8119 8123 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_mul pm initPM 370 1 8064 8120 8124 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have mulShape : ∀ (x y : Tensor) (a : Nat),
      x.shape = [a, 1] → y.shape = [a, 1024] → (elemwiseMul x y).shape = [a, 1024] := by
    intro x y a hx hy
    show outShape2 x y = [a, 1024]
    unfold outShape2
    rw [hx, hy]
    show (max a a) :: (1024 : Nat) :: [] = [a, 1024]
    rw [Nat.max_self]
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, hs.value, hv.value,
      fw_mul_allGather0_commute_2_of_broadcast _ _ _ _ 2048 1024
        (by omega) (by omega) (by decide) (by decide) (by decide)
        hs.shard0_shape hs.shard1_shape hv.shard0_shape hv.shard1_shape, r0, r1]
  · rw [rs]; exact mulShape _ _ 4096 hs.full_shape hv.full_shape
  · rw [r0]; exact mulShape _ _ 2048 hs.shard0_shape hv.shard0_shape
  · rw [r1]; exact mulShape _ _ 2048 hs.shard1_shape hv.shard1_shape

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 broadcast gate product. -/
theorem recon_intermediateGoal_4895_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4895
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4895 4895 8123 8124
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_mul4895_rel initSM initPM hSM hPM hInit)

/-! ### Layer-4 post-MoE residual tail (pure distributed evaluator) -/

private theorem l2d_goal7564_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7564)
      (denoteGraphDistributed pm initPM 14851) (denoteGraphDistributed pm initPM 14859)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_add4865_rel initSM initPM hSM hPM hInit
  have rs := distributed_reduce1 sm initSM 133
    { rank := 0, op := "OpName.FW_multiref", ins := [4865], outs := [7560, 7564], params := [2] }
    4865 7564 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' sm st 0 4865 7560 7564 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce1 pm initPM 327
    { rank := 0, op := "OpName.FW_multiref", ins := [8025], outs := [14847, 14851], params := [2] }
    8025 14851 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 0 8025 14847 14851 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce1 pm initPM 328
    { rank := 1, op := "OpName.FW_multiref", ins := [8026], outs := [14855, 14859], params := [2] }
    8026 14859 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 1 8026 14855 14859 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rs r0 r1
  exact ⟨by rw [rs, h.value, r0, r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 pre-MoE residual carry. -/
theorem recon_intermediateGoal_7564_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7564
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_7564 7564 14851 14859
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_goal7564_rel initSM initPM hSM hPM hInit)

private theorem l2d_add4896_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4896)
      (denoteGraphDistributed pm initPM 8127) (denoteGraphDistributed pm initPM 8128)
      [4096, 1024] [2048, 1024] := by
  have ha := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_4876 4876 8049 8050
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4876_distributed initSM initPM hSM hPM hInit)
  have hb := l2d_mul4895_rel initSM initPM hSM hPM hInit
  have rs := l2d_add sm initSM 155 0 4876 4895 4896 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_add pm initPM 371 0 8049 8123 8127 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_add pm initPM 372 1 8050 8124 8128 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, ha.value, hb.value,
      fw_add_allGather0_commute_2_2048_1024 _ _ _ _ ha.shard0_shape ha.shard1_shape
        hb.shard0_shape hb.shard1_shape, r0, r1]
  · rw [rs]; exact elemwiseAdd_shape_of_shapes _ _ [4096, 1024] ha.full_shape hb.full_shape
  · rw [r0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] ha.shard0_shape hb.shard0_shape
  · rw [r1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] ha.shard1_shape hb.shard1_shape

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 post-MoE residual add. -/
theorem recon_intermediateGoal_4896_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4896
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4896 4896 8127 8128
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_add4896_rel initSM initPM hSM hPM hInit)

private theorem l2d_float4897_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4897)
      (denoteGraphDistributed pm initPM 8133) (denoteGraphDistributed pm initPM 8134)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_add4896_rel initSM initPM hSM hPM hInit
  have rs := l2d_float sm initSM 156 0 4896 4897 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_float pm initPM 373 0 8127 8133 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_float pm initPM 374 1 8128 8134 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  exact ⟨by rw [rs, h.value, r0, r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 post-MoE float. -/
theorem recon_intermediateGoal_4897_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4897
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4897 4897 8133 8134
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_float4897_rel initSM initPM hSM hPM hInit)

private theorem l2d_add4898_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4898)
      (denoteGraphDistributed pm initPM 8137) (denoteGraphDistributed pm initPM 8138)
      [4096, 1024] [2048, 1024] := by
  have ha := l2d_goal7564_rel initSM initPM hSM hPM hInit
  have hb := l2d_float4897_rel initSM initPM hSM hPM hInit
  have rs := l2d_add sm initSM 157 0 7564 4897 4898 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_add pm initPM 375 0 14851 8133 8137 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_add pm initPM 376 1 14859 8134 8138 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, ha.value, hb.value,
      fw_add_allGather0_commute_2_2048_1024 _ _ _ _ ha.shard0_shape ha.shard1_shape
        hb.shard0_shape hb.shard1_shape, r0, r1]
  · rw [rs]; exact elemwiseAdd_shape_of_shapes _ _ [4096, 1024] ha.full_shape hb.full_shape
  · rw [r0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] ha.shard0_shape hb.shard0_shape
  · rw [r1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] ha.shard1_shape hb.shard1_shape

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 cross-block residual add. -/
theorem recon_intermediateGoal_4898_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4898
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4898 4898 8137 8138
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_add4898_rel initSM initPM hSM hPM hInit)

/-! ### Layer-4 attention projections (pure distributed evaluator) -/

private theorem l2d_rms4900_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4900)
      (denoteGraphDistributed pm initPM 8141) (denoteGraphDistributed pm initPM 8142)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_add4898_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 158
    { rank := 0, op := "OpName.FW_multiref", ins := [4898], outs := [7591, 7595], params := [2] }
    4898 7591 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out sm st 0 4898 7591 7595)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 377
    { rank := 0, op := "OpName.FW_multiref", ins := [8137], outs := [14909, 14913], params := [2] }
    8137 14909 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 0 8137 14909 14913)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 378
    { rank := 1, op := "OpName.FW_multiref", ins := [8138], outs := [14917, 14921], params := [2] }
    8138 14917 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 1 8138 14917 14921)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4899
    (by native_decide) 4899 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have rs := l2d_rms sm initSM 159 0 7591 4899 4900 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_rms pm initPM 379 0 14909 4899 8141 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_rms pm initPM 380 1 14917 4899 8142 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 14909).shape = [2048, 1024] := by
    rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 14917).shape = [2048, 1024] := by
    rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs0 hs1,
      r0, r1]
  · rw [rs]; exact fw_rms_norm_shape2 _ _ 4096 1024 (by rw [s]; exact h.full_shape)
  · rw [r0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs0
  · rw [r1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs1

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 attention RMSNorm. -/
theorem recon_intermediateGoal_4900_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4900
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4900 4900 8141 8142
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_rms4900_rel initSM initPM hSM hPM hInit)

private theorem l2d_q4902_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4902)
      (denoteGraphDistributed pm initPM 8143) (denoteGraphDistributed pm initPM 8144)
      [4096, 16, 64] [2048, 16, 64] := by
  have h := l2d_rms4900_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 160
    { rank := 0, op := "OpName.FW_multiref", ins := [4900], outs := [7600, 7604, 7608], params := [3] }
    4900 7600 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' sm st 0 4900 7600 7604 7608)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 381
    { rank := 0, op := "OpName.FW_multiref", ins := [8141], outs := [14926, 14930, 14934], params := [3] }
    8141 14926 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' pm st 0 8141 14926 14930 14934)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 382
    { rank := 1, op := "OpName.FW_multiref", ins := [8142], outs := [14939, 14943, 14947], params := [3] }
    8142 14939 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' pm st 1 8142 14939 14943 14947)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4901
    (by native_decide) 4901 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4901
    (by native_decide) 4901 [16, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4901).shape = [16, 64, 1024] := by rw [← hw]; exact hws
  have rs := l2d_per_head_linear sm initSM 161 0 7600 4901 4902 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_per_head_linear pm initPM 383 0 14926 4901 8143 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_per_head_linear pm initPM 386 1 14939 4901 8144 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 14926).shape = [2048, 1024] := by rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 14939).shape = [2048, 1024] := by rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 16 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, r0, r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 16 64 (by rw [s]; exact h.full_shape) hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs0 hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs1 hpw

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 Q projection. -/
theorem recon_intermediateGoal_4902_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4902
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4902 4902 8143 8144
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl
    (l2d_q4902_rel initSM initPM hSM hPM hInit)

private theorem l2d_k4904_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4904)
      (denoteGraphDistributed pm initPM 8155) (denoteGraphDistributed pm initPM 8156)
      [4096, 4, 64] [2048, 4, 64] := by
  have h := l2d_rms4900_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 160
    { rank := 0, op := "OpName.FW_multiref", ins := [4900], outs := [7600, 7604, 7608], params := [3] }
    4900 7604 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' sm st 0 4900 7600 7604 7608 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 381
    { rank := 0, op := "OpName.FW_multiref", ins := [8141], outs := [14926, 14930, 14934], params := [3] }
    8141 14930 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' pm st 0 8141 14926 14930 14934 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 382
    { rank := 1, op := "OpName.FW_multiref", ins := [8142], outs := [14939, 14943, 14947], params := [3] }
    8142 14943 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' pm st 1 8142 14939 14943 14947 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4903
    (by native_decide) 4903 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4903
    (by native_decide) 4903 [4, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4903).shape = [4, 64, 1024] := by rw [← hw]; exact hws
  have rs := l2d_per_head_linear sm initSM 162 0 7604 4903 4904 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_per_head_linear pm initPM 384 0 14930 4903 8155 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_per_head_linear pm initPM 387 1 14943 4903 8156 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 14930).shape = [2048, 1024] := by rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 14943).shape = [2048, 1024] := by rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, r0, r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64 (by rw [s]; exact h.full_shape) hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs0 hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs1 hpw

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 K projection. -/
theorem recon_intermediateGoal_4904_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4904
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4904 4904 8155 8156
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l2d_k4904_rel initSM initPM hSM hPM hInit)

private theorem l2d_v4906_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4906)
      (denoteGraphDistributed pm initPM 8165) (denoteGraphDistributed pm initPM 8166)
      [4096, 4, 64] [2048, 4, 64] := by
  have h := l2d_rms4900_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 160
    { rank := 0, op := "OpName.FW_multiref", ins := [4900], outs := [7600, 7604, 7608], params := [3] }
    4900 7608 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' sm st 0 4900 7600 7604 7608 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 381
    { rank := 0, op := "OpName.FW_multiref", ins := [8141], outs := [14926, 14930, 14934], params := [3] }
    8141 14934 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' pm st 0 8141 14926 14930 14934 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 382
    { rank := 1, op := "OpName.FW_multiref", ins := [8142], outs := [14939, 14943, 14947], params := [3] }
    8142 14947 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' pm st 1 8142 14939 14943 14947 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4905
    (by native_decide) 4905 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4905
    (by native_decide) 4905 [4, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4905).shape = [4, 64, 1024] := by rw [← hw]; exact hws
  have rs := l2d_per_head_linear sm initSM 163 0 7608 4905 4906 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_per_head_linear pm initPM 385 0 14934 4905 8165 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_per_head_linear pm initPM 388 1 14947 4905 8166 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 14934).shape = [2048, 1024] := by rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 14947).shape = [2048, 1024] := by rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, r0, r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64 (by rw [s]; exact h.full_shape) hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs0 hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs1 hpw

/-- Pure-distributed exact 2-TP reconstruction of the layer-4 V projection. -/
theorem recon_intermediateGoal_4906_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4906
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4906 4906 8165 8166
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l2d_v4906_rel initSM initPM hSM hPM hInit)

/-- Distributed cache agreement for the layer-4 PM rotary-cache replica. -/
private theorem l2d_rotary_cache_11857 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraphDistributed sm initSM 4691 = denoteGraphDistributed pm initPM 11857 := by
  have hsource := sm_pm_rotary_cache_agree initSM initPM hInit 11857 4 (by norm_num) rfl
  have hbase := distributed_init_singleton_value initSM initPM hInit initGoal_4691
    (by native_decide) 4691 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hcopy : denoteGraphDistributed pm initPM 11857 = id (denoteGraphDistributed pm initPM 4691) :=
    distributed_reduce1 pm initPM 14
      { rank := 1, op := "OpName.FW_multiref", ins := [4691],
        outs := (List.range 12).map (fun r => 11853 + r),
        params := [((List.range 12).map (fun r => 11853 + r)).length] }
      4691 11857 id (by native_decide) (by native_decide) (by decide)
      (fun s => by
        rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm s _ (by decide) (by decide)]
        rw [applyNode_fw_multiref_mem_out pm s 1 4691
          ((List.range 12).map (fun r => 11853 + r)) 11857 (by native_decide), id_eq])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  rw [hcopy, id_eq]
  exact hbase

set_option maxHeartbeats 8000000 in
private theorem l2d_rotary4908_4909_rels (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4908)
      (denoteGraphDistributed pm initPM 8177) (denoteGraphDistributed pm initPM 8178)
      [4096, 16, 64] [2048, 16, 64] ∧
    Gather2Rel (denoteGraphDistributed sm initSM 4909)
      (denoteGraphDistributed pm initPM 8179) (denoteGraphDistributed pm initPM 8180)
      [4096, 4, 64] [2048, 4, 64] := by
  have hq := l2d_q4902_rel initSM initPM hSM hPM hInit
  have hk := l2d_k4904_rel initSM initPM hSM hPM hInit
  have hcache := l2d_rotary_cache_11857 initSM initPM hInit
  have hpos := distributed_init_singleton_value initSM initPM hInit initGoal_4907
    (by native_decide) 4907 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hspos := distributed_init_singleton_shape initSM initPM hInit initGoal_4907
    (by native_decide) 4907 [4096] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have c0 := l2d_chunk pm initPM 4 0 4907 8175 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c1 := l2d_chunk pm initPM 17 1 4907 8176 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c0' : denoteGraphDistributed pm initPM 8175 = chunkPrimDimN 0 2 0 (denoteGraphDistributed pm initPM 4907) := c0
  have c1' : denoteGraphDistributed pm initPM 8176 = chunkPrimDimN 0 2 1 (denoteGraphDistributed pm initPM 4907) := c1
  have qSM : denoteGraphDistributed sm initSM 4908 =
      (fw_rotary_embedding (denoteGraphDistributed sm initSM 4691) (denoteGraphDistributed sm initSM 4907)
        (denoteGraphDistributed sm initSM 4902) (denoteGraphDistributed sm initSM 4904) 16 4).1 := by
    rw [distributed_node_core sm initSM 164
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4907, 4902, 4904], outs := [4908, 4909], params := [16, 4] }
      4908 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring sm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read sm initSM 164 4691 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 164 4907 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 164 4902 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 164 4904 (by native_decide) (by native_decide)]
  have kSM : denoteGraphDistributed sm initSM 4909 =
      (fw_rotary_embedding (denoteGraphDistributed sm initSM 4691) (denoteGraphDistributed sm initSM 4907)
        (denoteGraphDistributed sm initSM 4902) (denoteGraphDistributed sm initSM 4904) 16 4).2 := by
    rw [distributed_node_core sm initSM 164
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4907, 4902, 4904], outs := [4908, 4909], params := [16, 4] }
      4909 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring sm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 4691 4907 4902 4904 4908 4909 (by decide),
      distributed_prefix_read sm initSM 164 4691 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 164 4907 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 164 4902 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 164 4904 (by native_decide) (by native_decide)]
  have q0 : denoteGraphDistributed pm initPM 8177 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11857) (denoteGraphDistributed pm initPM 8175)
        (denoteGraphDistributed pm initPM 8143) (denoteGraphDistributed pm initPM 8155) 16 4).1 := by
    rw [distributed_node_core pm initPM 389
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11857, 8175, 8143, 8155], outs := [8177, 8179], params := [16, 4] }
      8177 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide), applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read pm initPM 389 11857 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 389 8175 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 389 8143 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 389 8155 (by native_decide) (by native_decide)]
  have k0 : denoteGraphDistributed pm initPM 8179 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11857) (denoteGraphDistributed pm initPM 8175)
        (denoteGraphDistributed pm initPM 8143) (denoteGraphDistributed pm initPM 8155) 16 4).2 := by
    rw [distributed_node_core pm initPM 389
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11857, 8175, 8143, 8155], outs := [8177, 8179], params := [16, 4] }
      8179 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11857 8175 8143 8155 8177 8179 (by decide),
      distributed_prefix_read pm initPM 389 11857 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 389 8175 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 389 8143 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 389 8155 (by native_decide) (by native_decide)]
  have q1 : denoteGraphDistributed pm initPM 8178 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11857) (denoteGraphDistributed pm initPM 8176)
        (denoteGraphDistributed pm initPM 8144) (denoteGraphDistributed pm initPM 8156) 16 4).1 := by
    rw [distributed_node_core pm initPM 390
      { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11857, 8176, 8144, 8156], outs := [8178, 8180], params := [16, 4] }
      8178 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide), applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read pm initPM 390 11857 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 390 8176 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 390 8144 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 390 8156 (by native_decide) (by native_decide)]
  have k1 : denoteGraphDistributed pm initPM 8180 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11857) (denoteGraphDistributed pm initPM 8176)
        (denoteGraphDistributed pm initPM 8144) (denoteGraphDistributed pm initPM 8156) 16 4).2 := by
    rw [distributed_node_core pm initPM 390
      { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11857, 8176, 8144, 8156], outs := [8178, 8180], params := [16, 4] }
      8180 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11857 8176 8144 8156 8178 8180 (by decide),
      distributed_prefix_read pm initPM 390 11857 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 390 8176 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 390 8144 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 390 8156 (by native_decide) (by native_decide)]
  have qval : denoteGraphDistributed sm initSM 4908 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 8177, denoteGraphDistributed pm initPM 8178] := by
    rw [qSM]; simp only [fw_rotary_embedding]
    rw [hq.value, fw_rotary_apply_allGather0_commute_2_1d (denoteGraphDistributed sm initSM 4691)
      (denoteGraphDistributed sm initSM 4907) (denoteGraphDistributed pm initPM 8143)
      (denoteGraphDistributed pm initPM 8144) 2048 16 64 (by omega) (by omega) (by omega)
      hspos hq.shard0_shape hq.shard1_shape, hcache, hpos, ← c0', ← c1', q0, q1]
    simp only [fw_rotary_embedding]
  have kval : denoteGraphDistributed sm initSM 4909 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 8179, denoteGraphDistributed pm initPM 8180] := by
    rw [kSM]; simp only [fw_rotary_embedding]
    rw [hk.value, fw_rotary_apply_allGather0_commute_2_1d (denoteGraphDistributed sm initSM 4691)
      (denoteGraphDistributed sm initSM 4907) (denoteGraphDistributed pm initPM 8155)
      (denoteGraphDistributed pm initPM 8156) 2048 4 64 (by omega) (by omega) (by omega)
      hspos hk.shard0_shape hk.shard1_shape, hcache, hpos, ← c0', ← c1', k0, k1]
    simp only [fw_rotary_embedding]
  have qs0 : (denoteGraphDistributed pm initPM 8177).shape = [2048, 16, 64] := by
    rw [q0]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hq.shard0_shape
  have qs1 : (denoteGraphDistributed pm initPM 8178).shape = [2048, 16, 64] := by
    rw [q1]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hq.shard1_shape
  have ks0 : (denoteGraphDistributed pm initPM 8179).shape = [2048, 4, 64] := by
    rw [k0]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hk.shard0_shape
  have ks1 : (denoteGraphDistributed pm initPM 8180).shape = [2048, 4, 64] := by
    rw [k1]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hk.shard1_shape
  refine ⟨⟨qval, ?_, qs0, qs1, by decide⟩, ⟨kval, ?_, ks0, ks1, by decide⟩⟩
  · rw [qval, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [qs0])]; rfl
  · rw [kval, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [ks0])]; rfl

/-- Public pure-distributed exact 2-TP reconstruction of the layer-4 rotary Q output. -/
theorem recon_intermediateGoal_4908_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4908
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4908 4908 8177 8178
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl
    (l2d_rotary4908_4909_rels initSM initPM hSM hPM hInit).1

/-- Public pure-distributed exact 2-TP reconstruction of the layer-4 rotary K output. -/
theorem recon_intermediateGoal_4909_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4909
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4909 4909 8179 8180
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l2d_rotary4908_4909_rels initSM initPM hSM hPM hInit).2

private def layer5SmSliding : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [4908, 4909, 4906, 4910, 4911], outs := [4912],
    params := [16, 4, 64, 64, 1, 512] }
private def layer5PmSliding0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [8177, 8179, 8165, 4910, 4911], outs := [8181],
    params := [16, 4, 64, 64, 1, 512] }
private def layer5PmSliding1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window",
    ins := [8178, 8180, 8166, 4910, 4911], outs := [8182],
    params := [16, 4, 64, 64, 1, 512] }

-- Keep graph and replica-order certificates separate from the tensor proof.
set_option maxRecDepth 1000000 in
private theorem layer5_sm_node165 : sm.nodes[165]'(by native_decide) = layer5SmSliding := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer5_pm_node391 : pm.nodes[391]'(by native_decide) = layer5PmSliding0 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer5_pm_node392 : pm.nodes[392]'(by native_decide) = layer5PmSliding1 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer5_sm_buddy_sliding :
    ringAttnBuddies sm layer5SmSliding = [layer5SmSliding] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer5_pm_buddy_sliding0 :
    ringAttnBuddies pm layer5PmSliding0 = [layer5PmSliding0, layer5PmSliding1] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer5_pm_buddy_sliding1 :
    ringAttnBuddies pm layer5PmSliding1 = [layer5PmSliding0, layer5PmSliding1] := by native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
/-- Pure-distributed 2-TP reconstruction of the layer-4 sliding-attention output. -/
theorem recon_intermediateGoal_4912_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4912
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have gq := recon_intermediateGoal_4908_distributed initSM initPM hSM hPM hInit
  have gk := recon_intermediateGoal_4909_distributed initSM initPM hSM hPM hInit
  have gv := recon_intermediateGoal_4906_distributed initSM initPM hSM hPM hInit
  have gqshape : (denoteGraphDistributed sm initSM 4908).shape = [4096, 16, 64] := by
    simpa only [intermediateGoal_4908] using gq.1
  have gkshape : (denoteGraphDistributed sm initSM 4909).shape = [4096, 4, 64] := by
    simpa only [intermediateGoal_4909] using gk.1
  have gvshape : (denoteGraphDistributed sm initSM 4906).shape = [4096, 4, 64] := by
    simpa only [intermediateGoal_4906] using gv.1
  have q := (l2d_rotary4908_4909_rels initSM initPM hSM hPM hInit).1
  have k := (l2d_rotary4908_4909_rels initSM initPM hSM hPM hInit).2
  have v := l2d_v4906_rel initSM initPM hSM hPM hInit
  have hcu4910 := distributed_init_singleton_value initSM initPM hInit initGoal_4910
    (by native_decide) 4910 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hcu4911 := distributed_init_singleton_value initSM initPM hInit initGoal_4911
    (by native_decide) 4911 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  let fs := (sm.nodes.take 165).foldl (applyNodeDistributed sm) initSM
  let fp := (pm.nodes.take 391).foldl (applyNodeDistributed pm) initPM
  let fp' := (pm.nodes.take 392).foldl (applyNodeDistributed pm) initPM
  have bs (t : Tid) (hn : ∀ n ∈ sm.nodes.drop 165, n.outs ≠ [])
      (hw : ∀ n ∈ sm.nodes.drop 165, t ∉ n.outs) : fs t = denoteGraphDistributed sm initSM t :=
    distributed_prefix_read sm initSM 165 t hn hw
  have bp (t : Tid) (hn : ∀ n ∈ pm.nodes.drop 391, n.outs ≠ [])
      (hw : ∀ n ∈ pm.nodes.drop 391, t ∉ n.outs) : fp t = denoteGraphDistributed pm initPM t :=
    distributed_prefix_read pm initPM 391 t hn hw
  have hqfull : fs 4908 = allGatherPrimDimN 0 2 0 [fp 8177, fp 8178] := by
    rw [bs 4908 (by native_decide) (by native_decide),
      bp 8177 (by native_decide) (by native_decide),
      bp 8178 (by native_decide) (by native_decide)]
    exact q.value
  have hkfull : fs 4909 = allGatherPrimDimN 0 2 0 [fp 8179, fp 8180] := by
    rw [bs 4909 (by native_decide) (by native_decide),
      bp 8179 (by native_decide) (by native_decide),
      bp 8180 (by native_decide) (by native_decide)]
    exact k.value
  have hvfull : fs 4906 = allGatherPrimDimN 0 2 0 [fp 8165, fp 8166] := by
    rw [bs 4906 (by native_decide) (by native_decide),
      bp 8165 (by native_decide) (by native_decide),
      bp 8166 (by native_decide) (by native_decide)]
    exact v.value
  have hqpos : 0 < (fs (layer5SmSliding.ins.getD 0 0)).shape.length := by
    show 0 < (fs 4908).shape.length
    rw [bs 4908 (by native_decide) (by native_decide), gqshape]
    decide
  have hkpos : 0 < (fs (layer5SmSliding.ins.getD 1 0)).shape.length := by
    show 0 < (fs 4909).shape.length
    rw [bs 4909 (by native_decide) (by native_decide), gkshape]
    decide
  have hvpos : 0 < (fs (layer5SmSliding.ins.getD 2 0)).shape.length := by
    show 0 < (fs 4906).shape.length
    rw [bs 4906 (by native_decide) (by native_decide), gvshape]
    decide
  have hcuQ : fs 4910 = fp 4910 := by
    rw [bs 4910 (by native_decide) (by native_decide),
      bp 4910 (by native_decide) (by native_decide), hcu4910]
  have hcuK : fs 4911 = fp 4911 := by
    rw [bs 4911 (by native_decide) (by native_decide),
      bp 4911 (by native_decide) (by native_decide), hcu4911]
  have e8177 : fp 8177 = fp' 8177 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8177 391 392
      (by omega) (by native_decide) (by native_decide)).symm
  have e8178 : fp 8178 = fp' 8178 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8178 391 392
      (by omega) (by native_decide) (by native_decide)).symm
  have e8179 : fp 8179 = fp' 8179 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8179 391 392
      (by omega) (by native_decide) (by native_decide)).symm
  have e8180 : fp 8180 = fp' 8180 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8180 391 392
      (by omega) (by native_decide) (by native_decide)).symm
  have e8165 : fp 8165 = fp' 8165 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8165 391 392
      (by omega) (by native_decide) (by native_decide)).symm
  have e8166 : fp 8166 = fp' 8166 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8166 391 392
      (by omega) (by native_decide) (by native_decide)).symm
  have e4910 : fp 4910 = fp' 4910 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 4910 391 392
      (by omega) (by native_decide) (by native_decide)).symm
  have e4911 : fp 4911 = fp' 4911 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 4911 391 392
      (by omega) (by native_decide) (by native_decide)).symm
  have bridge : applyNodeRingAttn_sliding_window pm fp layer5PmSliding1 =
      applyNodeRingAttn_sliding_window pm fp' layer5PmSliding1 := by
    apply attn_sw_store_congr
    · rw [layer5_pm_buddy_sliding1]; intro m hm; fin_cases hm
      · exact e8177
      · exact e8178
    · rw [layer5_pm_buddy_sliding1]; intro m hm; fin_cases hm
      · exact e8179
      · exact e8180
    · rw [layer5_pm_buddy_sliding1]; intro m hm; fin_cases hm
      · exact e8165
      · exact e8166
    · exact e4910
    · exact e4911
  have rSM : denoteGraphDistributed sm initSM 4912 =
      applyNodeRingAttn_sliding_window sm fs layer5SmSliding := by
    rw [distributed_node_core sm initSM 165 layer5SmSliding 4912 (by native_decide)
      layer5_sm_node165 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out sm _ 0 4908 4909 4906 4910 4911 4912
      [16, 4, 64, 64, 1, 512]
  have rP0 : denoteGraphDistributed pm initPM 8181 =
      applyNodeRingAttn_sliding_window pm fp layer5PmSliding0 := by
    rw [distributed_node_core pm initPM 391 layer5PmSliding0 8181 (by native_decide)
      layer5_pm_node391 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out pm _ 0 8177 8179 8165 4910 4911 8181
      [16, 4, 64, 64, 1, 512]
  have rP1 : denoteGraphDistributed pm initPM 8182 =
      applyNodeRingAttn_sliding_window pm fp' layer5PmSliding1 := by
    rw [distributed_node_core pm initPM 392 layer5PmSliding1 8182 (by native_decide)
      layer5_pm_node392 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out pm _ 1 8178 8180 8166 4910 4911 8182
      [16, 4, 64, 64, 1, 512]
  have hfull : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 8177, fp 8178])
      (allGatherPrimDimN 0 2 0 [fp 8179, fp 8180])
      (allGatherPrimDimN 0 2 0 [fp 8165, fp 8166])
      (fp 4910) (fp 4911) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3, ← hqfull,
      bs 4908 (by native_decide) (by native_decide), gqshape]
    rfl
  have hfull' : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 8177, fp' 8178])
      (allGatherPrimDimN 0 2 0 [fp' 8179, fp' 8180])
      (allGatherPrimDimN 0 2 0 [fp' 8165, fp' 8166])
      (fp' 4910) (fp' 4911) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [← e8177, ← e8178, ← e8179, ← e8180, ← e8165, ← e8166,
      ← e4910, ← e4911]
    exact hfull
  exact recon_attn_sliding_window_2tp_distributed initSM initPM intermediateGoal_4912
    layer5SmSliding layer5PmSliding0 layer5PmSliding1 fs fp fp' 4912 8181 8182
    2048 16 64 (by omega) (by omega) (by omega) rSM rP0 rP1 bridge
    layer5_sm_buddy_sliding layer5_pm_buddy_sliding0 layer5_pm_buddy_sliding1
    (by native_decide) (by native_decide) hqpos hkpos hvpos hqfull hkfull hvfull
    hcuQ hcuK rfl rfl rfl rfl hfull hfull' rfl rfl rfl rfl rfl rfl

/-! ### Layer-5 post-attention residual cascade (pure distributed evaluator) -/

private theorem l2d_reshape4913_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4913)
      (denoteGraphDistributed pm initPM 8183) (denoteGraphDistributed pm initPM 8184)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_4912 4912 8181 8182
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4912_distributed initSM initPM hSM hPM hInit)
  have rs := l2d_reshape sm initSM 166 0 4912 4913 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l2d_reshape pm initPM 393 0 8181 8183 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l2d_reshape pm initPM 394 1 8182 8184 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, fw_view_allGather0_reshape_16_64_2_g12 _ _ h.shard0_shape h.shard1_shape,
      r0, r1]
  · rw [rs]; rfl
  · rw [r0]; rfl
  · rw [r1]; rfl

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 attention reshape. -/
theorem recon_intermediateGoal_4913_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4913
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4913 4913 8183 8184
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_reshape4913_rel initSM initPM hSM hPM hInit)

private theorem l2d_reshape4914_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4914)
      (denoteGraphDistributed pm initPM 8189) (denoteGraphDistributed pm initPM 8190)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_reshape4913_rel initSM initPM hSM hPM hInit
  have rs := l2d_reshape sm initSM 167 0 4913 4914 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l2d_reshape pm initPM 395 0 8183 8189 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l2d_reshape pm initPM 396 1 8184 8190 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 4914 = denoteGraphDistributed sm initSM 4913 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 8189 = denoteGraphDistributed pm initPM 8183 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 8190 = denoteGraphDistributed pm initPM 8184 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 identity reshape. -/
theorem recon_intermediateGoal_4914_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4914
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4914 4914 8189 8190
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_reshape4914_rel initSM initPM hSM hPM hInit)

private theorem l2d_linear4916_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4916)
      (denoteGraphDistributed pm initPM 8193) (denoteGraphDistributed pm initPM 8194)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_reshape4914_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4915
    (by native_decide) 4915 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4915
    (by native_decide) 4915 [1024, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4915).shape = [1024, 1024] := by
    rw [← hw]; exact hws
  have rs := l2d_linear sm initSM 168 0 4914 4915 4916 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_linear pm initPM 397 0 8189 4915 8193 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_linear pm initPM 398 1 8190 4915 8194 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 1024 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 1024 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 1024 _ _ h.shard1_shape hpw

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 output projection. -/
theorem recon_intermediateGoal_4916_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4916
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4916 4916 8193 8194
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_linear4916_rel initSM initPM hSM hPM hInit)

private theorem l2d_view4917_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4917)
      (denoteGraphDistributed pm initPM 8203) (denoteGraphDistributed pm initPM 8204)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_linear4916_rel initSM initPM hSM hPM hInit
  have rs := l2d_view sm initSM 169 0 4916 4917 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l2d_view pm initPM 399 0 8193 8203 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l2d_view pm initPM 400 1 8194 8204 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 4917 = denoteGraphDistributed sm initSM 4916 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 8203 = denoteGraphDistributed pm initPM 8193 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 8204 = denoteGraphDistributed pm initPM 8194 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 identity view. -/
theorem recon_intermediateGoal_4917_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4917
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4917 4917 8203 8204
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_view4917_rel initSM initPM hSM hPM hInit)

private theorem l2d_float4918_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4918)
      (denoteGraphDistributed pm initPM 8207) (denoteGraphDistributed pm initPM 8208)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_view4917_rel initSM initPM hSM hPM hInit
  have rs := l2d_float sm initSM 170 0 4917 4918 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_float pm initPM 401 0 8203 8207 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_float pm initPM 402 1 8204 8208 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  exact ⟨by rw [rs, h.value, r0, r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 float output. -/
theorem recon_intermediateGoal_4918_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4918
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4918 4918 8207 8208
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_float4918_rel initSM initPM hSM hPM hInit)

private theorem l2d_goal7595_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7595)
      (denoteGraphDistributed pm initPM 14913) (denoteGraphDistributed pm initPM 14921)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_add4898_rel initSM initPM hSM hPM hInit
  have rs := distributed_reduce1 sm initSM 158
    { rank := 0, op := "OpName.FW_multiref", ins := [4898], outs := [7591, 7595], params := [2] }
    4898 7595 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' sm st 0 4898 7591 7595 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce1 pm initPM 377
    { rank := 0, op := "OpName.FW_multiref", ins := [8137], outs := [14909, 14913], params := [2] }
    8137 14913 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 0 8137 14909 14913 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce1 pm initPM 378
    { rank := 1, op := "OpName.FW_multiref", ins := [8138], outs := [14917, 14921], params := [2] }
    8138 14921 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 1 8138 14917 14921 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rs r0 r1
  exact ⟨by rw [rs, h.value, r0, r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 residual carry. -/
theorem recon_intermediateGoal_7595_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7595
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_7595 7595 14913 14921
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_goal7595_rel initSM initPM hSM hPM hInit)

private theorem l2d_add4919_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4919)
      (denoteGraphDistributed pm initPM 8211) (denoteGraphDistributed pm initPM 8212)
      [4096, 1024] [2048, 1024] := by
  have ha := l2d_goal7595_rel initSM initPM hSM hPM hInit
  have hb := l2d_float4918_rel initSM initPM hSM hPM hInit
  have rs := l2d_add sm initSM 171 0 7595 4918 4919 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_add pm initPM 403 0 14913 8207 8211 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_add pm initPM 404 1 14921 8208 8212 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, ha.value, hb.value,
      fw_add_allGather0_commute_2_2048_1024 _ _ _ _ ha.shard0_shape ha.shard1_shape
        hb.shard0_shape hb.shard1_shape, r0, r1]
  · rw [rs]; exact elemwiseAdd_shape_of_shapes _ _ [4096, 1024] ha.full_shape hb.full_shape
  · rw [r0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] ha.shard0_shape hb.shard0_shape
  · rw [r1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] ha.shard1_shape hb.shard1_shape

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 residual add. -/
theorem recon_intermediateGoal_4919_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4919
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4919 4919 8211 8212
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_add4919_rel initSM initPM hSM hPM hInit)

/-! ### Layer-5 router entrance (pure distributed evaluator) -/

private theorem l2d_rms4921_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4921)
      (denoteGraphDistributed pm initPM 8215) (denoteGraphDistributed pm initPM 8216)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_add4919_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 172
    { rank := 0, op := "OpName.FW_multiref", ins := [4919], outs := [7612, 7616], params := [2] }
    4919 7612 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out sm st 0 4919 7612 7616)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 405
    { rank := 0, op := "OpName.FW_multiref", ins := [8211], outs := [14951, 14955], params := [2] }
    8211 14951 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 0 8211 14951 14955)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 406
    { rank := 1, op := "OpName.FW_multiref", ins := [8212], outs := [14959, 14963], params := [2] }
    8212 14959 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 1 8212 14959 14963)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4920
    (by native_decide) 4920 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have rs := l2d_rms sm initSM 173 0 7612 4920 4921 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_rms pm initPM 407 0 14951 4920 8215 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_rms pm initPM 408 1 14959 4920 8216 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 14951).shape = [2048, 1024] := by
    rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 14959).shape = [2048, 1024] := by
    rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs0 hs1,
      r0, r1]
  · rw [rs]; exact fw_rms_norm_shape2 _ _ 4096 1024 (by rw [s]; exact h.full_shape)
  · rw [r0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs0
  · rw [r1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs1

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 router RMSNorm. -/
theorem recon_intermediateGoal_4921_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4921
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4921 4921 8215 8216
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_rms4921_rel initSM initPM hSM hPM hInit)

private theorem l2d_float4922_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4922)
      (denoteGraphDistributed pm initPM 8217) (denoteGraphDistributed pm initPM 8218)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_rms4921_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 174
    { rank := 0, op := "OpName.FW_multiref", ins := [4921],
      outs := [7623, 7627, 7631, 7635, 7639], params := [5] }
    4921 7623 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref_first_out' sm st 0 4 4921 7623 [7627, 7631, 7635, 7639])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 409
    { rank := 0, op := "OpName.FW_multiref", ins := [8215],
      outs := [14970, 14974, 14978, 14982, 14986], params := [5] }
    8215 14970 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref_first_out' pm st 0 4 8215 14970 [14974, 14978, 14982, 14986])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 410
    { rank := 1, op := "OpName.FW_multiref", ins := [8216],
      outs := [14993, 14997, 15001, 15005, 15009], params := [5] }
    8216 14993 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref_first_out' pm st 1 4 8216 14993 [14997, 15001, 15005, 15009])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have rs := l2d_float sm initSM 175 0 7623 4922 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_float pm initPM 411 0 14970 8217 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_float pm initPM 415 1 14993 8218 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  exact ⟨by rw [rs, s, h.value, ← p0, ← p1, r0, r1],
    by rw [rs, s]; exact h.full_shape, by rw [r0, p0]; exact h.shard0_shape,
    by rw [r1, p1]; exact h.shard1_shape, by decide⟩

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 router float input. -/
theorem recon_intermediateGoal_4922_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4922
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4922 4922 8217 8218
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_float4922_rel initSM initPM hSM hPM hInit)

private theorem l2d_logits4924_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4924)
      (denoteGraphDistributed pm initPM 8223) (denoteGraphDistributed pm initPM 8224)
      [4096, 64] [2048, 64] := by
  have h := l2d_float4922_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4923
    (by native_decide) 4923 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4923
    (by native_decide) 4923 [64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4923).shape = [64, 1024] := by
    rw [← hw]; exact hws
  have rs := distributed_reduce2 sm initSM 179
    { rank := 0, op := "OpName.FW_norm_linear", ins := [4922, 4923], outs := [4924] }
    4922 4923 4924 fw_norm_linear (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_norm_linear_out sm st 0 4922 4923 4924)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce2 pm initPM 419
    { rank := 0, op := "OpName.FW_norm_linear", ins := [8217, 4923], outs := [8223] }
    8217 4923 8223 fw_norm_linear (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_norm_linear_out pm st 0 8217 4923 8223)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce2 pm initPM 423
    { rank := 1, op := "OpName.FW_norm_linear", ins := [8218, 4923], outs := [8224] }
    8218 4923 8224 fw_norm_linear (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_norm_linear_out pm st 1 8218 4923 8224)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw,
      fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64
        (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw,
      r0, r1]
  · rw [rs]; exact fw_norm_linear_2d_shape 4096 1024 64 _ _ (by decide) h.full_shape hws
  · rw [r0]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) h.shard0_shape hpw
  · rw [r1]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) h.shard1_shape hpw

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 router logits. -/
theorem recon_intermediateGoal_4924_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4924
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4924 4924 8223 8224
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl
    (l2d_logits4924_rel initSM initPM hSM hPM hInit)

private theorem l2d_topk4925_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4925)
      (denoteGraphDistributed pm initPM 8225) (denoteGraphDistributed pm initPM 8226)
      [4096, 64] [2048, 64] := by
  have h := l2d_logits4924_rel initSM initPM hSM hPM hInit
  let ss := (sm.nodes.take 183).foldl (applyNodeDistributed sm) initSM
  let p0s := (pm.nodes.take 427).foldl (applyNodeDistributed pm) initPM
  let p1s := (pm.nodes.take 431).foldl (applyNodeDistributed pm) initPM
  have es : ss 4924 = denoteGraphDistributed sm initSM 4924 :=
    foldl_take_distributed_eq sm initSM 4924 183 (by native_decide) (by native_decide)
  have e0 : p0s 8223 = denoteGraphDistributed pm initPM 8223 :=
    foldl_take_distributed_eq pm initPM 8223 427 (by native_decide) (by native_decide)
  have e1 : p1s 8224 = denoteGraphDistributed pm initPM 8224 :=
    foldl_take_distributed_eq pm initPM 8224 431 (by native_decide) (by native_decide)
  have hs : (ss 4924).shape.reverse.head? = some 64 := by rw [es, h.full_shape]; rfl
  have h0 : (p0s 8223).shape.reverse.head? = some 64 := by rw [e0, h.shard0_shape]; rfl
  have h1 : (p1s 8224).shape.reverse.head? = some 64 := by rw [e1, h.shard1_shape]; rfl
  have rs := distributed_reduce_fixed_one sm initSM 183
    { rank := 0, op := "OpName.FW_topk_routing", ins := [4924], outs := [4925, 4926, 4927], params := [8, 1] }
    4924 4925 (fun t => (fw_topk_routing t 8 64).1)
    (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_fst sm ss 0 4924 4925 4926 4927 hs)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce_fixed_one pm initPM 427
    { rank := 0, op := "OpName.FW_topk_routing", ins := [8223], outs := [8225, 8227, 8229], params := [8, 1] }
    8223 8225 (fun t => (fw_topk_routing t 8 64).1)
    (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_fst pm p0s 0 8223 8225 8227 8229 h0)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce_fixed_one pm initPM 431
    { rank := 1, op := "OpName.FW_topk_routing", ins := [8224], outs := [8226, 8228, 8230], params := [8, 1] }
    8224 8226 (fun t => (fw_topk_routing t 8 64).1)
    (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_fst pm p1s 1 8224 8226 8228 8230 h1)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value,
      fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64
        (by omega) (by omega) h.shard0_shape h.shard1_shape, r0, r1]
  · rw [rs]; exact fw_topk_routing_fst_shape _ 8 64 4096 (by rw [h.full_shape]; rfl)
  · rw [r0]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h.shard0_shape]; rfl)
  · rw [r1]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h.shard1_shape]; rfl)

/-- Public pure-distributed exact 2-TP reconstruction of layer-5 routing probabilities. -/
theorem recon_intermediateGoal_4925_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4925
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4925 4925 8225 8226
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl
    (l2d_topk4925_rel initSM initPM hSM hPM hInit)

private theorem l2d_topk4926_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4926)
      (denoteGraphDistributed pm initPM 8227) (denoteGraphDistributed pm initPM 8228)
      [4096, 64] [2048, 64] := by
  have h := l2d_logits4924_rel initSM initPM hSM hPM hInit
  let ss := (sm.nodes.take 183).foldl (applyNodeDistributed sm) initSM
  let p0s := (pm.nodes.take 427).foldl (applyNodeDistributed pm) initPM
  let p1s := (pm.nodes.take 431).foldl (applyNodeDistributed pm) initPM
  have es : ss 4924 = denoteGraphDistributed sm initSM 4924 :=
    foldl_take_distributed_eq sm initSM 4924 183 (by native_decide) (by native_decide)
  have e0 : p0s 8223 = denoteGraphDistributed pm initPM 8223 :=
    foldl_take_distributed_eq pm initPM 8223 427 (by native_decide) (by native_decide)
  have e1 : p1s 8224 = denoteGraphDistributed pm initPM 8224 :=
    foldl_take_distributed_eq pm initPM 8224 431 (by native_decide) (by native_decide)
  have hs : (ss 4924).shape.reverse.head? = some 64 := by rw [es, h.full_shape]; rfl
  have h0 : (p0s 8223).shape.reverse.head? = some 64 := by rw [e0, h.shard0_shape]; rfl
  have h1 : (p1s 8224).shape.reverse.head? = some 64 := by rw [e1, h.shard1_shape]; rfl
  have rs := distributed_reduce_fixed_one sm initSM 183
    { rank := 0, op := "OpName.FW_topk_routing", ins := [4924], outs := [4925, 4926, 4927], params := [8, 1] }
    4924 4926 (fun t => (fw_topk_routing t 8 64).2.1)
    (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_snd sm ss 0 4924 4925 4926 4927 (by decide) hs)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce_fixed_one pm initPM 427
    { rank := 0, op := "OpName.FW_topk_routing", ins := [8223], outs := [8225, 8227, 8229], params := [8, 1] }
    8223 8227 (fun t => (fw_topk_routing t 8 64).2.1)
    (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_snd pm p0s 0 8223 8225 8227 8229 (by decide) h0)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce_fixed_one pm initPM 431
    { rank := 1, op := "OpName.FW_topk_routing", ins := [8224], outs := [8226, 8228, 8230], params := [8, 1] }
    8224 8228 (fun t => (fw_topk_routing t 8 64).2.1)
    (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_snd pm p1s 1 8224 8226 8228 8230 (by decide) h1)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value,
      fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 8 64
        (by omega) (by omega) h.shard0_shape h.shard1_shape, r0, r1]
  · rw [rs]; exact fw_topk_routing_snd_shape _ 8 64 4096 (by rw [h.full_shape]; rfl)
  · rw [r0]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [h.shard0_shape]; rfl)
  · rw [r1]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [h.shard1_shape]; rfl)

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 routing map. -/
theorem recon_intermediateGoal_4926_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4926
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4926 4926 8227 8228
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl
    (l2d_topk4926_rel initSM initPM hSM hPM hInit)

private theorem l2d_token7627_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7627)
      (denoteGraphDistributed pm initPM 14974) (denoteGraphDistributed pm initPM 14997)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_rms4921_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 174
    { rank := 0, op := "OpName.FW_multiref", ins := [4921],
      outs := [7623, 7627, 7631, 7635, 7639], params := [5] }
    4921 7627 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos1_out sm st 0 4921 7623 7627 7631 7635 7639
      (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 409
    { rank := 0, op := "OpName.FW_multiref", ins := [8215],
      outs := [14970, 14974, 14978, 14982, 14986], params := [5] }
    8215 14974 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos1_out pm st 0 8215 14970 14974 14978 14982 14986
      (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 410
    { rank := 1, op := "OpName.FW_multiref", ins := [8216],
      outs := [14993, 14997, 15001, 15005, 15009], params := [5] }
    8216 14997 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos1_out pm st 1 8216 14993 14997 15001 15005 15009
      (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  exact ⟨by rw [s, h.value, ← p0, ← p1], by rw [s]; exact h.full_shape,
    by rw [p0]; exact h.shard0_shape, by rw [p1]; exact h.shard1_shape, by decide⟩

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 MoE token input. -/
theorem recon_intermediateGoal_7627_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7627
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_7627 7627 14974 14997
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_token7627_rel initSM initPM hSM hPM hInit)

private def layer5SmMoe : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [7627, 4925, 4926, 4928, 4929], outs := [4930], params := [64, 0, 64, 8] }
private def layer5PmMoe0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [14974, 8225, 8227, 8231, 8233], outs := [8235], params := [64, 0, 32, 8] }
private def layer5PmMoe1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm",
    ins := [14997, 8226, 8228, 8232, 8234], outs := [8236], params := [64, 32, 64, 8] }

set_option maxRecDepth 1000000 in
private theorem layer5_sm_node187 : sm.nodes[187]'(by native_decide) = layer5SmMoe := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer5_pm_node435 : pm.nodes[435]'(by native_decide) = layer5PmMoe0 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer5_pm_node438 : pm.nodes[438]'(by native_decide) = layer5PmMoe1 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer5_sm_buddies : sm.replicaBuddies layer5SmMoe = [layer5SmMoe] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer5_pm_buddies0 :
    pm.replicaBuddies layer5PmMoe0 = [layer5PmMoe0, layer5PmMoe1] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer5_pm_buddies1 :
    pm.replicaBuddies layer5PmMoe1 = [layer5PmMoe0, layer5PmMoe1] := by native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
/-- Pure-distributed full-expert reconstruction of the layer-5 MoE boundary. -/
theorem recon_intermediateGoal_4930_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4930
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have hi := l2d_token7627_rel initSM initPM hSM hPM hInit
  have hrp := l2d_topk4925_rel initSM initPM hSM hPM hInit
  have hrm := l2d_topk4926_rel initSM initPM hSM hPM hInit

  have hW13 := hInit initGoal_4928 (by native_decide)
  have hW2 := hInit initGoal_4929 (by native_decide)
  have hsW13 := hW13.2.1
  have hsW2 := hW2.2.1
  simp only [initGoal_4928, List.map, List.cons.injEq, and_true] at hsW13
  simp only [initGoal_4929, List.map, List.cons.injEq, and_true] at hsW2
  have hsW13A : (denoteGraphDistributed pm initPM 8231).shape = [32, 1024, 1024] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8231
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW13.1
  have hsW13B : (denoteGraphDistributed pm initPM 8232).shape = [32, 1024, 1024] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8232
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW13.2
  have hsW2A : (denoteGraphDistributed pm initPM 8233).shape = [32, 1024, 512] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8233
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW2.1
  have hsW2B : (denoteGraphDistributed pm initPM 8234).shape = [32, 1024, 512] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8234
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW2.2
  have hbrW13 : denoteGraphDistributed sm initSM 4928 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 8231, denoteGraphDistributed pm initPM 8232] := by
    have hv := hW13.2.2
    rw [reconstructForGoal_of_not_replicated initGoal_4928 pm.numRanks _ rfl] at hv
    simp only [initGoal_4928, List.map] at hv
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
      (by rw [hsW13.1]; decide)] at hv
    have ds : denoteGraphDistributed sm initSM 4928 = initSM 4928 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written sm sm.nodes initSM 4928
        layer1_sm_nodes_nonempty (by native_decide)
    have dp0 : denoteGraphDistributed pm initPM 8231 = initPM 8231 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8231
        layer1_pm_nodes_nonempty (by native_decide)
    have dp1 : denoteGraphDistributed pm initPM 8232 = initPM 8232 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8232
        layer1_pm_nodes_nonempty (by native_decide)
    rw [ds, dp0, dp1]
    exact hv
  have hbrW2 : denoteGraphDistributed sm initSM 4929 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 8233, denoteGraphDistributed pm initPM 8234] := by
    have hv := hW2.2.2
    rw [reconstructForGoal_of_not_replicated initGoal_4929 pm.numRanks _ rfl] at hv
    simp only [initGoal_4929, List.map] at hv
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
      (by rw [hsW2.1]; decide)] at hv
    have ds : denoteGraphDistributed sm initSM 4929 = initSM 4929 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written sm sm.nodes initSM 4929
        layer1_sm_nodes_nonempty (by native_decide)
    have dp0 : denoteGraphDistributed pm initPM 8233 = initPM 8233 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8233
        layer1_pm_nodes_nonempty (by native_decide)
    have dp1 : denoteGraphDistributed pm initPM 8234 = initPM 8234 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8234
        layer1_pm_nodes_nonempty (by native_decide)
    rw [ds, dp0, dp1]
    exact hv
  have hW13single : allGatherPrimDimN 0 1 0 [denoteGraphDistributed sm initSM 4928] =
      denoteGraphDistributed sm initSM 4928 := by
    have hs : (denoteGraphDistributed sm initSM 4928).shape = [64, 1024, 1024] := by
      rw [hbrW13, allGatherPrimDimN_shape 0 2 _ [32, 1024, 1024] (by simp [hsW13A])]
      simp [List.set]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hs]; decide)
  have hW2single : allGatherPrimDimN 0 1 0 [denoteGraphDistributed sm initSM 4929] =
      denoteGraphDistributed sm initSM 4929 := by
    have hs : (denoteGraphDistributed sm initSM 4929).shape = [64, 1024, 512] := by
      rw [hbrW2, allGatherPrimDimN_shape 0 2 _ [32, 1024, 512] (by simp [hsW2A])]
      simp [List.set]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hs]; decide)

  have hSMout : denoteGraphDistributed sm initSM 4930 =
      fw_all2all_moe_gmm_full (denoteGraphDistributed sm initSM 7627)
        (denoteGraphDistributed sm initSM 4925) (denoteGraphDistributed sm initSM 4926)
        [denoteGraphDistributed pm initPM 8231, denoteGraphDistributed pm initPM 8232]
        [denoteGraphDistributed pm initPM 8233, denoteGraphDistributed pm initPM 8234]
        64 8 (((10 : Nat) : Scalar)) := by
    have hk : 187 < sm.nodes.length := by native_decide
    rw [distributed_moe_reduce sm initSM 187 layer5SmMoe 4930 hk
      (show sm.nodes[187]'hk = layer5SmMoe from layer5_sm_node187)
      rfl rfl (by native_decide) (by native_decide)]
    unfold applyNodeFullExpertMoE_value
    rw [layer5_sm_buddies]
    simp only [layer5SmMoe, List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    rw [foldl_take_distributed_eq sm initSM 7627 187 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 4925 187 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 4926 187 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 4928 187 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 4929 187 (by native_decide) (by native_decide)]
    unfold fw_all2all_moe_gmm_full
    simp only [List.length_cons, List.length_nil]
    rw [hW13single, hW2single, hbrW13, hbrW2]
  have hP0 : denoteGraphDistributed pm initPM 8235 =
      fw_all2all_moe_gmm_full (denoteGraphDistributed pm initPM 14974)
        (denoteGraphDistributed pm initPM 8225) (denoteGraphDistributed pm initPM 8227)
        [denoteGraphDistributed pm initPM 8231, denoteGraphDistributed pm initPM 8232]
        [denoteGraphDistributed pm initPM 8233, denoteGraphDistributed pm initPM 8234]
        64 8 (((10 : Nat) : Scalar)) := by
    have hk : 435 < pm.nodes.length := by native_decide
    rw [distributed_moe_reduce pm initPM 435 layer5PmMoe0 8235 hk
      (show pm.nodes[435]'hk = layer5PmMoe0 from layer5_pm_node435)
      rfl rfl (by native_decide) (by native_decide)]
    unfold applyNodeFullExpertMoE_value
    rw [layer5_pm_buddies0]
    simp only [layer5PmMoe0, layer5PmMoe1, List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    rw [foldl_take_distributed_eq pm initPM 14974 435 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8225 435 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8227 435 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8231 435 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8232 435 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8233 435 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8234 435 (by native_decide) (by native_decide)]
  have hP1 : denoteGraphDistributed pm initPM 8236 =
      fw_all2all_moe_gmm_full (denoteGraphDistributed pm initPM 14997)
        (denoteGraphDistributed pm initPM 8226) (denoteGraphDistributed pm initPM 8228)
        [denoteGraphDistributed pm initPM 8231, denoteGraphDistributed pm initPM 8232]
        [denoteGraphDistributed pm initPM 8233, denoteGraphDistributed pm initPM 8234]
        64 8 (((10 : Nat) : Scalar)) := by
    have hk : 438 < pm.nodes.length := by native_decide
    rw [distributed_moe_reduce pm initPM 438 layer5PmMoe1 8236 hk
      (show pm.nodes[438]'hk = layer5PmMoe1 from layer5_pm_node438)
      rfl rfl (by native_decide) (by native_decide)]
    unfold applyNodeFullExpertMoE_value
    rw [layer5_pm_buddies1]
    simp only [layer5PmMoe0, layer5PmMoe1, List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    rw [foldl_take_distributed_eq pm initPM 14997 438 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8226 438 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8228 438 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8231 438 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8232 438 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8233 438 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8234 438 (by native_decide) (by native_decide)]

  have hc := fw_all2all_moe_gmm_full_split_commute_2
    (denoteGraphDistributed pm initPM 14974) (denoteGraphDistributed pm initPM 14997)
    (denoteGraphDistributed pm initPM 8225) (denoteGraphDistributed pm initPM 8226)
    (denoteGraphDistributed pm initPM 8227) (denoteGraphDistributed pm initPM 8228)
    (denoteGraphDistributed pm initPM 8231) (denoteGraphDistributed pm initPM 8232)
    (denoteGraphDistributed pm initPM 8233) (denoteGraphDistributed pm initPM 8234)
    2048 1024 32 8 1024 512 (((10 : Nat) : Scalar))
    (by omega) (by omega) (by omega) (by omega) (by omega) rfl
    hi.shard0_shape hi.shard1_shape hrp.shard0_shape hrp.shard1_shape
    hrm.shard0_shape hrm.shard1_shape hsW13A hsW13B hsW2A hsW2B
  have hval : denoteGraphDistributed sm initSM 4930 = allGatherPrimDimN 0 pm.numRanks 0
      [denoteGraphDistributed pm initPM 8235, denoteGraphDistributed pm initPM 8236] := by
    rw [hSMout, hi.value, hrp.value, hrm.value, hc, ← hP0, ← hP1,
      show pm.numRanks = 2 from rfl]
  have hsP0 : (denoteGraphDistributed pm initPM 8235).shape = [2048, 1024] := by
    rw [hP0]
    exact fw_all2all_moe_gmm_full_shape
      (input := denoteGraphDistributed pm initPM 14974)
      (rp := denoteGraphDistributed pm initPM 8225)
      (rm := denoteGraphDistributed pm initPM 8227)
      (w13s := [denoteGraphDistributed pm initPM 8231, denoteGraphDistributed pm initPM 8232])
      (w2s := [denoteGraphDistributed pm initPM 8233, denoteGraphDistributed pm initPM 8234])
      (numExp := 64) (topK := 8) (swigluLimit := (((10 : Nat) : Scalar)))
      (lDim := 2048) (hModel := 1024)
      (by rw [hi.shard0_shape]; rfl) (by rw [hi.shard0_shape]; rfl)
  have hsP1 : (denoteGraphDistributed pm initPM 8236).shape = [2048, 1024] := by
    rw [hP1]
    exact fw_all2all_moe_gmm_full_shape
      (input := denoteGraphDistributed pm initPM 14997)
      (rp := denoteGraphDistributed pm initPM 8226)
      (rm := denoteGraphDistributed pm initPM 8228)
      (w13s := [denoteGraphDistributed pm initPM 8231, denoteGraphDistributed pm initPM 8232])
      (w2s := [denoteGraphDistributed pm initPM 8233, denoteGraphDistributed pm initPM 8234])
      (numExp := 64) (topK := 8) (swigluLimit := (((10 : Nat) : Scalar)))
      (lDim := 2048) (hModel := 1024)
      (by rw [hi.shard1_shape]; rfl) (by rw [hi.shard1_shape]; rfl)
  have hsSM : (denoteGraphDistributed sm initSM 4930).shape = [4096, 1024] := by
    rw [hval, show pm.numRanks = 2 from rfl,
      allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsP0])]
    simp [List.set]
  exact wrap_2tp_allGather_gen _ _ intermediateGoal_4930 4930 8235 8236
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    hval hsSM hsP0 hsP1

/-! ### Layer-5 gate/expert side branches (pure distributed evaluator) -/

private theorem l2d_l5_expert_reshape
    (full shard0 shard1 mid mid0 mid1 out out0 out1 : Tensor)
    (h : Gather2Rel full shard0 shard1 [4096, 1024] [2048, 1024])
    (s : mid = full) (p0 : mid0 = shard0) (p1 : mid1 = shard1)
    (rs : out = fw_view [4096, 1024] mid)
    (r0 : out0 = fw_view [2048, 1024] mid0)
    (r1 : out1 = fw_view [2048, 1024] mid1) :
    Gather2Rel out out0 out1 [4096, 1024] [2048, 1024] := by
  have es : out = mid := by rw [rs, fw_view_id_shape [4096, 1024] _ (by rw [s]; exact h.full_shape)]
  have e0 : out0 = mid0 := by rw [r0, fw_view_id_shape [2048, 1024] _ (by rw [p0]; exact h.shard0_shape)]
  have e1 : out1 = mid1 := by rw [r1, fw_view_id_shape [2048, 1024] _ (by rw [p1]; exact h.shard1_shape)]
  exact ⟨by rw [es, s, h.value, ← p0, ← p1, ← e0, ← e1],
    by rw [es, s]; exact h.full_shape, by rw [e0, p0]; exact h.shard0_shape,
    by rw [e1, p1]; exact h.shard1_shape, by decide⟩

private theorem l2d_l5_expert_linear (width : Nat)
    (x x0 x1 w out out0 out1 : Tensor)
    (h : Gather2Rel x x0 x1 [4096, 1024] [2048, 1024])
    (hws : w.shape = [width, 1024])
    (rs : out = fw_linear x w) (r0 : out0 = fw_linear x0 w) (r1 : out1 = fw_linear x1 w)
    (hwpos : 0 < width) : Gather2Rel out out0 out1 [4096, width] [2048, width] := by
  refine ⟨?_, ?_, ?_, ?_, by
    intro heq
    have := congrArg List.length heq
    norm_num at this⟩
  · rw [rs, h.value, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 width
      (by omega) (by omega) hwpos h.shard0_shape h.shard1_shape hws, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 width _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 width _ _ h.shard0_shape hws
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 width _ _ h.shard1_shape hws

private theorem l2d_l5_expert_view (width : Nat)
    (x x0 x1 out out0 out1 : Tensor)
    (h : Gather2Rel x x0 x1 [4096, width] [2048, width])
    (rs : out = fw_view [4096, width] x)
    (r0 : out0 = fw_view [2048, width] x0)
    (r1 : out1 = fw_view [2048, width] x1) :
    Gather2Rel out out0 out1 [4096, width] [2048, width] := by
  have es : out = x := by rw [rs, fw_view_id_shape [4096, width] _ h.full_shape]
  have e0 : out0 = x0 := by rw [r0, fw_view_id_shape [2048, width] _ h.shard0_shape]
  have e1 : out1 = x1 := by rw [r1, fw_view_id_shape [2048, width] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by
      intro heq
      have := congrArg List.length heq
      norm_num at this⟩

private theorem l2d_reshape4931_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4931)
      (denoteGraphDistributed pm initPM 8237) (denoteGraphDistributed pm initPM 8238)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_rms4921_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 174
    { rank := 0, op := "OpName.FW_multiref", ins := [4921], outs := [7623, 7627, 7631, 7635, 7639], params := [5] }
    4921 7631 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos2_out sm st 0 4921 7623 7627 7631 7635 7639 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 409
    { rank := 0, op := "OpName.FW_multiref", ins := [8215], outs := [14970, 14974, 14978, 14982, 14986], params := [5] }
    8215 14978 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos2_out pm st 0 8215 14970 14974 14978 14982 14986 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 410
    { rank := 1, op := "OpName.FW_multiref", ins := [8216], outs := [14993, 14997, 15001, 15005, 15009], params := [5] }
    8216 15001 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos2_out pm st 1 8216 14993 14997 15001 15005 15009 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  exact l2d_l5_expert_reshape _ _ _ _ _ _ _ _ _ h s p0 p1
    (l2d_reshape sm initSM 176 0 7631 4931 4096 [1024] (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (l2d_reshape pm initPM 412 0 14978 8237 2048 [1024] (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (l2d_reshape pm initPM 416 1 15001 8238 2048 [1024] (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))

private theorem l2d_reshape4936_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4936)
      (denoteGraphDistributed pm initPM 8251) (denoteGraphDistributed pm initPM 8252)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_rms4921_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 174
    { rank := 0, op := "OpName.FW_multiref", ins := [4921], outs := [7623, 7627, 7631, 7635, 7639], params := [5] }
    4921 7635 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos3_out sm st 0 4921 7623 7627 7631 7635 7639 (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 409
    { rank := 0, op := "OpName.FW_multiref", ins := [8215], outs := [14970, 14974, 14978, 14982, 14986], params := [5] }
    8215 14982 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos3_out pm st 0 8215 14970 14974 14978 14982 14986 (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 410
    { rank := 1, op := "OpName.FW_multiref", ins := [8216], outs := [14993, 14997, 15001, 15005, 15009], params := [5] }
    8216 15005 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos3_out pm st 1 8216 14993 14997 15001 15005 15009 (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  exact l2d_l5_expert_reshape _ _ _ _ _ _ _ _ _ h s p0 p1
    (l2d_reshape sm initSM 177 0 7635 4936 4096 [1024] (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (l2d_reshape pm initPM 413 0 14982 8251 2048 [1024] (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (l2d_reshape pm initPM 417 1 15005 8252 2048 [1024] (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))

private theorem l2d_reshape4940_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4940)
      (denoteGraphDistributed pm initPM 8269) (denoteGraphDistributed pm initPM 8270)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_rms4921_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 174
    { rank := 0, op := "OpName.FW_multiref", ins := [4921], outs := [7623, 7627, 7631, 7635, 7639], params := [5] }
    4921 7639 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos4_out sm st 0 4921 7623 7627 7631 7635 7639 (by decide) (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 409
    { rank := 0, op := "OpName.FW_multiref", ins := [8215], outs := [14970, 14974, 14978, 14982, 14986], params := [5] }
    8215 14986 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos4_out pm st 0 8215 14970 14974 14978 14982 14986 (by decide) (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 410
    { rank := 1, op := "OpName.FW_multiref", ins := [8216], outs := [14993, 14997, 15001, 15005, 15009], params := [5] }
    8216 15009 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos4_out pm st 1 8216 14993 14997 15001 15005 15009 (by decide) (by decide) (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  exact l2d_l5_expert_reshape _ _ _ _ _ _ _ _ _ h s p0 p1
    (l2d_reshape sm initSM 178 0 7639 4940 4096 [1024] (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (l2d_reshape pm initPM 414 0 14986 8269 2048 [1024] (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (l2d_reshape pm initPM 418 1 15009 8270 2048 [1024] (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))

/-- Public pure-distributed exact 2-TP reconstructions of the three layer-5 expert inputs. -/
theorem recon_intermediateGoal_4931_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4931 (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4931 4931 8237 8238 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (l2d_reshape4931_rel initSM initPM hSM hPM hInit)

theorem recon_intermediateGoal_4936_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4936 (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4936 4936 8251 8252 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (l2d_reshape4936_rel initSM initPM hSM hPM hInit)

theorem recon_intermediateGoal_4940_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4940 (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4940 4940 8269 8270 [4096, 1024] [2048, 1024]
    rfl rfl rfl rfl rfl rfl (l2d_reshape4940_rel initSM initPM hSM hPM hInit)

private theorem l2d_linear4933_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4933) (denoteGraphDistributed pm initPM 8241)
      (denoteGraphDistributed pm initPM 8242) [4096, 1] [2048, 1] := by
  have h := l2d_reshape4931_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4932 (by native_decide) 4932
    rfl rfl rfl rfl layer1_sm_nodes_nonempty (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4932 (by native_decide) 4932
    [1, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  apply l2d_l5_expert_linear 1 _ _ _ (denoteGraphDistributed pm initPM 4932) _ _ _ h
    (by rw [← hw]; exact hws)
  · rw [l2d_linear sm initSM 180 0 4931 4932 4933 (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide), hw]
  · exact l2d_linear pm initPM 420 0 8237 4932 8241 (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  · exact l2d_linear pm initPM 424 1 8238 4932 8242 (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  · omega

private theorem l2d_linear4938_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4938) (denoteGraphDistributed pm initPM 8255)
      (denoteGraphDistributed pm initPM 8256) [4096, 512] [2048, 512] := by
  have h := l2d_reshape4936_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4937 (by native_decide) 4937
    rfl rfl rfl rfl layer1_sm_nodes_nonempty (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4937 (by native_decide) 4937
    [512, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  apply l2d_l5_expert_linear 512 _ _ _ (denoteGraphDistributed pm initPM 4937) _ _ _ h
    (by rw [← hw]; exact hws)
  · rw [l2d_linear sm initSM 181 0 4936 4937 4938 (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide), hw]
  · exact l2d_linear pm initPM 421 0 8251 4937 8255 (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  · exact l2d_linear pm initPM 425 1 8252 4937 8256 (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  · omega

private theorem l2d_linear4942_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4942) (denoteGraphDistributed pm initPM 8273)
      (denoteGraphDistributed pm initPM 8274) [4096, 512] [2048, 512] := by
  have h := l2d_reshape4940_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4941 (by native_decide) 4941
    rfl rfl rfl rfl layer1_sm_nodes_nonempty (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4941 (by native_decide) 4941
    [512, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  apply l2d_l5_expert_linear 512 _ _ _ (denoteGraphDistributed pm initPM 4941) _ _ _ h
    (by rw [← hw]; exact hws)
  · rw [l2d_linear sm initSM 182 0 4940 4941 4942 (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide), hw]
  · exact l2d_linear pm initPM 422 0 8269 4941 8273 (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  · exact l2d_linear pm initPM 426 1 8270 4941 8274 (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  · omega

/-- Public pure-distributed exact 2-TP layer-5 expert linear reconstructions. -/
theorem recon_intermediateGoal_4933_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4933 (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4933 4933 8241 8242 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (l2d_linear4933_rel initSM initPM hSM hPM hInit)

theorem recon_intermediateGoal_4938_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4938 (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4938 4938 8255 8256 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (l2d_linear4938_rel initSM initPM hSM hPM hInit)

theorem recon_intermediateGoal_4942_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4942 (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4942 4942 8273 8274 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (l2d_linear4942_rel initSM initPM hSM hPM hInit)

private theorem l2d_view4934_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4934) (denoteGraphDistributed pm initPM 8247)
      (denoteGraphDistributed pm initPM 8248) [4096, 1] [2048, 1] :=
  l2d_l5_expert_view 1 _ _ _ _ _ _ (l2d_linear4933_rel initSM initPM hSM hPM hInit)
    (l2d_view sm initSM 184 0 4933 4934 4096 [1] (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (l2d_view pm initPM 428 0 8241 8247 2048 [1] (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (l2d_view pm initPM 432 1 8242 8248 2048 [1] (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))

private theorem l2d_view4939_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4939) (denoteGraphDistributed pm initPM 8265)
      (denoteGraphDistributed pm initPM 8266) [4096, 512] [2048, 512] :=
  l2d_l5_expert_view 512 _ _ _ _ _ _ (l2d_linear4938_rel initSM initPM hSM hPM hInit)
    (l2d_view sm initSM 185 0 4938 4939 4096 [512] (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (l2d_view pm initPM 429 0 8255 8265 2048 [512] (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (l2d_view pm initPM 433 1 8256 8266 2048 [512] (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))

private theorem l2d_view4943_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4943) (denoteGraphDistributed pm initPM 8283)
      (denoteGraphDistributed pm initPM 8284) [4096, 512] [2048, 512] :=
  l2d_l5_expert_view 512 _ _ _ _ _ _ (l2d_linear4942_rel initSM initPM hSM hPM hInit)
    (l2d_view sm initSM 186 0 4942 4943 4096 [512] (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (l2d_view pm initPM 430 0 8273 8283 2048 [512] (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (l2d_view pm initPM 434 1 8274 8284 2048 [512] (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))

/-- Public pure-distributed exact 2-TP layer-5 expert view reconstructions. -/
theorem recon_intermediateGoal_4934_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4934 (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4934 4934 8247 8248 [4096, 1] [2048, 1]
    rfl rfl rfl rfl rfl rfl (l2d_view4934_rel initSM initPM hSM hPM hInit)

theorem recon_intermediateGoal_4939_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4939 (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4939 4939 8265 8266 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (l2d_view4939_rel initSM initPM hSM hPM hInit)

theorem recon_intermediateGoal_4943_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4943 (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4943 4943 8283 8284 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (l2d_view4943_rel initSM initPM hSM hPM hInit)

/-! ### Layer-5 gate/expert postprocessing (pure distributed evaluator) -/

private theorem l2d_sigmoid4935_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4935)
      (denoteGraphDistributed pm initPM 8249) (denoteGraphDistributed pm initPM 8250)
      [4096, 1] [2048, 1] := by
  have h := l2d_view4934_rel initSM initPM hSM hPM hInit
  have rs := l2d_sigmoid sm initSM 188 0 4934 4935 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_sigmoid pm initPM 436 0 8247 8249 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_sigmoid pm initPM 439 1 8248 8250 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, fw_sigmoid_allGather0_commute_2 _ _ 2048 1
      (by omega) (by omega) h.shard0_shape h.shard1_shape, r0, r1]
  · rw [rs, fw_sigmoid_shape]; exact h.full_shape
  · rw [r0, fw_sigmoid_shape]; exact h.shard0_shape
  · rw [r1, fw_sigmoid_shape]; exact h.shard1_shape

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 sigmoid gate. -/
theorem recon_intermediateGoal_4935_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4935
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4935 4935 8249 8250
    [4096, 1] [2048, 1] rfl rfl rfl rfl rfl rfl
    (l2d_sigmoid4935_rel initSM initPM hSM hPM hInit)

private theorem l2d_swiglu4944_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4944)
      (denoteGraphDistributed pm initPM 8287) (denoteGraphDistributed pm initPM 8288)
      [4096, 512] [2048, 512] := by
  have hx := l2d_view4939_rel initSM initPM hSM hPM hInit
  have hy := l2d_view4943_rel initSM initPM hSM hPM hInit
  have rs := l2d_swiglu sm initSM 189 0 4939 4943 4944 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_swiglu pm initPM 437 0 8265 8283 8287 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_swiglu pm initPM 440 1 8266 8284 8288 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, hx.value, hy.value,
      fw_swiglu_allGather0_commute_2 _ _ _ _ 2048 512 (by omega) (by omega)
        hx.shard0_shape hx.shard1_shape hy.shard0_shape hy.shard1_shape, r0, r1]
  · rw [rs]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hy.full_shape
  · rw [r0]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hy.shard0_shape
  · rw [r1]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hy.shard1_shape

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 SwiGLU output. -/
theorem recon_intermediateGoal_4944_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4944
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4944 4944 8287 8288
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l2d_swiglu4944_rel initSM initPM hSM hPM hInit)

private theorem l2d_reshape4945_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4945)
      (denoteGraphDistributed pm initPM 8289) (denoteGraphDistributed pm initPM 8290)
      [4096, 512] [2048, 512] := by
  have h := l2d_swiglu4944_rel initSM initPM hSM hPM hInit
  exact l2d_l5_expert_view 512 _ _ _ _ _ _ h
    (l2d_reshape sm initSM 190 0 4944 4945 4096 [512] (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (l2d_reshape pm initPM 441 0 8287 8289 2048 [512] (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (l2d_reshape pm initPM 442 1 8288 8290 2048 [512] (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 identity reshape. -/
theorem recon_intermediateGoal_4945_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4945
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4945 4945 8289 8290
    [4096, 512] [2048, 512] rfl rfl rfl rfl rfl rfl
    (l2d_reshape4945_rel initSM initPM hSM hPM hInit)

private theorem l2d_linear4947_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4947)
      (denoteGraphDistributed pm initPM 8295) (denoteGraphDistributed pm initPM 8296)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_reshape4945_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4946
    (by native_decide) 4946 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4946
    (by native_decide) 4946 [1024, 512] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4946).shape = [1024, 512] := by
    rw [← hw]; exact hws
  have rs := l2d_linear sm initSM 191 0 4945 4946 4947 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_linear pm initPM 443 0 8289 4946 8295 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_linear pm initPM 444 1 8290 4946 8296 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw,
      fw_linear_allGather0_commute_2_of _ _ _ 2048 512 1024 (by omega) (by omega) (by omega)
        h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 512 1024 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 512 1024 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 512 1024 _ _ h.shard1_shape hpw

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 expert output linear. -/
theorem recon_intermediateGoal_4947_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4947
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4947 4947 8295 8296
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_linear4947_rel initSM initPM hSM hPM hInit)

private theorem l2d_view4948_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4948)
      (denoteGraphDistributed pm initPM 8305) (denoteGraphDistributed pm initPM 8306)
      [4096, 1024] [2048, 1024] :=
  l2d_l5_expert_view 1024 _ _ _ _ _ _ (l2d_linear4947_rel initSM initPM hSM hPM hInit)
    (l2d_view sm initSM 192 0 4947 4948 4096 [1024] (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (l2d_view pm initPM 445 0 8295 8305 2048 [1024] (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (l2d_view pm initPM 446 1 8296 8306 2048 [1024] (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 expert output view. -/
theorem recon_intermediateGoal_4948_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4948
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4948 4948 8305 8306
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_view4948_rel initSM initPM hSM hPM hInit)

private theorem l2d_mul4949_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4949)
      (denoteGraphDistributed pm initPM 8309) (denoteGraphDistributed pm initPM 8310)
      [4096, 1024] [2048, 1024] := by
  have hs := l2d_sigmoid4935_rel initSM initPM hSM hPM hInit
  have hv := l2d_view4948_rel initSM initPM hSM hPM hInit
  have rs := l2d_mul sm initSM 193 0 4935 4948 4949 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_mul pm initPM 447 0 8249 8305 8309 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_mul pm initPM 448 1 8250 8306 8310 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have mulShape : ∀ (x y : Tensor) (a : Nat),
      x.shape = [a, 1] → y.shape = [a, 1024] → (elemwiseMul x y).shape = [a, 1024] := by
    intro x y a hx hy
    show outShape2 x y = [a, 1024]
    unfold outShape2
    rw [hx, hy]
    show (max a a) :: (1024 : Nat) :: [] = [a, 1024]
    rw [Nat.max_self]
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, hs.value, hv.value,
      fw_mul_allGather0_commute_2_of_broadcast _ _ _ _ 2048 1024
        (by omega) (by omega) (by decide) (by decide) (by decide)
        hs.shard0_shape hs.shard1_shape hv.shard0_shape hv.shard1_shape, r0, r1]
  · rw [rs]; exact mulShape _ _ 4096 hs.full_shape hv.full_shape
  · rw [r0]; exact mulShape _ _ 2048 hs.shard0_shape hv.shard0_shape
  · rw [r1]; exact mulShape _ _ 2048 hs.shard1_shape hv.shard1_shape

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 broadcast gate product. -/
theorem recon_intermediateGoal_4949_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4949
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4949 4949 8309 8310
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_mul4949_rel initSM initPM hSM hPM hInit)

/-! ### Layer-5 post-MoE residual tail (pure distributed evaluator) -/

private theorem l2d_goal7616_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7616)
      (denoteGraphDistributed pm initPM 14955) (denoteGraphDistributed pm initPM 14963)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_add4919_rel initSM initPM hSM hPM hInit
  have rs := distributed_reduce1 sm initSM 172
    { rank := 0, op := "OpName.FW_multiref", ins := [4919], outs := [7612, 7616], params := [2] }
    4919 7616 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' sm st 0 4919 7612 7616 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce1 pm initPM 405
    { rank := 0, op := "OpName.FW_multiref", ins := [8211], outs := [14951, 14955], params := [2] }
    8211 14955 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 0 8211 14951 14955 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce1 pm initPM 406
    { rank := 1, op := "OpName.FW_multiref", ins := [8212], outs := [14959, 14963], params := [2] }
    8212 14963 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 1 8212 14959 14963 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rs r0 r1
  exact ⟨by rw [rs, h.value, r0, r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 pre-MoE residual carry. -/
theorem recon_intermediateGoal_7616_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7616
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_7616 7616 14955 14963
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_goal7616_rel initSM initPM hSM hPM hInit)

private theorem l2d_add4950_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4950)
      (denoteGraphDistributed pm initPM 8313) (denoteGraphDistributed pm initPM 8314)
      [4096, 1024] [2048, 1024] := by
  have ha := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_4930 4930 8235 8236
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4930_distributed initSM initPM hSM hPM hInit)
  have hb := l2d_mul4949_rel initSM initPM hSM hPM hInit
  have rs := l2d_add sm initSM 194 0 4930 4949 4950 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_add pm initPM 449 0 8235 8309 8313 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_add pm initPM 450 1 8236 8310 8314 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, ha.value, hb.value,
      fw_add_allGather0_commute_2_2048_1024 _ _ _ _ ha.shard0_shape ha.shard1_shape
        hb.shard0_shape hb.shard1_shape, r0, r1]
  · rw [rs]; exact elemwiseAdd_shape_of_shapes _ _ [4096, 1024] ha.full_shape hb.full_shape
  · rw [r0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] ha.shard0_shape hb.shard0_shape
  · rw [r1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] ha.shard1_shape hb.shard1_shape

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 post-MoE residual add. -/
theorem recon_intermediateGoal_4950_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4950
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4950 4950 8313 8314
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_add4950_rel initSM initPM hSM hPM hInit)

private theorem l2d_float4951_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4951)
      (denoteGraphDistributed pm initPM 8319) (denoteGraphDistributed pm initPM 8320)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_add4950_rel initSM initPM hSM hPM hInit
  have rs := l2d_float sm initSM 195 0 4950 4951 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_float pm initPM 451 0 8313 8319 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_float pm initPM 452 1 8314 8320 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  exact ⟨by rw [rs, h.value, r0, r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 post-MoE float. -/
theorem recon_intermediateGoal_4951_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4951
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4951 4951 8319 8320
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_float4951_rel initSM initPM hSM hPM hInit)

private theorem l2d_add4952_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4952)
      (denoteGraphDistributed pm initPM 8323) (denoteGraphDistributed pm initPM 8324)
      [4096, 1024] [2048, 1024] := by
  have ha := l2d_goal7616_rel initSM initPM hSM hPM hInit
  have hb := l2d_float4951_rel initSM initPM hSM hPM hInit
  have rs := l2d_add sm initSM 196 0 7616 4951 4952 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_add pm initPM 453 0 14955 8319 8323 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_add pm initPM 454 1 14963 8320 8324 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, ha.value, hb.value,
      fw_add_allGather0_commute_2_2048_1024 _ _ _ _ ha.shard0_shape ha.shard1_shape
        hb.shard0_shape hb.shard1_shape, r0, r1]
  · rw [rs]; exact elemwiseAdd_shape_of_shapes _ _ [4096, 1024] ha.full_shape hb.full_shape
  · rw [r0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] ha.shard0_shape hb.shard0_shape
  · rw [r1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] ha.shard1_shape hb.shard1_shape

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 cross-block residual add. -/
theorem recon_intermediateGoal_4952_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4952
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4952 4952 8323 8324
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_add4952_rel initSM initPM hSM hPM hInit)

/-! ### Layer-5 attention normalization and projections (pure distributed evaluator) -/

private theorem l2d_rms4954_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4954)
      (denoteGraphDistributed pm initPM 8327) (denoteGraphDistributed pm initPM 8328)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_add4952_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 197
    { rank := 0, op := "OpName.FW_multiref", ins := [4952], outs := [7643, 7647], params := [2] }
    4952 7643 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out sm st 0 4952 7643 7647)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 455
    { rank := 0, op := "OpName.FW_multiref", ins := [8323], outs := [15013, 15017], params := [2] }
    8323 15013 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 0 8323 15013 15017)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 456
    { rank := 1, op := "OpName.FW_multiref", ins := [8324], outs := [15021, 15025], params := [2] }
    8324 15021 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 1 8324 15021 15025)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4953
    (by native_decide) 4953 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have rs := l2d_rms sm initSM 198 0 7643 4953 4954 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_rms pm initPM 457 0 15013 4953 8327 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_rms pm initPM 458 1 15021 4953 8328 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15013).shape = [2048, 1024] := by
    rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15021).shape = [2048, 1024] := by
    rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs0 hs1,
      r0, r1]
  · rw [rs]; exact fw_rms_norm_shape2 _ _ 4096 1024 (by rw [s]; exact h.full_shape)
  · rw [r0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs0
  · rw [r1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs1

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 attention RMSNorm. -/
theorem recon_intermediateGoal_4954_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4954
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4954 4954 8327 8328
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_rms4954_rel initSM initPM hSM hPM hInit)

private theorem l2d_q4956_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4956)
      (denoteGraphDistributed pm initPM 8329) (denoteGraphDistributed pm initPM 8330)
      [4096, 16, 64] [2048, 16, 64] := by
  have h := l2d_rms4954_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 199
    { rank := 0, op := "OpName.FW_multiref", ins := [4954], outs := [7652, 7656, 7660], params := [3] }
    4954 7652 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' sm st 0 4954 7652 7656 7660)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 459
    { rank := 0, op := "OpName.FW_multiref", ins := [8327], outs := [15030, 15034, 15038], params := [3] }
    8327 15030 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' pm st 0 8327 15030 15034 15038)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 460
    { rank := 1, op := "OpName.FW_multiref", ins := [8328], outs := [15043, 15047, 15051], params := [3] }
    8328 15043 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' pm st 1 8328 15043 15047 15051)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4955
    (by native_decide) 4955 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4955
    (by native_decide) 4955 [16, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4955).shape = [16, 64, 1024] := by rw [← hw]; exact hws
  have rs := l2d_per_head_linear sm initSM 200 0 7652 4955 4956 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_per_head_linear pm initPM 461 0 15030 4955 8329 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_per_head_linear pm initPM 464 1 15043 4955 8330 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15030).shape = [2048, 1024] := by rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15043).shape = [2048, 1024] := by rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 16 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, r0, r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 16 64 (by rw [s]; exact h.full_shape) hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs0 hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs1 hpw

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 Q projection. -/
theorem recon_intermediateGoal_4956_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4956
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4956 4956 8329 8330
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl
    (l2d_q4956_rel initSM initPM hSM hPM hInit)

private theorem l2d_k4958_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4958)
      (denoteGraphDistributed pm initPM 8341) (denoteGraphDistributed pm initPM 8342)
      [4096, 4, 64] [2048, 4, 64] := by
  have h := l2d_rms4954_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 199
    { rank := 0, op := "OpName.FW_multiref", ins := [4954], outs := [7652, 7656, 7660], params := [3] }
    4954 7656 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' sm st 0 4954 7652 7656 7660 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 459
    { rank := 0, op := "OpName.FW_multiref", ins := [8327], outs := [15030, 15034, 15038], params := [3] }
    8327 15034 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' pm st 0 8327 15030 15034 15038 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 460
    { rank := 1, op := "OpName.FW_multiref", ins := [8328], outs := [15043, 15047, 15051], params := [3] }
    8328 15047 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' pm st 1 8328 15043 15047 15051 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4957
    (by native_decide) 4957 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4957
    (by native_decide) 4957 [4, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4957).shape = [4, 64, 1024] := by rw [← hw]; exact hws
  have rs := l2d_per_head_linear sm initSM 201 0 7656 4957 4958 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_per_head_linear pm initPM 462 0 15034 4957 8341 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_per_head_linear pm initPM 465 1 15047 4957 8342 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15034).shape = [2048, 1024] := by rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15047).shape = [2048, 1024] := by rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, r0, r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64 (by rw [s]; exact h.full_shape) hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs0 hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs1 hpw

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 K projection. -/
theorem recon_intermediateGoal_4958_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4958
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4958 4958 8341 8342
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l2d_k4958_rel initSM initPM hSM hPM hInit)

private theorem l2d_v4960_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4960)
      (denoteGraphDistributed pm initPM 8351) (denoteGraphDistributed pm initPM 8352)
      [4096, 4, 64] [2048, 4, 64] := by
  have h := l2d_rms4954_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 199
    { rank := 0, op := "OpName.FW_multiref", ins := [4954], outs := [7652, 7656, 7660], params := [3] }
    4954 7660 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' sm st 0 4954 7652 7656 7660 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 459
    { rank := 0, op := "OpName.FW_multiref", ins := [8327], outs := [15030, 15034, 15038], params := [3] }
    8327 15038 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' pm st 0 8327 15030 15034 15038 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 460
    { rank := 1, op := "OpName.FW_multiref", ins := [8328], outs := [15043, 15047, 15051], params := [3] }
    8328 15051 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' pm st 1 8328 15043 15047 15051 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4959
    (by native_decide) 4959 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4959
    (by native_decide) 4959 [4, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4959).shape = [4, 64, 1024] := by rw [← hw]; exact hws
  have rs := l2d_per_head_linear sm initSM 202 0 7660 4959 4960 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_per_head_linear pm initPM 463 0 15038 4959 8351 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_per_head_linear pm initPM 466 1 15051 4959 8352 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15038).shape = [2048, 1024] := by rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15051).shape = [2048, 1024] := by rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, r0, r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64 (by rw [s]; exact h.full_shape) hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs0 hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs1 hpw

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 V projection. -/
theorem recon_intermediateGoal_4960_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4960
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4960 4960 8351 8352
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l2d_v4960_rel initSM initPM hSM hPM hInit)

/-- Distributed cache agreement for the layer-5 PM rotary-cache replica. -/
private theorem l2d_rotary_cache_11858 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraphDistributed sm initSM 4691 = denoteGraphDistributed pm initPM 11858 := by
  have hsource := sm_pm_rotary_cache_agree initSM initPM hInit 11858 5 (by norm_num) rfl
  have hbase := distributed_init_singleton_value initSM initPM hInit initGoal_4691
    (by native_decide) 4691 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hcopy : denoteGraphDistributed pm initPM 11858 = id (denoteGraphDistributed pm initPM 4691) :=
    distributed_reduce1 pm initPM 14
      { rank := 1, op := "OpName.FW_multiref", ins := [4691],
        outs := (List.range 12).map (fun r => 11853 + r),
        params := [((List.range 12).map (fun r => 11853 + r)).length] }
      4691 11858 id (by native_decide) (by native_decide) (by decide)
      (fun s => by
        rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm s _ (by decide) (by decide)]
        rw [applyNode_fw_multiref_mem_out pm s 1 4691
          ((List.range 12).map (fun r => 11853 + r)) 11858 (by native_decide), id_eq])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  rw [hcopy, id_eq]
  exact hbase

set_option maxHeartbeats 8000000 in
-- Concrete graph reduction for both rotary outputs requires the larger elaboration budget.
private theorem l2d_rotary4962_4963_rels (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4962)
      (denoteGraphDistributed pm initPM 8363) (denoteGraphDistributed pm initPM 8364)
      [4096, 16, 64] [2048, 16, 64] ∧
    Gather2Rel (denoteGraphDistributed sm initSM 4963)
      (denoteGraphDistributed pm initPM 8365) (denoteGraphDistributed pm initPM 8366)
      [4096, 4, 64] [2048, 4, 64] := by
  have hq := l2d_q4956_rel initSM initPM hSM hPM hInit
  have hk := l2d_k4958_rel initSM initPM hSM hPM hInit
  have hcache := l2d_rotary_cache_11858 initSM initPM hInit
  have hpos := distributed_init_singleton_value initSM initPM hInit initGoal_4961
    (by native_decide) 4961 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hspos := distributed_init_singleton_shape initSM initPM hInit initGoal_4961
    (by native_decide) 4961 [4096] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have c0 := l2d_chunk pm initPM 5 0 4961 8361 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c1 := l2d_chunk pm initPM 18 1 4961 8362 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c0' : denoteGraphDistributed pm initPM 8361 = chunkPrimDimN 0 2 0 (denoteGraphDistributed pm initPM 4961) := c0
  have c1' : denoteGraphDistributed pm initPM 8362 = chunkPrimDimN 0 2 1 (denoteGraphDistributed pm initPM 4961) := c1
  have qSM : denoteGraphDistributed sm initSM 4962 =
      (fw_rotary_embedding (denoteGraphDistributed sm initSM 4691) (denoteGraphDistributed sm initSM 4961)
        (denoteGraphDistributed sm initSM 4956) (denoteGraphDistributed sm initSM 4958) 16 4).1 := by
    rw [distributed_node_core sm initSM 203
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4961, 4956, 4958], outs := [4962, 4963], params := [16, 4] }
      4962 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring sm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read sm initSM 203 4691 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 203 4961 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 203 4956 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 203 4958 (by native_decide) (by native_decide)]
  have kSM : denoteGraphDistributed sm initSM 4963 =
      (fw_rotary_embedding (denoteGraphDistributed sm initSM 4691) (denoteGraphDistributed sm initSM 4961)
        (denoteGraphDistributed sm initSM 4956) (denoteGraphDistributed sm initSM 4958) 16 4).2 := by
    rw [distributed_node_core sm initSM 203
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4961, 4956, 4958], outs := [4962, 4963], params := [16, 4] }
      4963 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring sm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 4691 4961 4956 4958 4962 4963 (by decide),
      distributed_prefix_read sm initSM 203 4691 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 203 4961 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 203 4956 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 203 4958 (by native_decide) (by native_decide)]
  have q0 : denoteGraphDistributed pm initPM 8363 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11858) (denoteGraphDistributed pm initPM 8361)
        (denoteGraphDistributed pm initPM 8329) (denoteGraphDistributed pm initPM 8341) 16 4).1 := by
    rw [distributed_node_core pm initPM 467
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11858, 8361, 8329, 8341], outs := [8363, 8365], params := [16, 4] }
      8363 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide), applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read pm initPM 467 11858 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 467 8361 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 467 8329 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 467 8341 (by native_decide) (by native_decide)]
  have k0 : denoteGraphDistributed pm initPM 8365 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11858) (denoteGraphDistributed pm initPM 8361)
        (denoteGraphDistributed pm initPM 8329) (denoteGraphDistributed pm initPM 8341) 16 4).2 := by
    rw [distributed_node_core pm initPM 467
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11858, 8361, 8329, 8341], outs := [8363, 8365], params := [16, 4] }
      8365 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11858 8361 8329 8341 8363 8365 (by decide),
      distributed_prefix_read pm initPM 467 11858 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 467 8361 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 467 8329 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 467 8341 (by native_decide) (by native_decide)]
  have q1 : denoteGraphDistributed pm initPM 8364 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11858) (denoteGraphDistributed pm initPM 8362)
        (denoteGraphDistributed pm initPM 8330) (denoteGraphDistributed pm initPM 8342) 16 4).1 := by
    rw [distributed_node_core pm initPM 468
      { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11858, 8362, 8330, 8342], outs := [8364, 8366], params := [16, 4] }
      8364 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide), applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read pm initPM 468 11858 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 468 8362 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 468 8330 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 468 8342 (by native_decide) (by native_decide)]
  have k1 : denoteGraphDistributed pm initPM 8366 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11858) (denoteGraphDistributed pm initPM 8362)
        (denoteGraphDistributed pm initPM 8330) (denoteGraphDistributed pm initPM 8342) 16 4).2 := by
    rw [distributed_node_core pm initPM 468
      { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11858, 8362, 8330, 8342], outs := [8364, 8366], params := [16, 4] }
      8366 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11858 8362 8330 8342 8364 8366 (by decide),
      distributed_prefix_read pm initPM 468 11858 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 468 8362 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 468 8330 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 468 8342 (by native_decide) (by native_decide)]
  have qval : denoteGraphDistributed sm initSM 4962 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 8363, denoteGraphDistributed pm initPM 8364] := by
    rw [qSM]; simp only [fw_rotary_embedding]
    rw [hq.value, fw_rotary_apply_allGather0_commute_2_1d (denoteGraphDistributed sm initSM 4691)
      (denoteGraphDistributed sm initSM 4961) (denoteGraphDistributed pm initPM 8329)
      (denoteGraphDistributed pm initPM 8330) 2048 16 64 (by omega) (by omega) (by omega)
      hspos hq.shard0_shape hq.shard1_shape, hcache, hpos, ← c0', ← c1', q0, q1]
    simp only [fw_rotary_embedding]
  have kval : denoteGraphDistributed sm initSM 4963 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 8365, denoteGraphDistributed pm initPM 8366] := by
    rw [kSM]; simp only [fw_rotary_embedding]
    rw [hk.value, fw_rotary_apply_allGather0_commute_2_1d (denoteGraphDistributed sm initSM 4691)
      (denoteGraphDistributed sm initSM 4961) (denoteGraphDistributed pm initPM 8341)
      (denoteGraphDistributed pm initPM 8342) 2048 4 64 (by omega) (by omega) (by omega)
      hspos hk.shard0_shape hk.shard1_shape, hcache, hpos, ← c0', ← c1', k0, k1]
    simp only [fw_rotary_embedding]
  have qs0 : (denoteGraphDistributed pm initPM 8363).shape = [2048, 16, 64] := by
    rw [q0]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hq.shard0_shape
  have qs1 : (denoteGraphDistributed pm initPM 8364).shape = [2048, 16, 64] := by
    rw [q1]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hq.shard1_shape
  have ks0 : (denoteGraphDistributed pm initPM 8365).shape = [2048, 4, 64] := by
    rw [k0]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hk.shard0_shape
  have ks1 : (denoteGraphDistributed pm initPM 8366).shape = [2048, 4, 64] := by
    rw [k1]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hk.shard1_shape
  refine ⟨⟨qval, ?_, qs0, qs1, by decide⟩, ⟨kval, ?_, ks0, ks1, by decide⟩⟩
  · rw [qval, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [qs0])]; rfl
  · rw [kval, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [ks0])]; rfl

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 rotary Q output. -/
theorem recon_intermediateGoal_4962_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4962
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4962 4962 8363 8364
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl
    (l2d_rotary4962_4963_rels initSM initPM hSM hPM hInit).1

/-- Public pure-distributed exact 2-TP reconstruction of the layer-5 rotary K output. -/
theorem recon_intermediateGoal_4963_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4963
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4963 4963 8365 8366
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l2d_rotary4962_4963_rels initSM initPM hSM hPM hInit).2

private def layer5FinalSmSliding : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [4962, 4963, 4960, 4964, 4965], outs := [4966],
    params := [16, 4, 64, 64, 1, 512] }
private def layer5FinalPmSliding0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [8363, 8365, 8351, 4964, 4965], outs := [8367],
    params := [16, 4, 64, 64, 1, 512] }
private def layer5FinalPmSliding1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window",
    ins := [8364, 8366, 8352, 4964, 4965], outs := [8368],
    params := [16, 4, 64, 64, 1, 512] }

-- Concrete graph and buddy-order certificates for the final sliding-attention node.
set_option maxRecDepth 1000000 in
private theorem layer5_final_sm_node204 :
    sm.nodes[204]'(by native_decide) = layer5FinalSmSliding := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer5_final_pm_node469 :
    pm.nodes[469]'(by native_decide) = layer5FinalPmSliding0 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer5_final_pm_node470 :
    pm.nodes[470]'(by native_decide) = layer5FinalPmSliding1 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer5_final_sm_buddy :
    ringAttnBuddies sm layer5FinalSmSliding = [layer5FinalSmSliding] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer5_final_pm_buddy0 :
    ringAttnBuddies pm layer5FinalPmSliding0 =
      [layer5FinalPmSliding0, layer5FinalPmSliding1] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer5_final_pm_buddy1 :
    ringAttnBuddies pm layer5FinalPmSliding1 =
      [layer5FinalPmSliding0, layer5FinalPmSliding1] := by native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
/-- Faithful pure-distributed 2-TP reconstruction of the final layer-5 sliding attention. -/
theorem recon_intermediateGoal_4966_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4966
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have gq := recon_intermediateGoal_4962_distributed initSM initPM hSM hPM hInit
  have gk := recon_intermediateGoal_4963_distributed initSM initPM hSM hPM hInit
  have gv := recon_intermediateGoal_4960_distributed initSM initPM hSM hPM hInit
  have gqshape : (denoteGraphDistributed sm initSM 4962).shape = [4096, 16, 64] := by
    simpa only [intermediateGoal_4962] using gq.1
  have gkshape : (denoteGraphDistributed sm initSM 4963).shape = [4096, 4, 64] := by
    simpa only [intermediateGoal_4963] using gk.1
  have gvshape : (denoteGraphDistributed sm initSM 4960).shape = [4096, 4, 64] := by
    simpa only [intermediateGoal_4960] using gv.1
  have q := (l2d_rotary4962_4963_rels initSM initPM hSM hPM hInit).1
  have k := (l2d_rotary4962_4963_rels initSM initPM hSM hPM hInit).2
  have v := l2d_v4960_rel initSM initPM hSM hPM hInit
  have hcu4964 := distributed_init_singleton_value initSM initPM hInit initGoal_4964
    (by native_decide) 4964 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hcu4965 := distributed_init_singleton_value initSM initPM hInit initGoal_4965
    (by native_decide) 4965 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  let fs := (sm.nodes.take 204).foldl (applyNodeDistributed sm) initSM
  let fp := (pm.nodes.take 469).foldl (applyNodeDistributed pm) initPM
  let fp' := (pm.nodes.take 470).foldl (applyNodeDistributed pm) initPM
  have bs (t : Tid) (hn : ∀ n ∈ sm.nodes.drop 204, n.outs ≠ [])
      (hw : ∀ n ∈ sm.nodes.drop 204, t ∉ n.outs) : fs t = denoteGraphDistributed sm initSM t :=
    distributed_prefix_read sm initSM 204 t hn hw
  have bp (t : Tid) (hn : ∀ n ∈ pm.nodes.drop 469, n.outs ≠ [])
      (hw : ∀ n ∈ pm.nodes.drop 469, t ∉ n.outs) : fp t = denoteGraphDistributed pm initPM t :=
    distributed_prefix_read pm initPM 469 t hn hw
  have hqfull : fs 4962 = allGatherPrimDimN 0 2 0 [fp 8363, fp 8364] := by
    rw [bs 4962 (by native_decide) (by native_decide),
      bp 8363 (by native_decide) (by native_decide),
      bp 8364 (by native_decide) (by native_decide)]
    exact q.value
  have hkfull : fs 4963 = allGatherPrimDimN 0 2 0 [fp 8365, fp 8366] := by
    rw [bs 4963 (by native_decide) (by native_decide),
      bp 8365 (by native_decide) (by native_decide),
      bp 8366 (by native_decide) (by native_decide)]
    exact k.value
  have hvfull : fs 4960 = allGatherPrimDimN 0 2 0 [fp 8351, fp 8352] := by
    rw [bs 4960 (by native_decide) (by native_decide),
      bp 8351 (by native_decide) (by native_decide),
      bp 8352 (by native_decide) (by native_decide)]
    exact v.value
  have hqpos : 0 < (fs (layer5FinalSmSliding.ins.getD 0 0)).shape.length := by
    show 0 < (fs 4962).shape.length
    rw [bs 4962 (by native_decide) (by native_decide), gqshape]
    decide
  have hkpos : 0 < (fs (layer5FinalSmSliding.ins.getD 1 0)).shape.length := by
    show 0 < (fs 4963).shape.length
    rw [bs 4963 (by native_decide) (by native_decide), gkshape]
    decide
  have hvpos : 0 < (fs (layer5FinalSmSliding.ins.getD 2 0)).shape.length := by
    show 0 < (fs 4960).shape.length
    rw [bs 4960 (by native_decide) (by native_decide), gvshape]
    decide
  have hcuQ : fs 4964 = fp 4964 := by
    rw [bs 4964 (by native_decide) (by native_decide),
      bp 4964 (by native_decide) (by native_decide), hcu4964]
  have hcuK : fs 4965 = fp 4965 := by
    rw [bs 4965 (by native_decide) (by native_decide),
      bp 4965 (by native_decide) (by native_decide), hcu4965]
  have e8363 : fp 8363 = fp' 8363 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8363 469 470
      (by omega) (by native_decide) (by native_decide)).symm
  have e8364 : fp 8364 = fp' 8364 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8364 469 470
      (by omega) (by native_decide) (by native_decide)).symm
  have e8365 : fp 8365 = fp' 8365 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8365 469 470
      (by omega) (by native_decide) (by native_decide)).symm
  have e8366 : fp 8366 = fp' 8366 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8366 469 470
      (by omega) (by native_decide) (by native_decide)).symm
  have e8351 : fp 8351 = fp' 8351 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8351 469 470
      (by omega) (by native_decide) (by native_decide)).symm
  have e8352 : fp 8352 = fp' 8352 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8352 469 470
      (by omega) (by native_decide) (by native_decide)).symm
  have e4964 : fp 4964 = fp' 4964 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 4964 469 470
      (by omega) (by native_decide) (by native_decide)).symm
  have e4965 : fp 4965 = fp' 4965 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 4965 469 470
      (by omega) (by native_decide) (by native_decide)).symm
  have bridge : applyNodeRingAttn_sliding_window pm fp layer5FinalPmSliding1 =
      applyNodeRingAttn_sliding_window pm fp' layer5FinalPmSliding1 := by
    apply attn_sw_store_congr
    · rw [layer5_final_pm_buddy1]; intro m hm; fin_cases hm
      · exact e8363
      · exact e8364
    · rw [layer5_final_pm_buddy1]; intro m hm; fin_cases hm
      · exact e8365
      · exact e8366
    · rw [layer5_final_pm_buddy1]; intro m hm; fin_cases hm
      · exact e8351
      · exact e8352
    · exact e4964
    · exact e4965
  have rSM : denoteGraphDistributed sm initSM 4966 =
      applyNodeRingAttn_sliding_window sm fs layer5FinalSmSliding := by
    rw [distributed_node_core sm initSM 204 layer5FinalSmSliding 4966 (by native_decide)
      layer5_final_sm_node204 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out sm _ 0 4962 4963 4960 4964 4965 4966
      [16, 4, 64, 64, 1, 512]
  have rP0 : denoteGraphDistributed pm initPM 8367 =
      applyNodeRingAttn_sliding_window pm fp layer5FinalPmSliding0 := by
    rw [distributed_node_core pm initPM 469 layer5FinalPmSliding0 8367 (by native_decide)
      layer5_final_pm_node469 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out pm _ 0 8363 8365 8351 4964 4965 8367
      [16, 4, 64, 64, 1, 512]
  have rP1 : denoteGraphDistributed pm initPM 8368 =
      applyNodeRingAttn_sliding_window pm fp' layer5FinalPmSliding1 := by
    rw [distributed_node_core pm initPM 470 layer5FinalPmSliding1 8368 (by native_decide)
      layer5_final_pm_node470 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out pm _ 1 8364 8366 8352 4964 4965 8368
      [16, 4, 64, 64, 1, 512]
  have hfull : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 8363, fp 8364])
      (allGatherPrimDimN 0 2 0 [fp 8365, fp 8366])
      (allGatherPrimDimN 0 2 0 [fp 8351, fp 8352])
      (fp 4964) (fp 4965) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3, ← hqfull,
      bs 4962 (by native_decide) (by native_decide), gqshape]
    rfl
  have hfull' : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 8363, fp' 8364])
      (allGatherPrimDimN 0 2 0 [fp' 8365, fp' 8366])
      (allGatherPrimDimN 0 2 0 [fp' 8351, fp' 8352])
      (fp' 4964) (fp' 4965) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [← e8363, ← e8364, ← e8365, ← e8366, ← e8351, ← e8352,
      ← e4964, ← e4965]
    exact hfull
  exact recon_attn_sliding_window_2tp_distributed initSM initPM intermediateGoal_4966
    layer5FinalSmSliding layer5FinalPmSliding0 layer5FinalPmSliding1 fs fp fp' 4966 8367 8368
    2048 16 64 (by omega) (by omega) (by omega) rSM rP0 rP1 bridge
    layer5_final_sm_buddy layer5_final_pm_buddy0 layer5_final_pm_buddy1
    (by native_decide) (by native_decide) hqpos hkpos hvpos hqfull hkfull hvfull
    hcuQ hcuK rfl rfl rfl rfl hfull hfull' rfl rfl rfl rfl rfl rfl

/-! ### Layer-6 post-attention residual cascade (pure distributed evaluator) -/

private theorem l2d_reshape4967_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4967)
      (denoteGraphDistributed pm initPM 8369) (denoteGraphDistributed pm initPM 8370)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_4966 4966 8367 8368
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4966_distributed initSM initPM hSM hPM hInit)
  have rs := l2d_reshape sm initSM 205 0 4966 4967 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l2d_reshape pm initPM 471 0 8367 8369 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l2d_reshape pm initPM 472 1 8368 8370 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, fw_view_allGather0_reshape_16_64_2_g12 _ _ h.shard0_shape h.shard1_shape,
      r0, r1]
  · rw [rs]; rfl
  · rw [r0]; rfl
  · rw [r1]; rfl

/-- Public pure-distributed exact 2-TP reconstruction of the layer-6 attention reshape. -/
theorem recon_intermediateGoal_4967_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4967
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4967 4967 8369 8370
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_reshape4967_rel initSM initPM hSM hPM hInit)

private theorem l2d_reshape4968_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4968)
      (denoteGraphDistributed pm initPM 8375) (denoteGraphDistributed pm initPM 8376)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_reshape4967_rel initSM initPM hSM hPM hInit
  have rs := l2d_reshape sm initSM 206 0 4967 4968 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l2d_reshape pm initPM 473 0 8369 8375 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l2d_reshape pm initPM 474 1 8370 8376 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 4968 = denoteGraphDistributed sm initSM 4967 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 8375 = denoteGraphDistributed pm initPM 8369 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 8376 = denoteGraphDistributed pm initPM 8370 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Public pure-distributed exact 2-TP reconstruction of the layer-6 identity reshape. -/
theorem recon_intermediateGoal_4968_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4968
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4968 4968 8375 8376
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_reshape4968_rel initSM initPM hSM hPM hInit)

private theorem l2d_linear4970_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4970)
      (denoteGraphDistributed pm initPM 8379) (denoteGraphDistributed pm initPM 8380)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_reshape4968_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_4969
    (by native_decide) 4969 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_4969
    (by native_decide) 4969 [1024, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 4969).shape = [1024, 1024] := by
    rw [← hw]; exact hws
  have rs := l2d_linear sm initSM 207 0 4968 4969 4970 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_linear pm initPM 475 0 8375 4969 8379 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_linear pm initPM 476 1 8376 4969 8380 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 1024 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 1024 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 1024 _ _ h.shard1_shape hpw

/-- Public pure-distributed exact 2-TP reconstruction of the layer-6 output projection. -/
theorem recon_intermediateGoal_4970_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4970
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4970 4970 8379 8380
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_linear4970_rel initSM initPM hSM hPM hInit)

private theorem l2d_view4971_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4971)
      (denoteGraphDistributed pm initPM 8389) (denoteGraphDistributed pm initPM 8390)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_linear4970_rel initSM initPM hSM hPM hInit
  have rs := l2d_view sm initSM 208 0 4970 4971 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l2d_view pm initPM 477 0 8379 8389 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l2d_view pm initPM 478 1 8380 8390 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 4971 = denoteGraphDistributed sm initSM 4970 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 8389 = denoteGraphDistributed pm initPM 8379 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 8390 = denoteGraphDistributed pm initPM 8380 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Public pure-distributed exact 2-TP reconstruction of the layer-6 identity view. -/
theorem recon_intermediateGoal_4971_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4971
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4971 4971 8389 8390
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_view4971_rel initSM initPM hSM hPM hInit)

private theorem l2d_float4972_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4972)
      (denoteGraphDistributed pm initPM 8393) (denoteGraphDistributed pm initPM 8394)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_view4971_rel initSM initPM hSM hPM hInit
  have rs := l2d_float sm initSM 209 0 4971 4972 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_float pm initPM 479 0 8389 8393 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_float pm initPM 480 1 8390 8394 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  exact ⟨by rw [rs, h.value, r0, r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

/-- Public pure-distributed exact 2-TP reconstruction of the layer-6 float output. -/
theorem recon_intermediateGoal_4972_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4972
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4972 4972 8393 8394
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_float4972_rel initSM initPM hSM hPM hInit)

private theorem l2d_goal7647_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7647)
      (denoteGraphDistributed pm initPM 15017) (denoteGraphDistributed pm initPM 15025)
      [4096, 1024] [2048, 1024] := by
  have h := l2d_add4952_rel initSM initPM hSM hPM hInit
  have rs := distributed_reduce1 sm initSM 197
    { rank := 0, op := "OpName.FW_multiref", ins := [4952], outs := [7643, 7647], params := [2] }
    4952 7647 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' sm st 0 4952 7643 7647 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce1 pm initPM 455
    { rank := 0, op := "OpName.FW_multiref", ins := [8323], outs := [15013, 15017], params := [2] }
    8323 15017 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 0 8323 15013 15017 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce1 pm initPM 456
    { rank := 1, op := "OpName.FW_multiref", ins := [8324], outs := [15021, 15025], params := [2] }
    8324 15025 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 1 8324 15021 15025 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rs r0 r1
  exact ⟨by rw [rs, h.value, r0, r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

/-- Public pure-distributed exact 2-TP reconstruction of the layer-6 residual carry. -/
theorem recon_intermediateGoal_7647_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7647
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_7647 7647 15017 15025
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_goal7647_rel initSM initPM hSM hPM hInit)

private theorem l2d_add4973_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 4973)
      (denoteGraphDistributed pm initPM 8397) (denoteGraphDistributed pm initPM 8398)
      [4096, 1024] [2048, 1024] := by
  have ha := l2d_goal7647_rel initSM initPM hSM hPM hInit
  have hb := l2d_float4972_rel initSM initPM hSM hPM hInit
  have rs := l2d_add sm initSM 210 0 7647 4972 4973 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l2d_add pm initPM 481 0 15017 8393 8397 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l2d_add pm initPM 482 1 15025 8394 8398 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, ha.value, hb.value,
      fw_add_allGather0_commute_2_2048_1024 _ _ _ _ ha.shard0_shape ha.shard1_shape
        hb.shard0_shape hb.shard1_shape, r0, r1]
  · rw [rs]; exact elemwiseAdd_shape_of_shapes _ _ [4096, 1024] ha.full_shape hb.full_shape
  · rw [r0]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] ha.shard0_shape hb.shard0_shape
  · rw [r1]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] ha.shard1_shape hb.shard1_shape

/-- Public pure-distributed exact 2-TP reconstruction of the layer-6 residual add. -/
theorem recon_intermediateGoal_4973_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4973
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_4973 4973 8397 8398
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l2d_add4973_rel initSM initPM hSM hPM hInit)

#print axioms recon_intermediateGoal_4970_distributed
#print axioms recon_intermediateGoal_4973_distributed
#print axioms recon_intermediateGoal_4966_distributed
#print axioms recon_intermediateGoal_4962_distributed
#print axioms recon_intermediateGoal_4963_distributed
#print axioms recon_intermediateGoal_4954_distributed
#print axioms recon_intermediateGoal_4956_distributed
#print axioms recon_intermediateGoal_4958_distributed
#print axioms recon_intermediateGoal_4960_distributed
#print axioms recon_intermediateGoal_4952_distributed
#print axioms recon_intermediateGoal_4930_distributed
#print axioms recon_intermediateGoal_7627_distributed
#print axioms recon_intermediateGoal_4949_distributed

#print axioms recon_intermediateGoal_4934_distributed
#print axioms recon_intermediateGoal_4939_distributed
#print axioms recon_intermediateGoal_4943_distributed

#print axioms recon_intermediateGoal_4925_distributed
#print axioms recon_intermediateGoal_4926_distributed
#print axioms recon_intermediateGoal_4916_distributed
#print axioms recon_intermediateGoal_4919_distributed
#print axioms recon_intermediateGoal_4912_distributed
#print axioms recon_intermediateGoal_4908_distributed
#print axioms recon_intermediateGoal_4909_distributed
#print axioms recon_intermediateGoal_4900_distributed
#print axioms recon_intermediateGoal_4902_distributed
#print axioms recon_intermediateGoal_4904_distributed
#print axioms recon_intermediateGoal_4906_distributed

#print axioms recon_intermediateGoal_4898_distributed
#print axioms recon_intermediateGoal_4895_distributed
#print axioms recon_intermediateGoal_7575_distributed
#print axioms recon_intermediateGoal_4876_distributed

#print axioms recon_intermediateGoal_4880_distributed
#print axioms recon_intermediateGoal_4885_distributed
#print axioms recon_intermediateGoal_4889_distributed

#print axioms recon_intermediateGoal_4871_distributed
#print axioms recon_intermediateGoal_4872_distributed

#print axioms recon_intermediateGoal_4862_distributed
#print axioms recon_intermediateGoal_4865_distributed

#print axioms recon_intermediateGoal_4854_distributed
#print axioms recon_intermediateGoal_4855_distributed
#print axioms recon_intermediateGoal_4858_distributed
#print axioms recon_intermediateGoal_4846_distributed
#print axioms recon_intermediateGoal_4848_distributed
#print axioms recon_intermediateGoal_4850_distributed
#print axioms recon_intermediateGoal_4852_distributed

#print axioms recon_intermediateGoal_4841_distributed
#print axioms recon_intermediateGoal_4842_distributed
#print axioms recon_intermediateGoal_4844_distributed

#print axioms recon_intermediateGoal_4826_distributed
#print axioms recon_intermediateGoal_4831_distributed
#print axioms recon_intermediateGoal_4835_distributed
#print axioms recon_intermediateGoal_4811_distributed
#print axioms recon_intermediateGoal_4817_distributed
#print axioms recon_intermediateGoal_4818_distributed
#print axioms recon_intermediateGoal_4822_distributed

end TrainVerify.Denote.GeneratedPatterns
