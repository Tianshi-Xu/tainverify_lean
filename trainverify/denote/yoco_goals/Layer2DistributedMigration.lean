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

#print axioms recon_intermediateGoal_4811_distributed
#print axioms recon_intermediateGoal_4817_distributed
#print axioms recon_intermediateGoal_4818_distributed
#print axioms recon_intermediateGoal_4822_distributed

end TrainVerify.Denote.GeneratedPatterns
