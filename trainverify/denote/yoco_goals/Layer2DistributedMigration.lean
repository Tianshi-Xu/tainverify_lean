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

end TrainVerify.Denote.GeneratedPatterns
