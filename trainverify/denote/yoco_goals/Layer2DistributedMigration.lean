/- Distributed bootstrap for the next Layer-2 reconstruction slice.
   This file deliberately uses only distributed node algebra after importing the
   completed Layer-1 MoE boundary; no post-MoE ring reconstruction is used. -/
import denote.yoco_goals.Layer1TokenDependencyCone

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option maxRecDepth 10000000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

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

#print axioms recon_intermediateGoal_4772_distributed

end TrainVerify.Denote.GeneratedPatterns
