/- Pure-distributed layer-9 faithful full-expert MoE continuation. -/
import denote.yoco_goals.Layer8DistributedContinuation

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

private theorem l9d_token7835_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7835)
      (denoteGraphDistributed pm initPM 15390) (denoteGraphDistributed pm initPM 15413)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5137 5137 8959 8960
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5137_distributed initSM initPM hSM hPM hInit)
  have s := distributed_reduce1 sm initSM 330
    { rank := 0, op := "OpName.FW_multiref", ins := [5137],
      outs := [7831, 7835, 7839, 7843, 7847], params := [5] }
    5137 7835 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos1_out sm st 0 5137 7831 7835 7839 7843 7847 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 721
    { rank := 0, op := "OpName.FW_multiref", ins := [8959],
      outs := [15386, 15390, 15394, 15398, 15402], params := [5] }
    8959 15390 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos1_out pm st 0 8959 15386 15390 15394 15398 15402 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 722
    { rank := 1, op := "OpName.FW_multiref", ins := [8960],
      outs := [15409, 15413, 15417, 15421, 15425], params := [5] }
    8960 15413 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos1_out pm st 1 8960 15409 15413 15417 15421 15425 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  exact ⟨by rw [s, h.value, ← p0, ← p1], by rw [s]; exact h.full_shape,
    by rw [p0]; exact h.shard0_shape, by rw [p1]; exact h.shard1_shape, by decide⟩

/-- Public pure-distributed exact 2-TP bridge for `mref5-pos1(5137)`. -/
theorem recon_intermediateGoal_7835_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7835
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_7835 7835 15390 15413
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l9d_token7835_rel initSM initPM hSM hPM hInit)

private def layer9SmMoe : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [7835, 5141, 5142, 5144, 5145], outs := [5146], params := [64, 0, 64, 8] }
private def layer9PmMoe0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [15390, 8969, 8971, 8975, 8977], outs := [8979], params := [64, 0, 32, 8] }
private def layer9PmMoe1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm",
    ins := [15413, 8970, 8972, 8976, 8978], outs := [8980], params := [64, 32, 64, 8] }

set_option maxRecDepth 1000000 in
private theorem layer9_sm_node343 : sm.nodes[343]'(by native_decide) = layer9SmMoe := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer9_pm_node747 : pm.nodes[747]'(by native_decide) = layer9PmMoe0 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer9_pm_node750 : pm.nodes[750]'(by native_decide) = layer9PmMoe1 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer9_sm_buddies : sm.replicaBuddies layer9SmMoe = [layer9SmMoe] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer9_pm_buddies0 :
    pm.replicaBuddies layer9PmMoe0 = [layer9PmMoe0, layer9PmMoe1] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer9_pm_buddies1 :
    pm.replicaBuddies layer9PmMoe1 = [layer9PmMoe0, layer9PmMoe1] := by native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
/-- Faithful pure-distributed full-expert reconstruction of the layer-9 MoE boundary. -/
theorem recon_intermediateGoal_5146_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5146
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have hi := l9d_token7835_rel initSM initPM hSM hPM hInit
  have hrp := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5141 5141 8969 8970
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5141_distributed initSM initPM hSM hPM hInit)
  have hrm := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5142 5142 8971 8972
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5142_distributed initSM initPM hSM hPM hInit)
  have hW13 := hInit initGoal_5144 (by native_decide)
  have hW2 := hInit initGoal_5145 (by native_decide)
  have hsW13 := hW13.2.1
  have hsW2 := hW2.2.1
  simp only [initGoal_5144, List.map, List.cons.injEq, and_true] at hsW13
  simp only [initGoal_5145, List.map, List.cons.injEq, and_true] at hsW2
  have hsW13A : (denoteGraphDistributed pm initPM 8975).shape = [32, 1024, 1024] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8975
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW13.1
  have hsW13B : (denoteGraphDistributed pm initPM 8976).shape = [32, 1024, 1024] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8976
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW13.2
  have hsW2A : (denoteGraphDistributed pm initPM 8977).shape = [32, 1024, 512] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8977
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW2.1
  have hsW2B : (denoteGraphDistributed pm initPM 8978).shape = [32, 1024, 512] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8978
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW2.2
  have hbrW13 : denoteGraphDistributed sm initSM 5144 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 8975, denoteGraphDistributed pm initPM 8976] := by
    have hv := hW13.2.2
    rw [reconstructForGoal_of_not_replicated initGoal_5144 pm.numRanks _ rfl] at hv
    simp only [initGoal_5144, List.map] at hv
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
      (by rw [hsW13.1]; decide)] at hv
    have ds : denoteGraphDistributed sm initSM 5144 = initSM 5144 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written sm sm.nodes initSM 5144
        layer1_sm_nodes_nonempty (by native_decide)
    have dp0 : denoteGraphDistributed pm initPM 8975 = initPM 8975 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8975
        layer1_pm_nodes_nonempty (by native_decide)
    have dp1 : denoteGraphDistributed pm initPM 8976 = initPM 8976 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8976
        layer1_pm_nodes_nonempty (by native_decide)
    rw [ds, dp0, dp1]
    exact hv
  have hbrW2 : denoteGraphDistributed sm initSM 5145 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 8977, denoteGraphDistributed pm initPM 8978] := by
    have hv := hW2.2.2
    rw [reconstructForGoal_of_not_replicated initGoal_5145 pm.numRanks _ rfl] at hv
    simp only [initGoal_5145, List.map] at hv
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
      (by rw [hsW2.1]; decide)] at hv
    have ds : denoteGraphDistributed sm initSM 5145 = initSM 5145 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written sm sm.nodes initSM 5145
        layer1_sm_nodes_nonempty (by native_decide)
    have dp0 : denoteGraphDistributed pm initPM 8977 = initPM 8977 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8977
        layer1_pm_nodes_nonempty (by native_decide)
    have dp1 : denoteGraphDistributed pm initPM 8978 = initPM 8978 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8978
        layer1_pm_nodes_nonempty (by native_decide)
    rw [ds, dp0, dp1]
    exact hv
  have hW13single : allGatherPrimDimN 0 1 0 [denoteGraphDistributed sm initSM 5144] =
      denoteGraphDistributed sm initSM 5144 := by
    have hs : (denoteGraphDistributed sm initSM 5144).shape = [64, 1024, 1024] := by
      rw [hbrW13, allGatherPrimDimN_shape 0 2 _ [32, 1024, 1024] (by simp [hsW13A])]
      simp [List.set]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hs]; decide)
  have hW2single : allGatherPrimDimN 0 1 0 [denoteGraphDistributed sm initSM 5145] =
      denoteGraphDistributed sm initSM 5145 := by
    have hs : (denoteGraphDistributed sm initSM 5145).shape = [64, 1024, 512] := by
      rw [hbrW2, allGatherPrimDimN_shape 0 2 _ [32, 1024, 512] (by simp [hsW2A])]
      simp [List.set]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hs]; decide)
  have hSMout : denoteGraphDistributed sm initSM 5146 =
      fw_all2all_moe_gmm_full (denoteGraphDistributed sm initSM 7835)
        (denoteGraphDistributed sm initSM 5141) (denoteGraphDistributed sm initSM 5142)
        [denoteGraphDistributed pm initPM 8975, denoteGraphDistributed pm initPM 8976]
        [denoteGraphDistributed pm initPM 8977, denoteGraphDistributed pm initPM 8978]
        64 8 (((10 : Nat) : Scalar)) := by
    have hk : 343 < sm.nodes.length := by native_decide
    rw [distributed_moe_reduce sm initSM 343 layer9SmMoe 5146 hk
      (show sm.nodes[343]'hk = layer9SmMoe from layer9_sm_node343)
      rfl rfl (by native_decide) (by native_decide)]
    unfold applyNodeFullExpertMoE_value
    rw [layer9_sm_buddies]
    simp only [layer9SmMoe, List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    rw [foldl_take_distributed_eq sm initSM 7835 343 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 5141 343 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 5142 343 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 5144 343 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 5145 343 (by native_decide) (by native_decide)]
    unfold fw_all2all_moe_gmm_full
    simp only [List.length_cons, List.length_nil]
    rw [hW13single, hW2single, hbrW13, hbrW2]
  have hP0 : denoteGraphDistributed pm initPM 8979 =
      fw_all2all_moe_gmm_full (denoteGraphDistributed pm initPM 15390)
        (denoteGraphDistributed pm initPM 8969) (denoteGraphDistributed pm initPM 8971)
        [denoteGraphDistributed pm initPM 8975, denoteGraphDistributed pm initPM 8976]
        [denoteGraphDistributed pm initPM 8977, denoteGraphDistributed pm initPM 8978]
        64 8 (((10 : Nat) : Scalar)) := by
    have hk : 747 < pm.nodes.length := by native_decide
    rw [distributed_moe_reduce pm initPM 747 layer9PmMoe0 8979 hk
      (show pm.nodes[747]'hk = layer9PmMoe0 from layer9_pm_node747)
      rfl rfl (by native_decide) (by native_decide)]
    unfold applyNodeFullExpertMoE_value
    rw [layer9_pm_buddies0]
    simp only [layer9PmMoe0, layer9PmMoe1, List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    rw [foldl_take_distributed_eq pm initPM 15390 747 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8969 747 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8971 747 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8975 747 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8976 747 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8977 747 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8978 747 (by native_decide) (by native_decide)]
  have hP1 : denoteGraphDistributed pm initPM 8980 =
      fw_all2all_moe_gmm_full (denoteGraphDistributed pm initPM 15413)
        (denoteGraphDistributed pm initPM 8970) (denoteGraphDistributed pm initPM 8972)
        [denoteGraphDistributed pm initPM 8975, denoteGraphDistributed pm initPM 8976]
        [denoteGraphDistributed pm initPM 8977, denoteGraphDistributed pm initPM 8978]
        64 8 (((10 : Nat) : Scalar)) := by
    have hk : 750 < pm.nodes.length := by native_decide
    rw [distributed_moe_reduce pm initPM 750 layer9PmMoe1 8980 hk
      (show pm.nodes[750]'hk = layer9PmMoe1 from layer9_pm_node750)
      rfl rfl (by native_decide) (by native_decide)]
    unfold applyNodeFullExpertMoE_value
    rw [layer9_pm_buddies1]
    simp only [layer9PmMoe0, layer9PmMoe1, List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    rw [foldl_take_distributed_eq pm initPM 15413 750 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8970 750 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8972 750 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8975 750 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8976 750 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8977 750 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8978 750 (by native_decide) (by native_decide)]
  have hc := fw_all2all_moe_gmm_full_split_commute_2
    (denoteGraphDistributed pm initPM 15390) (denoteGraphDistributed pm initPM 15413)
    (denoteGraphDistributed pm initPM 8969) (denoteGraphDistributed pm initPM 8970)
    (denoteGraphDistributed pm initPM 8971) (denoteGraphDistributed pm initPM 8972)
    (denoteGraphDistributed pm initPM 8975) (denoteGraphDistributed pm initPM 8976)
    (denoteGraphDistributed pm initPM 8977) (denoteGraphDistributed pm initPM 8978)
    2048 1024 32 8 1024 512 (((10 : Nat) : Scalar))
    (by omega) (by omega) (by omega) (by omega) (by omega) rfl
    hi.shard0_shape hi.shard1_shape hrp.shard0_shape hrp.shard1_shape
    hrm.shard0_shape hrm.shard1_shape hsW13A hsW13B hsW2A hsW2B
  have hval : denoteGraphDistributed sm initSM 5146 = allGatherPrimDimN 0 pm.numRanks 0
      [denoteGraphDistributed pm initPM 8979, denoteGraphDistributed pm initPM 8980] := by
    rw [hSMout, hi.value, hrp.value, hrm.value, hc, ← hP0, ← hP1,
      show pm.numRanks = 2 from rfl]
  have hsP0 : (denoteGraphDistributed pm initPM 8979).shape = [2048, 1024] := by
    rw [hP0]
    exact fw_all2all_moe_gmm_full_shape
      (input := denoteGraphDistributed pm initPM 15390)
      (rp := denoteGraphDistributed pm initPM 8969)
      (rm := denoteGraphDistributed pm initPM 8971)
      (w13s := [denoteGraphDistributed pm initPM 8975, denoteGraphDistributed pm initPM 8976])
      (w2s := [denoteGraphDistributed pm initPM 8977, denoteGraphDistributed pm initPM 8978])
      (numExp := 64) (topK := 8) (swigluLimit := (((10 : Nat) : Scalar)))
      (lDim := 2048) (hModel := 1024)
      (by rw [hi.shard0_shape]; rfl) (by rw [hi.shard0_shape]; rfl)
  have hsP1 : (denoteGraphDistributed pm initPM 8980).shape = [2048, 1024] := by
    rw [hP1]
    exact fw_all2all_moe_gmm_full_shape
      (input := denoteGraphDistributed pm initPM 15413)
      (rp := denoteGraphDistributed pm initPM 8970)
      (rm := denoteGraphDistributed pm initPM 8972)
      (w13s := [denoteGraphDistributed pm initPM 8975, denoteGraphDistributed pm initPM 8976])
      (w2s := [denoteGraphDistributed pm initPM 8977, denoteGraphDistributed pm initPM 8978])
      (numExp := 64) (topK := 8) (swigluLimit := (((10 : Nat) : Scalar)))
      (lDim := 2048) (hModel := 1024)
      (by rw [hi.shard1_shape]; rfl) (by rw [hi.shard1_shape]; rfl)
  have hsSM : (denoteGraphDistributed sm initSM 5146).shape = [4096, 1024] := by
    rw [hval, show pm.numRanks = 2 from rfl,
      allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsP0])]
    simp [List.set]
  exact wrap_2tp_allGather_gen _ _ intermediateGoal_5146 5146 8979 8980
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    hval hsSM hsP0 hsP1

/-! ### Pure-distributed post-MoE residual tail. -/

private theorem l9d_float (g : GraphDecl) (init : Store) (k r i o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_float", ins := [i], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributed g init o = denoteGraphDistributed g init i := by
  have h := distributed_reduce1 g init k _ i o id hk hn (by simp)
    (fun st => applyNode_fw_float_out g st r i o []) hdn hdw hpn hpw
  simpa only [id_eq] using h

private theorem l9d_carry7824_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7824)
      (denoteGraphDistributed pm initPM 15371) (denoteGraphDistributed pm initPM 15379)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5135 5135 8955 8956
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5135_distributed initSM initPM hSM hPM hInit)
  have rs := distributed_reduce1 sm initSM 328
    { rank := 0, op := "OpName.FW_multiref", ins := [5135], outs := [7820, 7824], params := [2] }
    5135 7824 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' sm st 0 5135 7820 7824 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce1 pm initPM 717
    { rank := 0, op := "OpName.FW_multiref", ins := [8955], outs := [15367, 15371], params := [2] }
    8955 15371 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 0 8955 15367 15371 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce1 pm initPM 718
    { rank := 1, op := "OpName.FW_multiref", ins := [8956], outs := [15375, 15379], params := [2] }
    8956 15379 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 1 8956 15375 15379 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rs r0 r1
  exact ⟨by rw [rs, h.value, ← r0, ← r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP `mref2`-second carry of the layer-9 pre-MoE residual. -/
theorem recon_intermediateGoal_7824_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7824
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_7824 7824 15371 15379
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l9d_carry7824_rel initSM initPM hSM hPM hInit)

private theorem l9d_add5166_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5166)
      (denoteGraphDistributed pm initPM 9057) (denoteGraphDistributed pm initPM 9058)
      [4096, 1024] [2048, 1024] := by
  have ha := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5146 5146 8979 8980
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5146_distributed initSM initPM hSM hPM hInit)
  have hb := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5165 5165 9053 9054
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5165_distributed initSM initPM hSM hPM hInit)
  have rs := distributed_reduce2 sm initSM 350
    { rank := 0, op := "OpName.FW_add", ins := [5146, 5165], outs := [5166] }
    5146 5165 5166 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_add2_out sm st 0 5146 5165 5166)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce2 pm initPM 761
    { rank := 0, op := "OpName.FW_add", ins := [8979, 9053], outs := [9057] }
    8979 9053 9057 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_add2_out pm st 0 8979 9053 9057)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce2 pm initPM 762
    { rank := 1, op := "OpName.FW_add", ins := [8980, 9054], outs := [9058] }
    8980 9054 9058 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_add2_out pm st 1 8980 9054 9058)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, ha.value, hb.value,
      fw_add_allGather0_commute_2_2048_1024 _ _ _ _ ha.shard0_shape ha.shard1_shape
        hb.shard0_shape hb.shard1_shape, ← r0, ← r1]
  · rw [rs]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.full_shape hb.full_shape
  · rw [r0]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.shard0_shape hb.shard0_shape
  · rw [r1]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.shard1_shape hb.shard1_shape

/-- Pure-distributed exact 2-TP post-MoE residual add `5146 + 5165`. -/
theorem recon_intermediateGoal_5166_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5166
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5166 5166 9057 9058
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l9d_add5166_rel initSM initPM hSM hPM hInit)

private theorem l9d_float5167_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5167)
      (denoteGraphDistributed pm initPM 9063) (denoteGraphDistributed pm initPM 9064)
      [4096, 1024] [2048, 1024] := by
  have h := l9d_add5166_rel initSM initPM hSM hPM hInit
  have rs := l9d_float sm initSM 351 0 5166 5167 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l9d_float pm initPM 763 0 9057 9063 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l9d_float pm initPM 764 1 9058 9064 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  exact ⟨by rw [rs, h.value, r0, r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP identity float of the layer-9 post-MoE residual. -/
theorem recon_intermediateGoal_5167_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5167
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5167 5167 9063 9064
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l9d_float5167_rel initSM initPM hSM hPM hInit)

/-- Pure-distributed exact 2-TP cross-block residual add `7824 + 5167`. -/
theorem recon_intermediateGoal_5168_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5168
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have ha := l9d_carry7824_rel initSM initPM hSM hPM hInit
  have hb := l9d_float5167_rel initSM initPM hSM hPM hInit
  have rs := distributed_reduce2 sm initSM 352
    { rank := 0, op := "OpName.FW_add", ins := [7824, 5167], outs := [5168] }
    7824 5167 5168 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_add2_out sm st 0 7824 5167 5168)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce2 pm initPM 765
    { rank := 0, op := "OpName.FW_add", ins := [15371, 9063], outs := [9067] }
    15371 9063 9067 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_add2_out pm st 0 15371 9063 9067)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce2 pm initPM 766
    { rank := 1, op := "OpName.FW_add", ins := [15379, 9064], outs := [9068] }
    15379 9064 9068 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_add2_out pm st 1 15379 9064 9068)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hv : denoteGraphDistributed sm initSM 5168 = allGatherPrimDimN 0 pm.numRanks 0
      [denoteGraphDistributed pm initPM 9067, denoteGraphDistributed pm initPM 9068] := by
    rw [rs, ha.value, hb.value, show pm.numRanks = 2 from rfl,
      fw_add_allGather0_commute_2_2048_1024 _ _ _ _ ha.shard0_shape ha.shard1_shape
        hb.shard0_shape hb.shard1_shape, ← r0, ← r1]
  have hs0 : (denoteGraphDistributed pm initPM 9067).shape = [2048, 1024] := by
    rw [r0]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.shard0_shape hb.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 9068).shape = [2048, 1024] := by
    rw [r1]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.shard1_shape hb.shard1_shape
  have hs : (denoteGraphDistributed sm initSM 5168).shape = [4096, 1024] := by
    rw [rs]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.full_shape hb.full_shape
  exact wrap_2tp_allGather_gen _ _ intermediateGoal_5168 5168 9067 9068
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide) hv hs hs0 hs1

/-! ### Pure-distributed next-layer pre-attention Q/K/V slice. -/

private theorem l9d_rms (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_rms_norm", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributed g init o =
      fw_rms_norm (denoteGraphDistributed g init x) (denoteGraphDistributed g init w) :=
  distributed_reduce2 g init k _ x w o fw_rms_norm hk hn (by simp)
    (fun st => applyNode_fw_rms_norm_out_1p g st r x w o) hdn hdw hpn hpx hpw

private theorem l9d_per_head_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
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
    (fun st => applyNode_fw_per_head_mix_precision_linear_out g st r x w o [])
    hdn hdw hpn hpx hpw

private theorem l9d_5170_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5170)
      (denoteGraphDistributed pm initPM 9071) (denoteGraphDistributed pm initPM 9072)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5168 5168 9067 9068
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5168_distributed initSM initPM hSM hPM hInit)
  have s := distributed_reduce1 sm initSM 353
    { rank := 0, op := "OpName.FW_multiref", ins := [5168], outs := [7851, 7855], params := [2] }
    5168 7851 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out sm st 0 5168 7851 7855)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 767
    { rank := 0, op := "OpName.FW_multiref", ins := [9067], outs := [15429, 15433], params := [2] }
    9067 15429 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 0 9067 15429 15433)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 768
    { rank := 1, op := "OpName.FW_multiref", ins := [9068], outs := [15437, 15441], params := [2] }
    9068 15437 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 1 9068 15437 15441)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5169
    (by native_decide) 5169 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have rs := l9d_rms sm initSM 354 0 7851 5169 5170 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l9d_rms pm initPM 769 0 15429 5169 9071 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l9d_rms pm initPM 770 1 15437 5169 9072 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15429).shape = [2048, 1024] := by
    rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15437).shape = [2048, 1024] := by
    rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs0 hs1,
      r0, r1]
  · rw [rs]; exact fw_rms_norm_shape2 _ _ 4096 1024 (by rw [s]; exact h.full_shape)
  · rw [r0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs0
  · rw [r1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs1

/-- Pure-distributed exact 2-TP next-layer pre-attention RMSNorm. -/
theorem recon_intermediateGoal_5170_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5170
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5170 5170 9071 9072
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l9d_5170_rel initSM initPM hSM hPM hInit)

private theorem l9d_5172_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5172)
      (denoteGraphDistributed pm initPM 9073) (denoteGraphDistributed pm initPM 9074)
      [4096, 16, 64] [2048, 16, 64] := by
  have h := l9d_5170_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 355
    { rank := 0, op := "OpName.FW_multiref", ins := [5170], outs := [7860, 7864, 7868], params := [3] }
    5170 7860 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' sm st 0 5170 7860 7864 7868)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 771
    { rank := 0, op := "OpName.FW_multiref", ins := [9071], outs := [15446, 15450, 15454], params := [3] }
    9071 15446 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' pm st 0 9071 15446 15450 15454)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 772
    { rank := 1, op := "OpName.FW_multiref", ins := [9072], outs := [15459, 15463, 15467], params := [3] }
    9072 15459 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' pm st 1 9072 15459 15463 15467)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5171
    (by native_decide) 5171 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5171
    (by native_decide) 5171 [16, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5171).shape = [16, 64, 1024] := by rw [← hw]; exact hws
  have rs := l9d_per_head_linear sm initSM 356 0 7860 5171 5172 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l9d_per_head_linear pm initPM 773 0 15446 5171 9073 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l9d_per_head_linear pm initPM 776 1 15459 5171 9074 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15446).shape = [2048, 1024] := by rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15459).shape = [2048, 1024] := by rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 16 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, r0, r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 16 64 (by rw [s]; exact h.full_shape) hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs0 hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs1 hpw

/-- Pure-distributed exact 2-TP next-layer Q projection. -/
theorem recon_intermediateGoal_5172_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5172
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5172 5172 9073 9074
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl
    (l9d_5172_rel initSM initPM hSM hPM hInit)

private theorem l9d_5174_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5174)
      (denoteGraphDistributed pm initPM 9085) (denoteGraphDistributed pm initPM 9086)
      [4096, 4, 64] [2048, 4, 64] := by
  have h := l9d_5170_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 355
    { rank := 0, op := "OpName.FW_multiref", ins := [5170], outs := [7860, 7864, 7868], params := [3] }
    5170 7864 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' sm st 0 5170 7860 7864 7868 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 771
    { rank := 0, op := "OpName.FW_multiref", ins := [9071], outs := [15446, 15450, 15454], params := [3] }
    9071 15450 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' pm st 0 9071 15446 15450 15454 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 772
    { rank := 1, op := "OpName.FW_multiref", ins := [9072], outs := [15459, 15463, 15467], params := [3] }
    9072 15463 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' pm st 1 9072 15459 15463 15467 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5173
    (by native_decide) 5173 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5173
    (by native_decide) 5173 [4, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5173).shape = [4, 64, 1024] := by rw [← hw]; exact hws
  have rs := l9d_per_head_linear sm initSM 357 0 7864 5173 5174 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l9d_per_head_linear pm initPM 774 0 15450 5173 9085 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l9d_per_head_linear pm initPM 777 1 15463 5173 9086 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15450).shape = [2048, 1024] := by rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15463).shape = [2048, 1024] := by rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, r0, r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64 (by rw [s]; exact h.full_shape) hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs0 hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs1 hpw

/-- Pure-distributed exact 2-TP next-layer K projection. -/
theorem recon_intermediateGoal_5174_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5174
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5174 5174 9085 9086
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l9d_5174_rel initSM initPM hSM hPM hInit)

private theorem l9d_5176_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5176)
      (denoteGraphDistributed pm initPM 9095) (denoteGraphDistributed pm initPM 9096)
      [4096, 4, 64] [2048, 4, 64] := by
  have h := l9d_5170_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 355
    { rank := 0, op := "OpName.FW_multiref", ins := [5170], outs := [7860, 7864, 7868], params := [3] }
    5170 7868 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' sm st 0 5170 7860 7864 7868 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 771
    { rank := 0, op := "OpName.FW_multiref", ins := [9071], outs := [15446, 15450, 15454], params := [3] }
    9071 15454 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' pm st 0 9071 15446 15450 15454 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 772
    { rank := 1, op := "OpName.FW_multiref", ins := [9072], outs := [15459, 15463, 15467], params := [3] }
    9072 15467 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' pm st 1 9072 15459 15463 15467 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5175
    (by native_decide) 5175 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5175
    (by native_decide) 5175 [4, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5175).shape = [4, 64, 1024] := by rw [← hw]; exact hws
  have rs := l9d_per_head_linear sm initSM 358 0 7868 5175 5176 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l9d_per_head_linear pm initPM 775 0 15454 5175 9095 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l9d_per_head_linear pm initPM 778 1 15467 5175 9096 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15454).shape = [2048, 1024] := by rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15467).shape = [2048, 1024] := by rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, r0, r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64 (by rw [s]; exact h.full_shape) hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs0 hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs1 hpw

/-- Pure-distributed exact 2-TP next-layer V projection. -/
theorem recon_intermediateGoal_5176_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5176
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5176 5176 9095 9096
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l9d_5176_rel initSM initPM hSM hPM hInit)

private theorem l9d_chunk (g : GraphDecl) (init : Store) (k r i o d : Nat)
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
    hk hn (by simp) (fun st => applyNode_chunkPrimDimN_out g st r i o d) hdn hdw hpn hpw

/-- Distributed cache agreement for the layer-9 PM rotary-cache replica. -/
private theorem l9d_rotary_cache_11862 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraphDistributed sm initSM 4691 = denoteGraphDistributed pm initPM 11862 := by
  have hsource := sm_pm_rotary_cache_agree initSM initPM hInit 11862 9 (by norm_num) rfl
  have hbase := distributed_init_singleton_value initSM initPM hInit initGoal_4691
    (by native_decide) 4691 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hcopy : denoteGraphDistributed pm initPM 11862 = id (denoteGraphDistributed pm initPM 4691) :=
    distributed_reduce1 pm initPM 14
      { rank := 1, op := "OpName.FW_multiref", ins := [4691],
        outs := (List.range 12).map (fun r => 11853 + r),
        params := [((List.range 12).map (fun r => 11853 + r)).length] }
      4691 11862 id (by native_decide) (by native_decide) (by decide)
      (fun st => by
        rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm st _ (by decide) (by decide)]
        rw [applyNode_fw_multiref_mem_out pm st 1 4691
          ((List.range 12).map (fun r => 11853 + r)) 11862 (by native_decide), id_eq])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  rw [hcopy, id_eq]
  exact hbase

set_option maxHeartbeats 8000000 in
private theorem l9d_rotary5178_5179_rels (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5178)
      (denoteGraphDistributed pm initPM 9107) (denoteGraphDistributed pm initPM 9108)
      [4096, 16, 64] [2048, 16, 64] ∧
    Gather2Rel (denoteGraphDistributed sm initSM 5179)
      (denoteGraphDistributed pm initPM 9109) (denoteGraphDistributed pm initPM 9110)
      [4096, 4, 64] [2048, 4, 64] := by
  have hq := l9d_5172_rel initSM initPM hSM hPM hInit
  have hk := l9d_5174_rel initSM initPM hSM hPM hInit
  have hcache := l9d_rotary_cache_11862 initSM initPM hInit
  have hpos := distributed_init_singleton_value initSM initPM hInit initGoal_5177
    (by native_decide) 5177 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hspos := distributed_init_singleton_shape initSM initPM hInit initGoal_5177
    (by native_decide) 5177 [4096] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have c0 := l9d_chunk pm initPM 9 0 5177 9105 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c1 := l9d_chunk pm initPM 22 1 5177 9106 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c0' : denoteGraphDistributed pm initPM 9105 = chunkPrimDimN 0 2 0
      (denoteGraphDistributed pm initPM 5177) := c0
  have c1' : denoteGraphDistributed pm initPM 9106 = chunkPrimDimN 0 2 1
      (denoteGraphDistributed pm initPM 5177) := c1
  have qSM : denoteGraphDistributed sm initSM 5178 =
      (fw_rotary_embedding (denoteGraphDistributed sm initSM 4691) (denoteGraphDistributed sm initSM 5177)
        (denoteGraphDistributed sm initSM 5172) (denoteGraphDistributed sm initSM 5174) 16 4).1 := by
    rw [distributed_node_core sm initSM 359
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5177, 5172, 5174], outs := [5178, 5179], params := [16, 4] }
      5178 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring sm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read sm initSM 359 4691 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 359 5177 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 359 5172 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 359 5174 (by native_decide) (by native_decide)]
  have kSM : denoteGraphDistributed sm initSM 5179 =
      (fw_rotary_embedding (denoteGraphDistributed sm initSM 4691) (denoteGraphDistributed sm initSM 5177)
        (denoteGraphDistributed sm initSM 5172) (denoteGraphDistributed sm initSM 5174) 16 4).2 := by
    rw [distributed_node_core sm initSM 359
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5177, 5172, 5174], outs := [5178, 5179], params := [16, 4] }
      5179 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring sm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 4691 5177 5172 5174 5178 5179 (by decide),
      distributed_prefix_read sm initSM 359 4691 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 359 5177 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 359 5172 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 359 5174 (by native_decide) (by native_decide)]
  have q0 : denoteGraphDistributed pm initPM 9107 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11862) (denoteGraphDistributed pm initPM 9105)
        (denoteGraphDistributed pm initPM 9073) (denoteGraphDistributed pm initPM 9085) 16 4).1 := by
    rw [distributed_node_core pm initPM 779
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11862, 9105, 9073, 9085], outs := [9107, 9109], params := [16, 4] }
      9107 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide), applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read pm initPM 779 11862 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 779 9105 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 779 9073 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 779 9085 (by native_decide) (by native_decide)]
  have k0 : denoteGraphDistributed pm initPM 9109 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11862) (denoteGraphDistributed pm initPM 9105)
        (denoteGraphDistributed pm initPM 9073) (denoteGraphDistributed pm initPM 9085) 16 4).2 := by
    rw [distributed_node_core pm initPM 779
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11862, 9105, 9073, 9085], outs := [9107, 9109], params := [16, 4] }
      9109 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11862 9105 9073 9085 9107 9109 (by decide),
      distributed_prefix_read pm initPM 779 11862 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 779 9105 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 779 9073 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 779 9085 (by native_decide) (by native_decide)]
  have q1 : denoteGraphDistributed pm initPM 9108 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11862) (denoteGraphDistributed pm initPM 9106)
        (denoteGraphDistributed pm initPM 9074) (denoteGraphDistributed pm initPM 9086) 16 4).1 := by
    rw [distributed_node_core pm initPM 780
      { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11862, 9106, 9074, 9086], outs := [9108, 9110], params := [16, 4] }
      9108 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide), applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read pm initPM 780 11862 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 780 9106 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 780 9074 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 780 9086 (by native_decide) (by native_decide)]
  have k1 : denoteGraphDistributed pm initPM 9110 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11862) (denoteGraphDistributed pm initPM 9106)
        (denoteGraphDistributed pm initPM 9074) (denoteGraphDistributed pm initPM 9086) 16 4).2 := by
    rw [distributed_node_core pm initPM 780
      { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11862, 9106, 9074, 9086], outs := [9108, 9110], params := [16, 4] }
      9110 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11862 9106 9074 9086 9108 9110 (by decide),
      distributed_prefix_read pm initPM 780 11862 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 780 9106 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 780 9074 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 780 9086 (by native_decide) (by native_decide)]
  have qval : denoteGraphDistributed sm initSM 5178 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 9107, denoteGraphDistributed pm initPM 9108] := by
    rw [qSM]; simp only [fw_rotary_embedding]
    rw [hq.value, fw_rotary_apply_allGather0_commute_2_1d (denoteGraphDistributed sm initSM 4691)
      (denoteGraphDistributed sm initSM 5177) (denoteGraphDistributed pm initPM 9073)
      (denoteGraphDistributed pm initPM 9074) 2048 16 64 (by omega) (by omega) (by omega)
      hspos hq.shard0_shape hq.shard1_shape, hcache, hpos, ← c0', ← c1', q0, q1]
    simp only [fw_rotary_embedding]
  have kval : denoteGraphDistributed sm initSM 5179 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 9109, denoteGraphDistributed pm initPM 9110] := by
    rw [kSM]; simp only [fw_rotary_embedding]
    rw [hk.value, fw_rotary_apply_allGather0_commute_2_1d (denoteGraphDistributed sm initSM 4691)
      (denoteGraphDistributed sm initSM 5177) (denoteGraphDistributed pm initPM 9085)
      (denoteGraphDistributed pm initPM 9086) 2048 4 64 (by omega) (by omega) (by omega)
      hspos hk.shard0_shape hk.shard1_shape, hcache, hpos, ← c0', ← c1', k0, k1]
    simp only [fw_rotary_embedding]
  have qs0 : (denoteGraphDistributed pm initPM 9107).shape = [2048, 16, 64] := by
    rw [q0]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hq.shard0_shape
  have qs1 : (denoteGraphDistributed pm initPM 9108).shape = [2048, 16, 64] := by
    rw [q1]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hq.shard1_shape
  have ks0 : (denoteGraphDistributed pm initPM 9109).shape = [2048, 4, 64] := by
    rw [k0]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hk.shard0_shape
  have ks1 : (denoteGraphDistributed pm initPM 9110).shape = [2048, 4, 64] := by
    rw [k1]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hk.shard1_shape
  refine ⟨⟨qval, ?_, qs0, qs1, by decide⟩, ⟨kval, ?_, ks0, ks1, by decide⟩⟩
  · rw [qval, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [qs0])]; rfl
  · rw [kval, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [ks0])]; rfl

/-- Public pure-distributed exact 2-TP reconstruction of the layer-9 rotary Q output. -/
theorem recon_intermediateGoal_5178_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5178
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5178 5178 9107 9108
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl
    (l9d_rotary5178_5179_rels initSM initPM hSM hPM hInit).1

/-- Public pure-distributed exact 2-TP reconstruction of the layer-9 rotary K output. -/
theorem recon_intermediateGoal_5179_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5179
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5179 5179 9109 9110
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l9d_rotary5178_5179_rels initSM initPM hSM hPM hInit).2

private def layer9SmSliding : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [5178, 5179, 5176, 5180, 5181], outs := [5182],
    params := [16, 4, 64, 64, 1, 512] }
private def layer9PmSliding0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [9107, 9109, 9095, 5180, 5181], outs := [9111],
    params := [16, 4, 64, 64, 1, 512] }
private def layer9PmSliding1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window",
    ins := [9108, 9110, 9096, 5180, 5181], outs := [9112],
    params := [16, 4, 64, 64, 1, 512] }

set_option maxRecDepth 1000000 in
private theorem layer9_sm_sliding_node360 :
    sm.nodes[360]'(by native_decide) = layer9SmSliding := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer9_pm_sliding_node781 :
    pm.nodes[781]'(by native_decide) = layer9PmSliding0 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer9_pm_sliding_node782 :
    pm.nodes[782]'(by native_decide) = layer9PmSliding1 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer9_sm_sliding_buddy :
    ringAttnBuddies sm layer9SmSliding = [layer9SmSliding] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer9_pm_sliding_buddy0 :
    ringAttnBuddies pm layer9PmSliding0 = [layer9PmSliding0, layer9PmSliding1] := by
  native_decide
set_option maxRecDepth 1000000 in
private theorem layer9_pm_sliding_buddy1 :
    ringAttnBuddies pm layer9PmSliding1 = [layer9PmSliding0, layer9PmSliding1] := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
/-- Faithful public pure-distributed exact 2-TP reconstruction of the layer-9
    sliding-window attention output. -/
theorem recon_intermediateGoal_5182_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5182
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have q := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5178 5178 9107 9108
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5178_distributed initSM initPM hSM hPM hInit)
  have k := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5179 5179 9109 9110
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5179_distributed initSM initPM hSM hPM hInit)
  have v := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5176 5176 9095 9096
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5176_distributed initSM initPM hSM hPM hInit)
  have hcu5180 := distributed_init_singleton_value initSM initPM hInit initGoal_5180
    (by native_decide) 5180 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hcu5181 := distributed_init_singleton_value initSM initPM hInit initGoal_5181
    (by native_decide) 5181 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  let fs := (sm.nodes.take 360).foldl (applyNodeDistributed sm) initSM
  let fp := (pm.nodes.take 781).foldl (applyNodeDistributed pm) initPM
  let fp' := (pm.nodes.take 782).foldl (applyNodeDistributed pm) initPM
  have bs (t : Tid) (hn : ∀ n ∈ sm.nodes.drop 360, n.outs ≠ [])
      (hw : ∀ n ∈ sm.nodes.drop 360, t ∉ n.outs) :
      fs t = denoteGraphDistributed sm initSM t :=
    distributed_prefix_read sm initSM 360 t hn hw
  have bp (t : Tid) (hn : ∀ n ∈ pm.nodes.drop 781, n.outs ≠ [])
      (hw : ∀ n ∈ pm.nodes.drop 781, t ∉ n.outs) :
      fp t = denoteGraphDistributed pm initPM t :=
    distributed_prefix_read pm initPM 781 t hn hw
  have hqfull : fs 5178 = allGatherPrimDimN 0 2 0 [fp 9107, fp 9108] := by
    rw [bs 5178 (by native_decide) (by native_decide),
      bp 9107 (by native_decide) (by native_decide),
      bp 9108 (by native_decide) (by native_decide)]
    exact q.value
  have hkfull : fs 5179 = allGatherPrimDimN 0 2 0 [fp 9109, fp 9110] := by
    rw [bs 5179 (by native_decide) (by native_decide),
      bp 9109 (by native_decide) (by native_decide),
      bp 9110 (by native_decide) (by native_decide)]
    exact k.value
  have hvfull : fs 5176 = allGatherPrimDimN 0 2 0 [fp 9095, fp 9096] := by
    rw [bs 5176 (by native_decide) (by native_decide),
      bp 9095 (by native_decide) (by native_decide),
      bp 9096 (by native_decide) (by native_decide)]
    exact v.value
  have hqpos : 0 < (fs (layer9SmSliding.ins.getD 0 0)).shape.length := by
    show 0 < (fs 5178).shape.length
    rw [bs 5178 (by native_decide) (by native_decide), q.full_shape]
    decide
  have hkpos : 0 < (fs (layer9SmSliding.ins.getD 1 0)).shape.length := by
    show 0 < (fs 5179).shape.length
    rw [bs 5179 (by native_decide) (by native_decide), k.full_shape]
    decide
  have hvpos : 0 < (fs (layer9SmSliding.ins.getD 2 0)).shape.length := by
    show 0 < (fs 5176).shape.length
    rw [bs 5176 (by native_decide) (by native_decide), v.full_shape]
    decide
  have hcuQ : fs 5180 = fp 5180 := by
    rw [bs 5180 (by native_decide) (by native_decide),
      bp 5180 (by native_decide) (by native_decide), hcu5180]
  have hcuK : fs 5181 = fp 5181 := by
    rw [bs 5181 (by native_decide) (by native_decide),
      bp 5181 (by native_decide) (by native_decide), hcu5181]
  have e9107 : fp 9107 = fp' 9107 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 9107 781 782
      (by omega) (by native_decide) (by native_decide)).symm
  have e9108 : fp 9108 = fp' 9108 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 9108 781 782
      (by omega) (by native_decide) (by native_decide)).symm
  have e9109 : fp 9109 = fp' 9109 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 9109 781 782
      (by omega) (by native_decide) (by native_decide)).symm
  have e9110 : fp 9110 = fp' 9110 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 9110 781 782
      (by omega) (by native_decide) (by native_decide)).symm
  have e9095 : fp 9095 = fp' 9095 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 9095 781 782
      (by omega) (by native_decide) (by native_decide)).symm
  have e9096 : fp 9096 = fp' 9096 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 9096 781 782
      (by omega) (by native_decide) (by native_decide)).symm
  have e5180 : fp 5180 = fp' 5180 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 5180 781 782
      (by omega) (by native_decide) (by native_decide)).symm
  have e5181 : fp 5181 = fp' 5181 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 5181 781 782
      (by omega) (by native_decide) (by native_decide)).symm
  have bridge : applyNodeRingAttn_sliding_window pm fp layer9PmSliding1 =
      applyNodeRingAttn_sliding_window pm fp' layer9PmSliding1 := by
    apply attn_sw_store_congr
    · rw [layer9_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e9107
      · exact e9108
    · rw [layer9_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e9109
      · exact e9110
    · rw [layer9_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e9095
      · exact e9096
    · exact e5180
    · exact e5181
  have rSM : denoteGraphDistributed sm initSM 5182 =
      applyNodeRingAttn_sliding_window sm fs layer9SmSliding := by
    rw [distributed_node_core sm initSM 360 layer9SmSliding 5182 (by native_decide)
      layer9_sm_sliding_node360 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out sm _ 0 5178 5179 5176 5180 5181 5182
      [16, 4, 64, 64, 1, 512]
  have rP0 : denoteGraphDistributed pm initPM 9111 =
      applyNodeRingAttn_sliding_window pm fp layer9PmSliding0 := by
    rw [distributed_node_core pm initPM 781 layer9PmSliding0 9111 (by native_decide)
      layer9_pm_sliding_node781 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out pm _ 0 9107 9109 9095 5180 5181 9111
      [16, 4, 64, 64, 1, 512]
  have rP1 : denoteGraphDistributed pm initPM 9112 =
      applyNodeRingAttn_sliding_window pm fp' layer9PmSliding1 := by
    rw [distributed_node_core pm initPM 782 layer9PmSliding1 9112 (by native_decide)
      layer9_pm_sliding_node782 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out pm _ 1 9108 9110 9096 5180 5181 9112
      [16, 4, 64, 64, 1, 512]
  have hfull : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 9107, fp 9108])
      (allGatherPrimDimN 0 2 0 [fp 9109, fp 9110])
      (allGatherPrimDimN 0 2 0 [fp 9095, fp 9096])
      (fp 5180) (fp 5181) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3, ← hqfull,
      bs 5178 (by native_decide) (by native_decide), q.full_shape]
    rfl
  have hfull' : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 9107, fp' 9108])
      (allGatherPrimDimN 0 2 0 [fp' 9109, fp' 9110])
      (allGatherPrimDimN 0 2 0 [fp' 9095, fp' 9096])
      (fp' 5180) (fp' 5181) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [← e9107, ← e9108, ← e9109, ← e9110, ← e9095, ← e9096,
      ← e5180, ← e5181]
    exact hfull
  exact recon_attn_sliding_window_2tp_distributed initSM initPM intermediateGoal_5182
    layer9SmSliding layer9PmSliding0 layer9PmSliding1 fs fp fp' 5182 9111 9112
    2048 16 64 (by omega) (by omega) (by omega) rSM rP0 rP1 bridge
    layer9_sm_sliding_buddy layer9_pm_sliding_buddy0 layer9_pm_sliding_buddy1
    (by native_decide) (by native_decide) hqpos hkpos hvpos hqfull hkfull hvfull
    hcuQ hcuK rfl rfl rfl rfl hfull hfull' rfl rfl rfl rfl rfl rfl

/-! ### Pure-distributed layer-10 post-attention projection and residual cascade. -/

private theorem l10d_reshape (g : GraphDecl) (init : Store) (k r i o hd : Nat)
    (tl : List Nat) (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_reshape", ins := [i], outs := [o], params := hd :: tl })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributed g init o = fw_view (hd :: tl) (denoteGraphDistributed g init i) :=
  distributed_reduce1 g init k _ i o (fw_view (hd :: tl)) hk hn (by simp)
    (fun st => applyNode_fw_reshape_out g st r i o (hd :: tl)) hdn hdw hpn hpw

private theorem l10d_view (g : GraphDecl) (init : Store) (k r i o hd : Nat)
    (tl : List Nat) (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_view", ins := [i], outs := [o], params := hd :: tl })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributed g init o = fw_view (hd :: tl) (denoteGraphDistributed g init i) :=
  distributed_reduce1 g init k _ i o (fw_view (hd :: tl)) hk hn (by simp)
    (fun st => applyNode_fw_view_out g st r hd tl i o) hdn hdw hpn hpw

private theorem l10d_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
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
    (fun st => applyNode_fw_mix_precision_linear_out_1p g st r x w o)
    hdn hdw hpn hpx hpw

private theorem l10d_float (g : GraphDecl) (init : Store) (k r i o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = { rank := r, op := "OpName.FW_float", ins := [i], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, i ∉ n.outs) :
    denoteGraphDistributed g init o = denoteGraphDistributed g init i := by
  have h := distributed_reduce1 g init k _ i o id hk hn (by simp)
    (fun st => applyNode_fw_float_out g st r i o []) hdn hdw hpn hpw
  simpa only [id_eq] using h

private theorem l10d_add (g : GraphDecl) (init : Store) (k r x y o : Nat)
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
    (fun st => applyNode_fw_add2_out g st r x y o) hdn hdw hpn hpx hpy

private theorem l10d_reshape5183_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5183)
      (denoteGraphDistributed pm initPM 9113) (denoteGraphDistributed pm initPM 9114)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5182 5182 9111 9112
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5182_distributed initSM initPM hSM hPM hInit)
  have rs := l10d_reshape sm initSM 361 0 5182 5183 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l10d_reshape pm initPM 783 0 9111 9113 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l10d_reshape pm initPM 784 1 9112 9114 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine ⟨?_, by rw [rs]; rfl, by rw [r0]; rfl, by rw [r1]; rfl, by decide⟩
  rw [rs, h.value, fw_view_allGather0_reshape_16_64_2_g12 _ _ h.shard0_shape h.shard1_shape,
    r0, r1]

/-- Pure-distributed exact 2-TP reconstruction of the layer-10 attention reshape. -/
theorem recon_intermediateGoal_5183_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5183
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5183 5183 9113 9114
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l10d_reshape5183_rel initSM initPM hSM hPM hInit)

private theorem l10d_reshape5184_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5184)
      (denoteGraphDistributed pm initPM 9119) (denoteGraphDistributed pm initPM 9120)
      [4096, 1024] [2048, 1024] := by
  have h := l10d_reshape5183_rel initSM initPM hSM hPM hInit
  have rs := l10d_reshape sm initSM 362 0 5183 5184 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l10d_reshape pm initPM 785 0 9113 9119 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l10d_reshape pm initPM 786 1 9114 9120 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5184 = denoteGraphDistributed sm initSM 5183 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 9119 = denoteGraphDistributed pm initPM 9113 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 9120 = denoteGraphDistributed pm initPM 9114 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of the layer-10 identity reshape. -/
theorem recon_intermediateGoal_5184_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5184
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5184 5184 9119 9120
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l10d_reshape5184_rel initSM initPM hSM hPM hInit)

private theorem l10d_linear5186_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5186)
      (denoteGraphDistributed pm initPM 9123) (denoteGraphDistributed pm initPM 9124)
      [4096, 1024] [2048, 1024] := by
  have h := l10d_reshape5184_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5185
    (by native_decide) 5185 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5185
    (by native_decide) 5185 [1024, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5185).shape = [1024, 1024] := by
    rw [← hw]; exact hws
  have rs := l10d_linear sm initSM 363 0 5184 5185 5186 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10d_linear pm initPM 787 0 9119 5185 9123 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10d_linear pm initPM 788 1 9120 5185 9124 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 1024 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 1024 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 1024 _ _ h.shard1_shape hpw

/-- Pure-distributed exact 2-TP reconstruction of the layer-10 output projection. -/
theorem recon_intermediateGoal_5186_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5186
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5186 5186 9123 9124
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l10d_linear5186_rel initSM initPM hSM hPM hInit)

private theorem l10d_view5187_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5187)
      (denoteGraphDistributed pm initPM 9133) (denoteGraphDistributed pm initPM 9134)
      [4096, 1024] [2048, 1024] := by
  have h := l10d_linear5186_rel initSM initPM hSM hPM hInit
  have rs := l10d_view sm initSM 364 0 5186 5187 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l10d_view pm initPM 789 0 9123 9133 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l10d_view pm initPM 790 1 9124 9134 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5187 = denoteGraphDistributed sm initSM 5186 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 9133 = denoteGraphDistributed pm initPM 9123 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 9134 = denoteGraphDistributed pm initPM 9124 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of the layer-10 identity view. -/
theorem recon_intermediateGoal_5187_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5187
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5187 5187 9133 9134
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l10d_view5187_rel initSM initPM hSM hPM hInit)

private theorem l10d_float5188_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5188)
      (denoteGraphDistributed pm initPM 9137) (denoteGraphDistributed pm initPM 9138)
      [4096, 1024] [2048, 1024] := by
  have h := l10d_view5187_rel initSM initPM hSM hPM hInit
  have rs := l10d_float sm initSM 365 0 5187 5188 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10d_float pm initPM 791 0 9133 9137 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10d_float pm initPM 792 1 9134 9138 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  exact ⟨by rw [rs, h.value, r0, r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of the layer-10 post-projection float. -/
theorem recon_intermediateGoal_5188_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5188
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5188 5188 9137 9138
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l10d_float5188_rel initSM initPM hSM hPM hInit)

private theorem l10d_carry7855_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7855)
      (denoteGraphDistributed pm initPM 15433) (denoteGraphDistributed pm initPM 15441)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5168 5168 9067 9068
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5168_distributed initSM initPM hSM hPM hInit)
  have rs := distributed_reduce1 sm initSM 353
    { rank := 0, op := "OpName.FW_multiref", ins := [5168], outs := [7851, 7855], params := [2] }
    5168 7855 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' sm st 0 5168 7851 7855 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce1 pm initPM 767
    { rank := 0, op := "OpName.FW_multiref", ins := [9067], outs := [15429, 15433], params := [2] }
    9067 15433 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 0 9067 15429 15433 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce1 pm initPM 768
    { rank := 1, op := "OpName.FW_multiref", ins := [9068], outs := [15437, 15441], params := [2] }
    9068 15441 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 1 9068 15437 15441 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rs r0 r1
  exact ⟨by rw [rs, h.value, ← r0, ← r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP `mref2`-second carry of the layer-10 residual. -/
theorem recon_intermediateGoal_7855_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7855
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_7855 7855 15433 15441
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l10d_carry7855_rel initSM initPM hSM hPM hInit)

/-- Pure-distributed exact 2-TP layer-10 residual add `7855 + 5188`. -/
theorem recon_intermediateGoal_5189_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5189
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have ha := l10d_carry7855_rel initSM initPM hSM hPM hInit
  have hb := l10d_float5188_rel initSM initPM hSM hPM hInit
  have rs := l10d_add sm initSM 366 0 7855 5188 5189
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10d_add pm initPM 793 0 15433 9137 9141
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10d_add pm initPM 794 1 15441 9138 9142
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hv : denoteGraphDistributed sm initSM 5189 = allGatherPrimDimN 0 pm.numRanks 0
      [denoteGraphDistributed pm initPM 9141, denoteGraphDistributed pm initPM 9142] := by
    rw [rs, ha.value, hb.value, show pm.numRanks = 2 from rfl,
      fw_add_allGather0_commute_2_2048_1024 _ _ _ _ ha.shard0_shape ha.shard1_shape
        hb.shard0_shape hb.shard1_shape, ← r0, ← r1]
  have hs0 : (denoteGraphDistributed pm initPM 9141).shape = [2048, 1024] := by
    rw [r0]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.shard0_shape hb.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 9142).shape = [2048, 1024] := by
    rw [r1]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.shard1_shape hb.shard1_shape
  have hs : (denoteGraphDistributed sm initSM 5189).shape = [4096, 1024] := by
    rw [rs]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.full_shape hb.full_shape
  exact wrap_2tp_allGather_gen _ _ intermediateGoal_5189 5189 9141 9142
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide) hv hs hs0 hs1

#print axioms recon_intermediateGoal_7835_distributed
#print axioms recon_intermediateGoal_5146_distributed
#print axioms recon_intermediateGoal_7824_distributed
#print axioms recon_intermediateGoal_5166_distributed
#print axioms recon_intermediateGoal_5167_distributed
#print axioms recon_intermediateGoal_5168_distributed
#print axioms recon_intermediateGoal_5170_distributed
#print axioms recon_intermediateGoal_5172_distributed
#print axioms recon_intermediateGoal_5174_distributed
#print axioms recon_intermediateGoal_5176_distributed
#print axioms recon_intermediateGoal_5178_distributed
#print axioms recon_intermediateGoal_5179_distributed
#print axioms recon_intermediateGoal_5182_distributed
#print axioms recon_intermediateGoal_5189_distributed

end TrainVerify.Denote.GeneratedPatterns
