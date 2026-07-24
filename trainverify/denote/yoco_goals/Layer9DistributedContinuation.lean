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

#print axioms recon_intermediateGoal_7835_distributed
#print axioms recon_intermediateGoal_5146_distributed
#print axioms recon_intermediateGoal_7824_distributed
#print axioms recon_intermediateGoal_5166_distributed
#print axioms recon_intermediateGoal_5167_distributed
#print axioms recon_intermediateGoal_5168_distributed

end TrainVerify.Denote.GeneratedPatterns
