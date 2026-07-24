/- Faithful pure-distributed continuation at the layer-6 MoE boundary. -/
import denote.yoco_goals.Layer2DistributedMigration

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

private theorem l6d_token7679_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7679)
      (denoteGraphDistributed pm initPM 15078) (denoteGraphDistributed pm initPM 15101)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_4975 4975 8401 8402
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4975_distributed initSM initPM hSM hPM hInit)
  have s := distributed_reduce1 sm initSM 213
    { rank := 0, op := "OpName.FW_multiref", ins := [4975],
      outs := [7675, 7679, 7683, 7687, 7691], params := [5] }
    4975 7679 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos1_out sm st 0 4975 7675 7679 7683 7687 7691
      (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 487
    { rank := 0, op := "OpName.FW_multiref", ins := [8401],
      outs := [15074, 15078, 15082, 15086, 15090], params := [5] }
    8401 15078 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos1_out pm st 0 8401 15074 15078 15082 15086 15090
      (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 488
    { rank := 1, op := "OpName.FW_multiref", ins := [8402],
      outs := [15097, 15101, 15105, 15109, 15113], params := [5] }
    8402 15101 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref5_at_pos1_out pm st 1 8402 15097 15101 15105 15109 15113
      (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  exact ⟨by rw [s, h.value, ← p0, ← p1], by rw [s]; exact h.full_shape,
    by rw [p0]; exact h.shard0_shape, by rw [p1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of the layer-6 MoE token input
    (`mref5` position 1). -/
theorem recon_intermediateGoal_7679_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7679
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_7679 7679 15078 15101
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l6d_token7679_rel initSM initPM hSM hPM hInit)

private def layer6SmMoe : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [7679, 4979, 4980, 4982, 4983], outs := [4984], params := [64, 0, 64, 8] }
private def layer6PmMoe0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [15078, 8411, 8413, 8417, 8419], outs := [8421], params := [64, 0, 32, 8] }
private def layer6PmMoe1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm",
    ins := [15101, 8412, 8414, 8418, 8420], outs := [8422], params := [64, 32, 64, 8] }

set_option maxRecDepth 1000000 in
private theorem layer6_sm_node226 : sm.nodes[226]'(by native_decide) = layer6SmMoe := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer6_pm_node513 : pm.nodes[513]'(by native_decide) = layer6PmMoe0 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer6_pm_node516 : pm.nodes[516]'(by native_decide) = layer6PmMoe1 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer6_sm_buddies : sm.replicaBuddies layer6SmMoe = [layer6SmMoe] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer6_pm_buddies0 :
    pm.replicaBuddies layer6PmMoe0 = [layer6PmMoe0, layer6PmMoe1] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer6_pm_buddies1 :
    pm.replicaBuddies layer6PmMoe1 = [layer6PmMoe0, layer6PmMoe1] := by native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
/-- Faithful pure-distributed full-expert reconstruction of the layer-6 MoE boundary. -/
theorem recon_intermediateGoal_4984_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4984
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have hi := l6d_token7679_rel initSM initPM hSM hPM hInit
  have hrp := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_4979 4979 8411 8412
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4979_distributed initSM initPM hSM hPM hInit)
  have hrm := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_4980 4980 8413 8414
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4980_distributed initSM initPM hSM hPM hInit)

  have hW13 := hInit initGoal_4982 (by native_decide)
  have hW2 := hInit initGoal_4983 (by native_decide)
  have hsW13 := hW13.2.1
  have hsW2 := hW2.2.1
  simp only [initGoal_4982, List.map, List.cons.injEq, and_true] at hsW13
  simp only [initGoal_4983, List.map, List.cons.injEq, and_true] at hsW2
  have hsW13A : (denoteGraphDistributed pm initPM 8417).shape = [32, 1024, 1024] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8417
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW13.1
  have hsW13B : (denoteGraphDistributed pm initPM 8418).shape = [32, 1024, 1024] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8418
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW13.2
  have hsW2A : (denoteGraphDistributed pm initPM 8419).shape = [32, 1024, 512] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8419
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW2.1
  have hsW2B : (denoteGraphDistributed pm initPM 8420).shape = [32, 1024, 512] := by
    rw [denoteGraphDistributed,
      foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8420
        layer1_pm_nodes_nonempty (by native_decide)]
    exact hsW2.2
  have hbrW13 : denoteGraphDistributed sm initSM 4982 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 8417, denoteGraphDistributed pm initPM 8418] := by
    have hv := hW13.2.2
    rw [reconstructForGoal_of_not_replicated initGoal_4982 pm.numRanks _ rfl] at hv
    simp only [initGoal_4982, List.map] at hv
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
      (by rw [hsW13.1]; decide)] at hv
    have ds : denoteGraphDistributed sm initSM 4982 = initSM 4982 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written sm sm.nodes initSM 4982
        layer1_sm_nodes_nonempty (by native_decide)
    have dp0 : denoteGraphDistributed pm initPM 8417 = initPM 8417 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8417
        layer1_pm_nodes_nonempty (by native_decide)
    have dp1 : denoteGraphDistributed pm initPM 8418 = initPM 8418 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8418
        layer1_pm_nodes_nonempty (by native_decide)
    rw [ds, dp0, dp1]
    exact hv
  have hbrW2 : denoteGraphDistributed sm initSM 4983 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 8419, denoteGraphDistributed pm initPM 8420] := by
    have hv := hW2.2.2
    rw [reconstructForGoal_of_not_replicated initGoal_4983 pm.numRanks _ rfl] at hv
    simp only [initGoal_4983, List.map] at hv
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm.numRanks 0 _ _ []
      (by rw [hsW2.1]; decide)] at hv
    have ds : denoteGraphDistributed sm initSM 4983 = initSM 4983 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written sm sm.nodes initSM 4983
        layer1_sm_nodes_nonempty (by native_decide)
    have dp0 : denoteGraphDistributed pm initPM 8419 = initPM 8419 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8419
        layer1_pm_nodes_nonempty (by native_decide)
    have dp1 : denoteGraphDistributed pm initPM 8420 = initPM 8420 := by
      rw [denoteGraphDistributed]
      exact foldl_applyNodeDistributed_at_not_written pm pm.nodes initPM 8420
        layer1_pm_nodes_nonempty (by native_decide)
    rw [ds, dp0, dp1]
    exact hv
  have hW13single : allGatherPrimDimN 0 1 0 [denoteGraphDistributed sm initSM 4982] =
      denoteGraphDistributed sm initSM 4982 := by
    have hs : (denoteGraphDistributed sm initSM 4982).shape = [64, 1024, 1024] := by
      rw [hbrW13, allGatherPrimDimN_shape 0 2 _ [32, 1024, 1024] (by simp [hsW13A])]
      simp [List.set]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hs]; decide)
  have hW2single : allGatherPrimDimN 0 1 0 [denoteGraphDistributed sm initSM 4983] =
      denoteGraphDistributed sm initSM 4983 := by
    have hs : (denoteGraphDistributed sm initSM 4983).shape = [64, 1024, 512] := by
      rw [hbrW2, allGatherPrimDimN_shape 0 2 _ [32, 1024, 512] (by simp [hsW2A])]
      simp [List.set]
    exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hs]; decide)

  have hSMout : denoteGraphDistributed sm initSM 4984 =
      fw_all2all_moe_gmm_full (denoteGraphDistributed sm initSM 7679)
        (denoteGraphDistributed sm initSM 4979) (denoteGraphDistributed sm initSM 4980)
        [denoteGraphDistributed pm initPM 8417, denoteGraphDistributed pm initPM 8418]
        [denoteGraphDistributed pm initPM 8419, denoteGraphDistributed pm initPM 8420]
        64 8 (((10 : Nat) : Scalar)) := by
    have hk : 226 < sm.nodes.length := by native_decide
    rw [distributed_moe_reduce sm initSM 226 layer6SmMoe 4984 hk
      (show sm.nodes[226]'hk = layer6SmMoe from layer6_sm_node226)
      rfl rfl (by native_decide) (by native_decide)]
    unfold applyNodeFullExpertMoE_value
    rw [layer6_sm_buddies]
    simp only [layer6SmMoe, List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    rw [foldl_take_distributed_eq sm initSM 7679 226 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 4979 226 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 4980 226 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 4982 226 (by native_decide) (by native_decide),
      foldl_take_distributed_eq sm initSM 4983 226 (by native_decide) (by native_decide)]
    unfold fw_all2all_moe_gmm_full
    simp only [List.length_cons, List.length_nil]
    rw [hW13single, hW2single, hbrW13, hbrW2]
  have hP0 : denoteGraphDistributed pm initPM 8421 =
      fw_all2all_moe_gmm_full (denoteGraphDistributed pm initPM 15078)
        (denoteGraphDistributed pm initPM 8411) (denoteGraphDistributed pm initPM 8413)
        [denoteGraphDistributed pm initPM 8417, denoteGraphDistributed pm initPM 8418]
        [denoteGraphDistributed pm initPM 8419, denoteGraphDistributed pm initPM 8420]
        64 8 (((10 : Nat) : Scalar)) := by
    have hk : 513 < pm.nodes.length := by native_decide
    rw [distributed_moe_reduce pm initPM 513 layer6PmMoe0 8421 hk
      (show pm.nodes[513]'hk = layer6PmMoe0 from layer6_pm_node513)
      rfl rfl (by native_decide) (by native_decide)]
    unfold applyNodeFullExpertMoE_value
    rw [layer6_pm_buddies0]
    simp only [layer6PmMoe0, layer6PmMoe1, List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    rw [foldl_take_distributed_eq pm initPM 15078 513 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8411 513 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8413 513 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8417 513 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8418 513 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8419 513 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8420 513 (by native_decide) (by native_decide)]
  have hP1 : denoteGraphDistributed pm initPM 8422 =
      fw_all2all_moe_gmm_full (denoteGraphDistributed pm initPM 15101)
        (denoteGraphDistributed pm initPM 8412) (denoteGraphDistributed pm initPM 8414)
        [denoteGraphDistributed pm initPM 8417, denoteGraphDistributed pm initPM 8418]
        [denoteGraphDistributed pm initPM 8419, denoteGraphDistributed pm initPM 8420]
        64 8 (((10 : Nat) : Scalar)) := by
    have hk : 516 < pm.nodes.length := by native_decide
    rw [distributed_moe_reduce pm initPM 516 layer6PmMoe1 8422 hk
      (show pm.nodes[516]'hk = layer6PmMoe1 from layer6_pm_node516)
      rfl rfl (by native_decide) (by native_decide)]
    unfold applyNodeFullExpertMoE_value
    rw [layer6_pm_buddies1]
    simp only [layer6PmMoe0, layer6PmMoe1, List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, List.getElem?_nil, Option.getD_some, Option.getD_none]
    rw [foldl_take_distributed_eq pm initPM 15101 516 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8412 516 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8414 516 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8417 516 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8418 516 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8419 516 (by native_decide) (by native_decide),
      foldl_take_distributed_eq pm initPM 8420 516 (by native_decide) (by native_decide)]

  have hc := fw_all2all_moe_gmm_full_split_commute_2
    (denoteGraphDistributed pm initPM 15078) (denoteGraphDistributed pm initPM 15101)
    (denoteGraphDistributed pm initPM 8411) (denoteGraphDistributed pm initPM 8412)
    (denoteGraphDistributed pm initPM 8413) (denoteGraphDistributed pm initPM 8414)
    (denoteGraphDistributed pm initPM 8417) (denoteGraphDistributed pm initPM 8418)
    (denoteGraphDistributed pm initPM 8419) (denoteGraphDistributed pm initPM 8420)
    2048 1024 32 8 1024 512 (((10 : Nat) : Scalar))
    (by omega) (by omega) (by omega) (by omega) (by omega) rfl
    hi.shard0_shape hi.shard1_shape hrp.shard0_shape hrp.shard1_shape
    hrm.shard0_shape hrm.shard1_shape hsW13A hsW13B hsW2A hsW2B
  have hval : denoteGraphDistributed sm initSM 4984 = allGatherPrimDimN 0 pm.numRanks 0
      [denoteGraphDistributed pm initPM 8421, denoteGraphDistributed pm initPM 8422] := by
    rw [hSMout, hi.value, hrp.value, hrm.value, hc, ← hP0, ← hP1,
      show pm.numRanks = 2 from rfl]
  have hsP0 : (denoteGraphDistributed pm initPM 8421).shape = [2048, 1024] := by
    rw [hP0]
    exact fw_all2all_moe_gmm_full_shape
      (input := denoteGraphDistributed pm initPM 15078)
      (rp := denoteGraphDistributed pm initPM 8411)
      (rm := denoteGraphDistributed pm initPM 8413)
      (w13s := [denoteGraphDistributed pm initPM 8417, denoteGraphDistributed pm initPM 8418])
      (w2s := [denoteGraphDistributed pm initPM 8419, denoteGraphDistributed pm initPM 8420])
      (numExp := 64) (topK := 8) (swigluLimit := (((10 : Nat) : Scalar)))
      (lDim := 2048) (hModel := 1024)
      (by rw [hi.shard0_shape]; rfl) (by rw [hi.shard0_shape]; rfl)
  have hsP1 : (denoteGraphDistributed pm initPM 8422).shape = [2048, 1024] := by
    rw [hP1]
    exact fw_all2all_moe_gmm_full_shape
      (input := denoteGraphDistributed pm initPM 15101)
      (rp := denoteGraphDistributed pm initPM 8412)
      (rm := denoteGraphDistributed pm initPM 8414)
      (w13s := [denoteGraphDistributed pm initPM 8417, denoteGraphDistributed pm initPM 8418])
      (w2s := [denoteGraphDistributed pm initPM 8419, denoteGraphDistributed pm initPM 8420])
      (numExp := 64) (topK := 8) (swigluLimit := (((10 : Nat) : Scalar)))
      (lDim := 2048) (hModel := 1024)
      (by rw [hi.shard1_shape]; rfl) (by rw [hi.shard1_shape]; rfl)
  have hsSM : (denoteGraphDistributed sm initSM 4984).shape = [4096, 1024] := by
    rw [hval, show pm.numRanks = 2 from rfl,
      allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hsP0])]
    simp [List.set]
  exact wrap_2tp_allGather_gen _ _ intermediateGoal_4984 4984 8421 8422
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    hval hsSM hsP0 hsP1

/-- The second `mref2` copy of the pre-MoE residual, carried to the cross-block add. -/
theorem recon_intermediateGoal_7668_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7668
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_4973 4973 8397 8398
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4973_distributed initSM initPM hSM hPM hInit)
  have s := distributed_reduce1 sm initSM 211
    { rank := 0, op := "OpName.FW_multiref", ins := [4973], outs := [7664, 7668], params := [2] }
    4973 7668 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' sm st 0 4973 7664 7668 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 483
    { rank := 0, op := "OpName.FW_multiref", ins := [8397], outs := [15055, 15059], params := [2] }
    8397 15059 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 0 8397 15055 15059 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 484
    { rank := 1, op := "OpName.FW_multiref", ins := [8398], outs := [15063, 15067], params := [2] }
    8398 15067 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 1 8398 15063 15067 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  exact Gather2Rel.to_initGoalHolds _ _ intermediateGoal_7668 7668 15059 15067
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    ⟨by rw [s, h.value, ← p0, ← p1], by rw [s]; exact h.full_shape,
      by rw [p0]; exact h.shard0_shape, by rw [p1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed post-MoE residual add `4984 + 5003`. -/
theorem recon_intermediateGoal_5004_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5004
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have ha := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_4984 4984 8421 8422
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_4984_distributed initSM initPM hSM hPM hInit)
  have hb := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5003 5003 8495 8496
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5003_distributed initSM initPM hSM hPM hInit)
  have s := distributed_reduce2 sm initSM 233
    { rank := 0, op := "OpName.FW_add", ins := [4984, 5003], outs := [5004] }
    4984 5003 5004 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_add2_out sm st 0 4984 5003 5004)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce2 pm initPM 527
    { rank := 0, op := "OpName.FW_add", ins := [8421, 8495], outs := [8499] }
    8421 8495 8499 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_add2_out pm st 0 8421 8495 8499)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce2 pm initPM 528
    { rank := 1, op := "OpName.FW_add", ins := [8422, 8496], outs := [8500] }
    8422 8496 8500 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_add2_out pm st 1 8422 8496 8500)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hv : denoteGraphDistributed sm initSM 5004 = allGatherPrimDimN 0 pm.numRanks 0
      [denoteGraphDistributed pm initPM 8499, denoteGraphDistributed pm initPM 8500] := by
    rw [s, ha.value, hb.value, show pm.numRanks = 2 from rfl,
      fw_add_allGather0_commute_2_2048_1024 _ _ _ _ ha.shard0_shape ha.shard1_shape
        hb.shard0_shape hb.shard1_shape, ← p0, ← p1]
  have hs0 : (denoteGraphDistributed pm initPM 8499).shape = [2048, 1024] := by
    rw [p0]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.shard0_shape hb.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 8500).shape = [2048, 1024] := by
    rw [p1]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.shard1_shape hb.shard1_shape
  have hs : (denoteGraphDistributed sm initSM 5004).shape = [4096, 1024] := by
    rw [s]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.full_shape hb.full_shape
  exact wrap_2tp_allGather_gen _ _ intermediateGoal_5004 5004 8499 8500
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide) hv hs hs0 hs1

/-- Pure-distributed identity float following the post-MoE residual add. -/
theorem recon_intermediateGoal_5005_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5005
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5004 5004 8499 8500
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5004_distributed initSM initPM hSM hPM hInit)
  have s := distributed_reduce1 sm initSM 234
    { rank := 0, op := "OpName.FW_float", ins := [5004], outs := [5005] }
    5004 5005 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_float_out sm st 0 5004 5005 [])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 529
    { rank := 0, op := "OpName.FW_float", ins := [8499], outs := [8505] }
    8499 8505 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_float_out pm st 0 8499 8505 [])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 530
    { rank := 1, op := "OpName.FW_float", ins := [8500], outs := [8506] }
    8500 8506 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_float_out pm st 1 8500 8506 [])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  exact Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5005 5005 8505 8506
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    ⟨by rw [s, h.value, ← p0, ← p1], by rw [s]; exact h.full_shape,
      by rw [p0]; exact h.shard0_shape, by rw [p1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed cross-block residual output `7668 + 5005`. -/
theorem recon_intermediateGoal_5006_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5006
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have ha := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_7668 7668 15059 15067
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_7668_distributed initSM initPM hSM hPM hInit)
  have hb := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5005 5005 8505 8506
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5005_distributed initSM initPM hSM hPM hInit)
  have s := distributed_reduce2 sm initSM 235
    { rank := 0, op := "OpName.FW_add", ins := [7668, 5005], outs := [5006] }
    7668 5005 5006 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_add2_out sm st 0 7668 5005 5006)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce2 pm initPM 531
    { rank := 0, op := "OpName.FW_add", ins := [15059, 8505], outs := [8509] }
    15059 8505 8509 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_add2_out pm st 0 15059 8505 8509)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce2 pm initPM 532
    { rank := 1, op := "OpName.FW_add", ins := [15067, 8506], outs := [8510] }
    15067 8506 8510 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_add2_out pm st 1 15067 8506 8510)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hv : denoteGraphDistributed sm initSM 5006 = allGatherPrimDimN 0 pm.numRanks 0
      [denoteGraphDistributed pm initPM 8509, denoteGraphDistributed pm initPM 8510] := by
    rw [s, ha.value, hb.value, show pm.numRanks = 2 from rfl,
      fw_add_allGather0_commute_2_2048_1024 _ _ _ _ ha.shard0_shape ha.shard1_shape
        hb.shard0_shape hb.shard1_shape, ← p0, ← p1]
  have hs0 : (denoteGraphDistributed pm initPM 8509).shape = [2048, 1024] := by
    rw [p0]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.shard0_shape hb.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 8510).shape = [2048, 1024] := by
    rw [p1]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.shard1_shape hb.shard1_shape
  have hs : (denoteGraphDistributed sm initSM 5006).shape = [4096, 1024] := by
    rw [s]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.full_shape hb.full_shape
  exact wrap_2tp_allGather_gen _ _ intermediateGoal_5006 5006 8509 8510
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide) hv hs hs0 hs1

private theorem l6d_rms (g : GraphDecl) (init : Store) (k r x w o : Nat)
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

private theorem l6d_per_head_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
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

private theorem l6d_rms5008_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5008)
      (denoteGraphDistributed pm initPM 8513) (denoteGraphDistributed pm initPM 8514)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5006 5006 8509 8510
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5006_distributed initSM initPM hSM hPM hInit)
  have s := distributed_reduce1 sm initSM 236
    { rank := 0, op := "OpName.FW_multiref", ins := [5006], outs := [7695, 7699], params := [2] }
    5006 7695 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out sm st 0 5006 7695 7699)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 533
    { rank := 0, op := "OpName.FW_multiref", ins := [8509], outs := [15117, 15121], params := [2] }
    8509 15117 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 0 8509 15117 15121)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 534
    { rank := 1, op := "OpName.FW_multiref", ins := [8510], outs := [15125, 15129], params := [2] }
    8510 15125 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 1 8510 15125 15129)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5007
    (by native_decide) 5007 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have rs := l6d_rms sm initSM 237 0 7695 5007 5008 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l6d_rms pm initPM 535 0 15117 5007 8513 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l6d_rms pm initPM 536 1 15125 5007 8514 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15117).shape = [2048, 1024] := by
    rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15125).shape = [2048, 1024] := by
    rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs0 hs1,
      r0, r1]
  · rw [rs]; exact fw_rms_norm_shape2 _ _ 4096 1024 (by rw [s]; exact h.full_shape)
  · rw [r0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs0
  · rw [r1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs1

/-- Pure-distributed exact 2-TP reconstruction of the layer-6 attention RMSNorm. -/
theorem recon_intermediateGoal_5008_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5008
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5008 5008 8513 8514
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l6d_rms5008_rel initSM initPM hSM hPM hInit)

private theorem l6d_q5010_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5010)
      (denoteGraphDistributed pm initPM 8515) (denoteGraphDistributed pm initPM 8516)
      [4096, 16, 64] [2048, 16, 64] := by
  have h := l6d_rms5008_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 238
    { rank := 0, op := "OpName.FW_multiref", ins := [5008], outs := [7704, 7708, 7712], params := [3] }
    5008 7704 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' sm st 0 5008 7704 7708 7712)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 537
    { rank := 0, op := "OpName.FW_multiref", ins := [8513], outs := [15134, 15138, 15142], params := [3] }
    8513 15134 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' pm st 0 8513 15134 15138 15142)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 538
    { rank := 1, op := "OpName.FW_multiref", ins := [8514], outs := [15147, 15151, 15155], params := [3] }
    8514 15147 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_first_out' pm st 1 8514 15147 15151 15155)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5009
    (by native_decide) 5009 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5009
    (by native_decide) 5009 [16, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5009).shape = [16, 64, 1024] := by rw [← hw]; exact hws
  have rs := l6d_per_head_linear sm initSM 239 0 7704 5009 5010 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l6d_per_head_linear pm initPM 539 0 15134 5009 8515 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l6d_per_head_linear pm initPM 542 1 15147 5009 8516 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15134).shape = [2048, 1024] := by rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15147).shape = [2048, 1024] := by rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 16 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, r0, r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 16 64 (by rw [s]; exact h.full_shape) hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs0 hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 16 64 hs1 hpw

/-- Pure-distributed exact 2-TP reconstruction of the layer-6 Q projection. -/
theorem recon_intermediateGoal_5010_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5010
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5010 5010 8515 8516
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl
    (l6d_q5010_rel initSM initPM hSM hPM hInit)

private theorem l6d_k5012_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5012)
      (denoteGraphDistributed pm initPM 8527) (denoteGraphDistributed pm initPM 8528)
      [4096, 4, 64] [2048, 4, 64] := by
  have h := l6d_rms5008_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 238
    { rank := 0, op := "OpName.FW_multiref", ins := [5008], outs := [7704, 7708, 7712], params := [3] }
    5008 7708 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' sm st 0 5008 7704 7708 7712 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 537
    { rank := 0, op := "OpName.FW_multiref", ins := [8513], outs := [15134, 15138, 15142], params := [3] }
    8513 15138 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' pm st 0 8513 15134 15138 15142 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 538
    { rank := 1, op := "OpName.FW_multiref", ins := [8514], outs := [15147, 15151, 15155], params := [3] }
    8514 15151 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_second_out' pm st 1 8514 15147 15151 15155 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5011
    (by native_decide) 5011 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5011
    (by native_decide) 5011 [4, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5011).shape = [4, 64, 1024] := by rw [← hw]; exact hws
  have rs := l6d_per_head_linear sm initSM 240 0 7708 5011 5012 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l6d_per_head_linear pm initPM 540 0 15138 5011 8527 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l6d_per_head_linear pm initPM 543 1 15151 5011 8528 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15138).shape = [2048, 1024] := by rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15151).shape = [2048, 1024] := by rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, r0, r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64 (by rw [s]; exact h.full_shape) hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs0 hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs1 hpw

/-- Pure-distributed exact 2-TP reconstruction of the layer-6 K projection. -/
theorem recon_intermediateGoal_5012_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5012
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5012 5012 8527 8528
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l6d_k5012_rel initSM initPM hSM hPM hInit)

private theorem l6d_v5014_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5014)
      (denoteGraphDistributed pm initPM 8537) (denoteGraphDistributed pm initPM 8538)
      [4096, 4, 64] [2048, 4, 64] := by
  have h := l6d_rms5008_rel initSM initPM hSM hPM hInit
  have s := distributed_reduce1 sm initSM 238
    { rank := 0, op := "OpName.FW_multiref", ins := [5008], outs := [7704, 7708, 7712], params := [3] }
    5008 7712 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' sm st 0 5008 7704 7708 7712 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p0 := distributed_reduce1 pm initPM 537
    { rank := 0, op := "OpName.FW_multiref", ins := [8513], outs := [15134, 15138, 15142], params := [3] }
    8513 15142 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' pm st 0 8513 15134 15138 15142 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have p1 := distributed_reduce1 pm initPM 538
    { rank := 1, op := "OpName.FW_multiref", ins := [8514], outs := [15147, 15151, 15155], params := [3] }
    8514 15155 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref3_third_out' pm st 1 8514 15147 15151 15155 (by decide) (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at s p0 p1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5013
    (by native_decide) 5013 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5013
    (by native_decide) 5013 [4, 64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5013).shape = [4, 64, 1024] := by rw [← hw]; exact hws
  have rs := l6d_per_head_linear sm initSM 241 0 7712 5013 5014 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l6d_per_head_linear pm initPM 541 0 15142 5013 8537 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l6d_per_head_linear pm initPM 544 1 15155 5013 8538 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15142).shape = [2048, 1024] := by rw [p0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15155).shape = [2048, 1024] := by rw [p1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, s, h.value, ← p0, ← p1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, r0, r1]
  · rw [rs]; exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64 (by rw [s]; exact h.full_shape) hws
  · rw [r0]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs0 hpw
  · rw [r1]; exact fw_per_head_linear_shape_3d _ _ 2048 1024 4 64 hs1 hpw

/-- Pure-distributed exact 2-TP reconstruction of the layer-6 V projection. -/
theorem recon_intermediateGoal_5014_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5014
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5014 5014 8537 8538
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l6d_v5014_rel initSM initPM hSM hPM hInit)

private theorem l6d_chunk (g : GraphDecl) (init : Store) (k r i o d : Nat)
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

/-- Distributed cache agreement for the layer-6 PM rotary-cache replica. -/
private theorem l6d_rotary_cache_11859 (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraphDistributed sm initSM 4691 = denoteGraphDistributed pm initPM 11859 := by
  have hsource := sm_pm_rotary_cache_agree initSM initPM hInit 11859 6 (by norm_num) rfl
  have hbase := distributed_init_singleton_value initSM initPM hInit initGoal_4691
    (by native_decide) 4691 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hcopy : denoteGraphDistributed pm initPM 11859 = id (denoteGraphDistributed pm initPM 4691) :=
    distributed_reduce1 pm initPM 14
      { rank := 1, op := "OpName.FW_multiref", ins := [4691],
        outs := (List.range 12).map (fun r => 11853 + r),
        params := [((List.range 12).map (fun r => 11853 + r)).length] }
      4691 11859 id (by native_decide) (by native_decide) (by decide)
      (fun st => by
        rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm st _ (by decide) (by decide)]
        rw [applyNode_fw_multiref_mem_out pm st 1 4691
          ((List.range 12).map (fun r => 11853 + r)) 11859 (by native_decide), id_eq])
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  rw [hcopy, id_eq]
  exact hbase

set_option maxHeartbeats 8000000 in
-- Concrete graph reduction for both rotary outputs requires the larger elaboration budget.
private theorem l6d_rotary5016_5017_rels (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5016)
      (denoteGraphDistributed pm initPM 8549) (denoteGraphDistributed pm initPM 8550)
      [4096, 16, 64] [2048, 16, 64] ∧
    Gather2Rel (denoteGraphDistributed sm initSM 5017)
      (denoteGraphDistributed pm initPM 8551) (denoteGraphDistributed pm initPM 8552)
      [4096, 4, 64] [2048, 4, 64] := by
  have hq := l6d_q5010_rel initSM initPM hSM hPM hInit
  have hk := l6d_k5012_rel initSM initPM hSM hPM hInit
  have hcache := l6d_rotary_cache_11859 initSM initPM hInit
  have hpos := distributed_init_singleton_value initSM initPM hInit initGoal_5015
    (by native_decide) 5015 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hspos := distributed_init_singleton_shape initSM initPM hInit initGoal_5015
    (by native_decide) 5015 [4096] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have c0 := l6d_chunk pm initPM 6 0 5015 8547 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c1 := l6d_chunk pm initPM 19 1 5015 8548 0 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have c0' : denoteGraphDistributed pm initPM 8547 = chunkPrimDimN 0 2 0
      (denoteGraphDistributed pm initPM 5015) := c0
  have c1' : denoteGraphDistributed pm initPM 8548 = chunkPrimDimN 0 2 1
      (denoteGraphDistributed pm initPM 5015) := c1
  have qSM : denoteGraphDistributed sm initSM 5016 =
      (fw_rotary_embedding (denoteGraphDistributed sm initSM 4691) (denoteGraphDistributed sm initSM 5015)
        (denoteGraphDistributed sm initSM 5010) (denoteGraphDistributed sm initSM 5012) 16 4).1 := by
    rw [distributed_node_core sm initSM 242
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5015, 5010, 5012], outs := [5016, 5017], params := [16, 4] }
      5016 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring sm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read sm initSM 242 4691 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 242 5015 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 242 5010 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 242 5012 (by native_decide) (by native_decide)]
  have kSM : denoteGraphDistributed sm initSM 5017 =
      (fw_rotary_embedding (denoteGraphDistributed sm initSM 4691) (denoteGraphDistributed sm initSM 5015)
        (denoteGraphDistributed sm initSM 5010) (denoteGraphDistributed sm initSM 5012) 16 4).2 := by
    rw [distributed_node_core sm initSM 242
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5015, 5010, 5012], outs := [5016, 5017], params := [16, 4] }
      5017 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring sm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 4691 5015 5010 5012 5016 5017 (by decide),
      distributed_prefix_read sm initSM 242 4691 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 242 5015 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 242 5010 (by native_decide) (by native_decide),
      distributed_prefix_read sm initSM 242 5012 (by native_decide) (by native_decide)]
  have q0 : denoteGraphDistributed pm initPM 8549 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11859) (denoteGraphDistributed pm initPM 8547)
        (denoteGraphDistributed pm initPM 8515) (denoteGraphDistributed pm initPM 8527) 16 4).1 := by
    rw [distributed_node_core pm initPM 545
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11859, 8547, 8515, 8527], outs := [8549, 8551], params := [16, 4] }
      8549 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide), applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read pm initPM 545 11859 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 545 8547 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 545 8515 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 545 8527 (by native_decide) (by native_decide)]
  have k0 : denoteGraphDistributed pm initPM 8551 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11859) (denoteGraphDistributed pm initPM 8547)
        (denoteGraphDistributed pm initPM 8515) (denoteGraphDistributed pm initPM 8527) 16 4).2 := by
    rw [distributed_node_core pm initPM 545
      { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11859, 8547, 8515, 8527], outs := [8549, 8551], params := [16, 4] }
      8551 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11859 8547 8515 8527 8549 8551 (by decide),
      distributed_prefix_read pm initPM 545 11859 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 545 8547 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 545 8515 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 545 8527 (by native_decide) (by native_decide)]
  have q1 : denoteGraphDistributed pm initPM 8550 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11859) (denoteGraphDistributed pm initPM 8548)
        (denoteGraphDistributed pm initPM 8516) (denoteGraphDistributed pm initPM 8528) 16 4).1 := by
    rw [distributed_node_core pm initPM 546
      { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11859, 8548, 8516, 8528], outs := [8550, 8552], params := [16, 4] }
      8550 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide), applyNode_fw_rotary_embedding_fst_out,
      distributed_prefix_read pm initPM 546 11859 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 546 8548 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 546 8516 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 546 8528 (by native_decide) (by native_decide)]
  have k1 : denoteGraphDistributed pm initPM 8552 =
      (fw_rotary_embedding (denoteGraphDistributed pm initPM 11859) (denoteGraphDistributed pm initPM 8548)
        (denoteGraphDistributed pm initPM 8516) (denoteGraphDistributed pm initPM 8528) 16 4).2 := by
    rw [distributed_node_core pm initPM 546
      { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11859, 8548, 8516, 8528], outs := [8550, 8552], params := [16, 4] }
      8552 (by native_decide) (by native_decide) (by decide) (by native_decide) (by native_decide),
      applyNodeRingAttn_eq_applyNode_of_not_ring pm _ _ (by decide) (by decide),
      applyNode_fw_rotary_embedding_snd_out _ _ _ _ _ 11859 8548 8516 8528 8550 8552 (by decide),
      distributed_prefix_read pm initPM 546 11859 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 546 8548 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 546 8516 (by native_decide) (by native_decide),
      distributed_prefix_read pm initPM 546 8528 (by native_decide) (by native_decide)]
  have qval : denoteGraphDistributed sm initSM 5016 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 8549, denoteGraphDistributed pm initPM 8550] := by
    rw [qSM]; simp only [fw_rotary_embedding]
    rw [hq.value, fw_rotary_apply_allGather0_commute_2_1d (denoteGraphDistributed sm initSM 4691)
      (denoteGraphDistributed sm initSM 5015) (denoteGraphDistributed pm initPM 8515)
      (denoteGraphDistributed pm initPM 8516) 2048 16 64 (by omega) (by omega) (by omega)
      hspos hq.shard0_shape hq.shard1_shape, hcache, hpos, ← c0', ← c1', q0, q1]
    simp only [fw_rotary_embedding]
  have kval : denoteGraphDistributed sm initSM 5017 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 8551, denoteGraphDistributed pm initPM 8552] := by
    rw [kSM]; simp only [fw_rotary_embedding]
    rw [hk.value, fw_rotary_apply_allGather0_commute_2_1d (denoteGraphDistributed sm initSM 4691)
      (denoteGraphDistributed sm initSM 5015) (denoteGraphDistributed pm initPM 8527)
      (denoteGraphDistributed pm initPM 8528) 2048 4 64 (by omega) (by omega) (by omega)
      hspos hk.shard0_shape hk.shard1_shape, hcache, hpos, ← c0', ← c1', k0, k1]
    simp only [fw_rotary_embedding]
  have qs0 : (denoteGraphDistributed pm initPM 8549).shape = [2048, 16, 64] := by
    rw [q0]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hq.shard0_shape
  have qs1 : (denoteGraphDistributed pm initPM 8550).shape = [2048, 16, 64] := by
    rw [q1]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 hq.shard1_shape
  have ks0 : (denoteGraphDistributed pm initPM 8551).shape = [2048, 4, 64] := by
    rw [k0]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hk.shard0_shape
  have ks1 : (denoteGraphDistributed pm initPM 8552).shape = [2048, 4, 64] := by
    rw [k1]; simp only [fw_rotary_embedding]; exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 hk.shard1_shape
  refine ⟨⟨qval, ?_, qs0, qs1, by decide⟩, ⟨kval, ?_, ks0, ks1, by decide⟩⟩
  · rw [qval, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [qs0])]; rfl
  · rw [kval, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [ks0])]; rfl

/-- Public pure-distributed exact 2-TP reconstruction of the layer-6 rotary Q output. -/
theorem recon_intermediateGoal_5016_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5016
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5016 5016 8549 8550
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl
    (l6d_rotary5016_5017_rels initSM initPM hSM hPM hInit).1

/-- Public pure-distributed exact 2-TP reconstruction of the layer-6 rotary K output. -/
theorem recon_intermediateGoal_5017_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5017
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5017 5017 8551 8552
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl
    (l6d_rotary5016_5017_rels initSM initPM hSM hPM hInit).2

private def layer6SmSliding : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [5016, 5017, 5014, 5018, 5019], outs := [5020],
    params := [16, 4, 64, 64, 1, 512] }
private def layer6PmSliding0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_sliding_window",
    ins := [8549, 8551, 8537, 5018, 5019], outs := [8553],
    params := [16, 4, 64, 64, 1, 512] }
private def layer6PmSliding1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_sliding_window",
    ins := [8550, 8552, 8538, 5018, 5019], outs := [8554],
    params := [16, 4, 64, 64, 1, 512] }

set_option maxRecDepth 1000000 in
private theorem layer6_sm_sliding_node243 :
    sm.nodes[243]'(by native_decide) = layer6SmSliding := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer6_pm_sliding_node547 :
    pm.nodes[547]'(by native_decide) = layer6PmSliding0 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer6_pm_sliding_node548 :
    pm.nodes[548]'(by native_decide) = layer6PmSliding1 := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer6_sm_sliding_buddy :
    ringAttnBuddies sm layer6SmSliding = [layer6SmSliding] := by native_decide
set_option maxRecDepth 1000000 in
private theorem layer6_pm_sliding_buddy0 :
    ringAttnBuddies pm layer6PmSliding0 = [layer6PmSliding0, layer6PmSliding1] := by
  native_decide
set_option maxRecDepth 1000000 in
private theorem layer6_pm_sliding_buddy1 :
    ringAttnBuddies pm layer6PmSliding1 = [layer6PmSliding0, layer6PmSliding1] := by
  native_decide

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
/-- Faithful public pure-distributed exact 2-TP reconstruction of the layer-6
    sliding-window attention output. -/
theorem recon_intermediateGoal_5020_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5020
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have q := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5016 5016 8549 8550
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5016_distributed initSM initPM hSM hPM hInit)
  have k := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5017 5017 8551 8552
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5017_distributed initSM initPM hSM hPM hInit)
  have v := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5014 5014 8537 8538
    [4096, 4, 64] [2048, 4, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5014_distributed initSM initPM hSM hPM hInit)
  have hcu5018 := distributed_init_singleton_value initSM initPM hInit initGoal_5018
    (by native_decide) 5018 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hcu5019 := distributed_init_singleton_value initSM initPM hInit initGoal_5019
    (by native_decide) 5019 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  let fs := (sm.nodes.take 243).foldl (applyNodeDistributed sm) initSM
  let fp := (pm.nodes.take 547).foldl (applyNodeDistributed pm) initPM
  let fp' := (pm.nodes.take 548).foldl (applyNodeDistributed pm) initPM
  have bs (t : Tid) (hn : ∀ n ∈ sm.nodes.drop 243, n.outs ≠ [])
      (hw : ∀ n ∈ sm.nodes.drop 243, t ∉ n.outs) :
      fs t = denoteGraphDistributed sm initSM t :=
    distributed_prefix_read sm initSM 243 t hn hw
  have bp (t : Tid) (hn : ∀ n ∈ pm.nodes.drop 547, n.outs ≠ [])
      (hw : ∀ n ∈ pm.nodes.drop 547, t ∉ n.outs) :
      fp t = denoteGraphDistributed pm initPM t :=
    distributed_prefix_read pm initPM 547 t hn hw
  have hqfull : fs 5016 = allGatherPrimDimN 0 2 0 [fp 8549, fp 8550] := by
    rw [bs 5016 (by native_decide) (by native_decide),
      bp 8549 (by native_decide) (by native_decide),
      bp 8550 (by native_decide) (by native_decide)]
    exact q.value
  have hkfull : fs 5017 = allGatherPrimDimN 0 2 0 [fp 8551, fp 8552] := by
    rw [bs 5017 (by native_decide) (by native_decide),
      bp 8551 (by native_decide) (by native_decide),
      bp 8552 (by native_decide) (by native_decide)]
    exact k.value
  have hvfull : fs 5014 = allGatherPrimDimN 0 2 0 [fp 8537, fp 8538] := by
    rw [bs 5014 (by native_decide) (by native_decide),
      bp 8537 (by native_decide) (by native_decide),
      bp 8538 (by native_decide) (by native_decide)]
    exact v.value
  have hqpos : 0 < (fs (layer6SmSliding.ins.getD 0 0)).shape.length := by
    show 0 < (fs 5016).shape.length
    rw [bs 5016 (by native_decide) (by native_decide), q.full_shape]
    decide
  have hkpos : 0 < (fs (layer6SmSliding.ins.getD 1 0)).shape.length := by
    show 0 < (fs 5017).shape.length
    rw [bs 5017 (by native_decide) (by native_decide), k.full_shape]
    decide
  have hvpos : 0 < (fs (layer6SmSliding.ins.getD 2 0)).shape.length := by
    show 0 < (fs 5014).shape.length
    rw [bs 5014 (by native_decide) (by native_decide), v.full_shape]
    decide
  have hcuQ : fs 5018 = fp 5018 := by
    rw [bs 5018 (by native_decide) (by native_decide),
      bp 5018 (by native_decide) (by native_decide), hcu5018]
  have hcuK : fs 5019 = fp 5019 := by
    rw [bs 5019 (by native_decide) (by native_decide),
      bp 5019 (by native_decide) (by native_decide), hcu5019]
  have e8549 : fp 8549 = fp' 8549 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8549 547 548
      (by omega) (by native_decide) (by native_decide)).symm
  have e8550 : fp 8550 = fp' 8550 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8550 547 548
      (by omega) (by native_decide) (by native_decide)).symm
  have e8551 : fp 8551 = fp' 8551 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8551 547 548
      (by omega) (by native_decide) (by native_decide)).symm
  have e8552 : fp 8552 = fp' 8552 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8552 547 548
      (by omega) (by native_decide) (by native_decide)).symm
  have e8537 : fp 8537 = fp' 8537 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8537 547 548
      (by omega) (by native_decide) (by native_decide)).symm
  have e8538 : fp 8538 = fp' 8538 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 8538 547 548
      (by omega) (by native_decide) (by native_decide)).symm
  have e5018 : fp 5018 = fp' 5018 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 5018 547 548
      (by omega) (by native_decide) (by native_decide)).symm
  have e5019 : fp 5019 = fp' 5019 :=
    (foldl_take_split_at_not_written_distributed pm pm.nodes initPM 5019 547 548
      (by omega) (by native_decide) (by native_decide)).symm
  have bridge : applyNodeRingAttn_sliding_window pm fp layer6PmSliding1 =
      applyNodeRingAttn_sliding_window pm fp' layer6PmSliding1 := by
    apply attn_sw_store_congr
    · rw [layer6_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e8549
      · exact e8550
    · rw [layer6_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e8551
      · exact e8552
    · rw [layer6_pm_sliding_buddy1]; intro m hm; fin_cases hm
      · exact e8537
      · exact e8538
    · exact e5018
    · exact e5019
  have rSM : denoteGraphDistributed sm initSM 5020 =
      applyNodeRingAttn_sliding_window sm fs layer6SmSliding := by
    rw [distributed_node_core sm initSM 243 layer6SmSliding 5020 (by native_decide)
      layer6_sm_sliding_node243 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out sm _ 0 5016 5017 5014 5018 5019 5020
      [16, 4, 64, 64, 1, 512]
  have rP0 : denoteGraphDistributed pm initPM 8553 =
      applyNodeRingAttn_sliding_window pm fp layer6PmSliding0 := by
    rw [distributed_node_core pm initPM 547 layer6PmSliding0 8553 (by native_decide)
      layer6_pm_sliding_node547 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out pm _ 0 8549 8551 8537 5018 5019 8553
      [16, 4, 64, 64, 1, 512]
  have rP1 : denoteGraphDistributed pm initPM 8554 =
      applyNodeRingAttn_sliding_window pm fp' layer6PmSliding1 := by
    rw [distributed_node_core pm initPM 548 layer6PmSliding1 8554 (by native_decide)
      layer6_pm_sliding_node548 (by decide) (by native_decide) (by native_decide)]
    exact applyNodeRingAttn_sliding_window_out pm _ 1 8550 8552 8538 5018 5019 8554
      [16, 4, 64, 64, 1, 512]
  have hfull : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp 8549, fp 8550])
      (allGatherPrimDimN 0 2 0 [fp 8551, fp 8552])
      (allGatherPrimDimN 0 2 0 [fp 8537, fp 8538])
      (fp 5018) (fp 5019) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3, ← hqfull,
      bs 5016 (by native_decide) (by native_decide), q.full_shape]
    rfl
  have hfull' : (fw_attn_varlen
      (allGatherPrimDimN 0 2 0 [fp' 8549, fp' 8550])
      (allGatherPrimDimN 0 2 0 [fp' 8551, fp' 8552])
      (allGatherPrimDimN 0 2 0 [fp' 8537, fp' 8538])
      (fp' 5018) (fp' 5019) 16 4 64 64 true 512).shape = [2 * 2048, 16, 64] := by
    rw [← e8549, ← e8550, ← e8551, ← e8552, ← e8537, ← e8538,
      ← e5018, ← e5019]
    exact hfull
  exact recon_attn_sliding_window_2tp_distributed initSM initPM intermediateGoal_5020
    layer6SmSliding layer6PmSliding0 layer6PmSliding1 fs fp fp' 5020 8553 8554
    2048 16 64 (by omega) (by omega) (by omega) rSM rP0 rP1 bridge
    layer6_sm_sliding_buddy layer6_pm_sliding_buddy0 layer6_pm_sliding_buddy1
    (by native_decide) (by native_decide) hqpos hkpos hvpos hqfull hkfull hvfull
    hcuQ hcuK rfl rfl rfl rfl hfull hfull' rfl rfl rfl rfl rfl rfl

private theorem l6d_reshape (g : GraphDecl) (init : Store) (k r i o hd : Nat)
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

private theorem l6d_view (g : GraphDecl) (init : Store) (k r i o hd : Nat)
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

private theorem l6d_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
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

private theorem l6d_float (g : GraphDecl) (init : Store) (k r i o : Nat)
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

private theorem l6d_reshape5021_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5021)
      (denoteGraphDistributed pm initPM 8555) (denoteGraphDistributed pm initPM 8556)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5020 5020 8553 8554
    [4096, 16, 64] [2048, 16, 64] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5020_distributed initSM initPM hSM hPM hInit)
  have rs := l6d_reshape sm initSM 244 0 5020 5021 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l6d_reshape pm initPM 549 0 8553 8555 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l6d_reshape pm initPM 550 1 8554 8556 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  refine ⟨?_, by rw [rs]; rfl, by rw [r0]; rfl, by rw [r1]; rfl, by decide⟩
  rw [rs, h.value, fw_view_allGather0_reshape_16_64_2_g12 _ _ h.shard0_shape h.shard1_shape,
    r0, r1]

/-- Pure-distributed exact 2-TP reconstruction of the next-layer attention reshape. -/
theorem recon_intermediateGoal_5021_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5021
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5021 5021 8555 8556
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l6d_reshape5021_rel initSM initPM hSM hPM hInit)

private theorem l6d_reshape5022_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5022)
      (denoteGraphDistributed pm initPM 8561) (denoteGraphDistributed pm initPM 8562)
      [4096, 1024] [2048, 1024] := by
  have h := l6d_reshape5021_rel initSM initPM hSM hPM hInit
  have rs := l6d_reshape sm initSM 245 0 5021 5022 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l6d_reshape pm initPM 551 0 8555 8561 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l6d_reshape pm initPM 552 1 8556 8562 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5022 = denoteGraphDistributed sm initSM 5021 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 8561 = denoteGraphDistributed pm initPM 8555 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 8562 = denoteGraphDistributed pm initPM 8556 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of the identity reshape. -/
theorem recon_intermediateGoal_5022_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5022
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5022 5022 8561 8562
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l6d_reshape5022_rel initSM initPM hSM hPM hInit)

private theorem l6d_linear5024_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5024)
      (denoteGraphDistributed pm initPM 8565) (denoteGraphDistributed pm initPM 8566)
      [4096, 1024] [2048, 1024] := by
  have h := l6d_reshape5022_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5023
    (by native_decide) 5023 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5023
    (by native_decide) 5023 [1024, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5023).shape = [1024, 1024] := by
    rw [← hw]; exact hws
  have rs := l6d_linear sm initSM 246 0 5022 5023 5024 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l6d_linear pm initPM 553 0 8561 5023 8565 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l6d_linear pm initPM 554 1 8562 5023 8566 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 1024
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_linear_2d_shape 4096 1024 1024 _ _ h.full_shape hws
  · rw [r0]; exact fw_linear_2d_shape 2048 1024 1024 _ _ h.shard0_shape hpw
  · rw [r1]; exact fw_linear_2d_shape 2048 1024 1024 _ _ h.shard1_shape hpw

/-- Pure-distributed exact 2-TP reconstruction of the output projection. -/
theorem recon_intermediateGoal_5024_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5024
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5024 5024 8565 8566
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l6d_linear5024_rel initSM initPM hSM hPM hInit)

private theorem l6d_view5025_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5025)
      (denoteGraphDistributed pm initPM 8575) (denoteGraphDistributed pm initPM 8576)
      [4096, 1024] [2048, 1024] := by
  have h := l6d_linear5024_rel initSM initPM hSM hPM hInit
  have rs := l6d_view sm initSM 247 0 5024 5025 4096 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r0 := l6d_view pm initPM 555 0 8565 8575 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have r1 := l6d_view pm initPM 556 1 8566 8576 2048 [1024]
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have es : denoteGraphDistributed sm initSM 5025 = denoteGraphDistributed sm initSM 5024 := by
    rw [rs, fw_view_id_shape [4096, 1024] _ h.full_shape]
  have e0 : denoteGraphDistributed pm initPM 8575 = denoteGraphDistributed pm initPM 8565 := by
    rw [r0, fw_view_id_shape [2048, 1024] _ h.shard0_shape]
  have e1 : denoteGraphDistributed pm initPM 8576 = denoteGraphDistributed pm initPM 8566 := by
    rw [r1, fw_view_id_shape [2048, 1024] _ h.shard1_shape]
  exact ⟨by rw [es, h.value, ← e0, ← e1], by rw [es]; exact h.full_shape,
    by rw [e0]; exact h.shard0_shape, by rw [e1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of the identity view. -/
theorem recon_intermediateGoal_5025_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5025
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5025 5025 8575 8576
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l6d_view5025_rel initSM initPM hSM hPM hInit)

private theorem l6d_float5026_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5026)
      (denoteGraphDistributed pm initPM 8579) (denoteGraphDistributed pm initPM 8580)
      [4096, 1024] [2048, 1024] := by
  have h := l6d_view5025_rel initSM initPM hSM hPM hInit
  have rs := l6d_float sm initSM 248 0 5025 5026 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l6d_float pm initPM 557 0 8575 8579 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l6d_float pm initPM 558 1 8576 8580 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  exact ⟨by rw [rs, h.value, r0, r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of the post-projection float. -/
theorem recon_intermediateGoal_5026_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5026
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5026 5026 8579 8580
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l6d_float5026_rel initSM initPM hSM hPM hInit)

private theorem l6d_carry7699_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 7699)
      (denoteGraphDistributed pm initPM 15121) (denoteGraphDistributed pm initPM 15129)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5006 5006 8509 8510
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5006_distributed initSM initPM hSM hPM hInit)
  have rs := distributed_reduce1 sm initSM 236
    { rank := 0, op := "OpName.FW_multiref", ins := [5006], outs := [7695, 7699], params := [2] }
    5006 7699 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' sm st 0 5006 7695 7699 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce1 pm initPM 533
    { rank := 0, op := "OpName.FW_multiref", ins := [8509], outs := [15117, 15121], params := [2] }
    8509 15121 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 0 8509 15117 15121 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce1 pm initPM 534
    { rank := 1, op := "OpName.FW_multiref", ins := [8510], outs := [15125, 15129], params := [2] }
    8510 15129 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_second_out' pm st 1 8510 15125 15129 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at rs r0 r1
  exact ⟨by rw [rs, h.value, ← r0, ← r1], by rw [rs]; exact h.full_shape,
    by rw [r0]; exact h.shard0_shape, by rw [r1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of the cross-block residual carry. -/
theorem recon_intermediateGoal_7699_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_7699
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_7699 7699 15121 15129
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l6d_carry7699_rel initSM initPM hSM hPM hInit)

/-- Pure-distributed residual add `7699 + 5026` completing the next-layer cascade. -/
theorem recon_intermediateGoal_5027_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5027
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  have ha := l6d_carry7699_rel initSM initPM hSM hPM hInit
  have hb := l6d_float5026_rel initSM initPM hSM hPM hInit
  have rs := distributed_reduce2 sm initSM 249
    { rank := 0, op := "OpName.FW_add", ins := [7699, 5026], outs := [5027] }
    7699 5026 5027 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_add2_out sm st 0 7699 5026 5027)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := distributed_reduce2 pm initPM 559
    { rank := 0, op := "OpName.FW_add", ins := [15121, 8579], outs := [8583] }
    15121 8579 8583 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_add2_out pm st 0 15121 8579 8583)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := distributed_reduce2 pm initPM 560
    { rank := 1, op := "OpName.FW_add", ins := [15129, 8580], outs := [8584] }
    15129 8580 8584 elemwiseAdd (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_add2_out pm st 1 15129 8580 8584)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hv : denoteGraphDistributed sm initSM 5027 = allGatherPrimDimN 0 pm.numRanks 0
      [denoteGraphDistributed pm initPM 8583, denoteGraphDistributed pm initPM 8584] := by
    rw [rs, ha.value, hb.value, show pm.numRanks = 2 from rfl,
      fw_add_allGather0_commute_2_2048_1024 _ _ _ _ ha.shard0_shape ha.shard1_shape
        hb.shard0_shape hb.shard1_shape, ← r0, ← r1]
  have hs0 : (denoteGraphDistributed pm initPM 8583).shape = [2048, 1024] := by
    rw [r0]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.shard0_shape hb.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 8584).shape = [2048, 1024] := by
    rw [r1]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.shard1_shape hb.shard1_shape
  have hs : (denoteGraphDistributed sm initSM 5027).shape = [4096, 1024] := by
    rw [rs]; exact elemwiseAdd_shape_of_shapes _ _ _ ha.full_shape hb.full_shape
  exact wrap_2tp_allGather_gen _ _ intermediateGoal_5027 5027 8583 8584
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide) hv hs hs0 hs1

/-! ## Pure-distributed layer-7 router entrance -/

private theorem l6d_norm_linear (g : GraphDecl) (init : Store) (k r x w o : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk =
      { rank := r, op := "OpName.FW_norm_linear", ins := [x, w], outs := [o] })
    (hdn : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdw : ∀ n ∈ g.nodes.drop (k + 1), o ∉ n.outs)
    (hpn : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpx : ∀ n ∈ g.nodes.drop k, x ∉ n.outs)
    (hpw : ∀ n ∈ g.nodes.drop k, w ∉ n.outs) :
    denoteGraphDistributed g init o =
      fw_norm_linear (denoteGraphDistributed g init x) (denoteGraphDistributed g init w) :=
  distributed_reduce2 g init k _ x w o fw_norm_linear hk hn (by simp)
    (fun st => applyNode_fw_norm_linear_out g st r x w o) hdn hdw hpn hpx hpw

private theorem l6d_rms5029_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5029)
      (denoteGraphDistributed pm initPM 8587) (denoteGraphDistributed pm initPM 8588)
      [4096, 1024] [2048, 1024] := by
  have h := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5027 5027 8583 8584
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5027_distributed initSM initPM hSM hPM hInit)
  have ms := distributed_reduce1 sm initSM 250
    { rank := 0, op := "OpName.FW_multiref", ins := [5027], outs := [7716, 7720], params := [2] }
    5027 7716 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out sm st 0 5027 7716 7720)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := distributed_reduce1 pm initPM 561
    { rank := 0, op := "OpName.FW_multiref", ins := [8583], outs := [15159, 15163], params := [2] }
    8583 15159 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 0 8583 15159 15163)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := distributed_reduce1 pm initPM 562
    { rank := 1, op := "OpName.FW_multiref", ins := [8584], outs := [15167, 15171], params := [2] }
    8584 15167 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref2_first_out pm st 1 8584 15167 15171)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5028
    (by native_decide) 5028 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have rs := l6d_rms sm initSM 251 0 7716 5028 5029 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l6d_rms pm initPM 563 0 15159 5028 8587 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l6d_rms pm initPM 564 1 15167 5028 8588 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 15159).shape = [2048, 1024] := by rw [m0]; exact h.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 15167).shape = [2048, 1024] := by rw [m1]; exact h.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, ms, h.value, ← m0, ← m1, hw,
      fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega) hs0 hs1, r0, r1]
  · rw [rs]; exact fw_rms_norm_shape2 _ _ 4096 1024 (by rw [ms]; exact h.full_shape)
  · rw [r0]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs0
  · rw [r1]; exact fw_rms_norm_shape2 _ _ 2048 1024 hs1

/-- Pure-distributed exact 2-TP reconstruction of the router RMSNorm. -/
theorem recon_intermediateGoal_5029_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5029
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5029 5029 8587 8588
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l6d_rms5029_rel initSM initPM hSM hPM hInit)

private theorem l6d_float5030_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5030)
      (denoteGraphDistributed pm initPM 8589) (denoteGraphDistributed pm initPM 8590)
      [4096, 1024] [2048, 1024] := by
  have h := l6d_rms5029_rel initSM initPM hSM hPM hInit
  have ms := distributed_reduce1 sm initSM 252
    { rank := 0, op := "OpName.FW_multiref", ins := [5029],
      outs := [7727, 7731, 7735, 7739, 7743], params := [5] }
    5029 7727 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref_first_out' sm st 0 4 5029 7727 [7731, 7735, 7739, 7743])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := distributed_reduce1 pm initPM 565
    { rank := 0, op := "OpName.FW_multiref", ins := [8587],
      outs := [15178, 15182, 15186, 15190, 15194], params := [5] }
    8587 15178 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref_first_out' pm st 0 4 8587 15178 [15182, 15186, 15190, 15194])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := distributed_reduce1 pm initPM 566
    { rank := 1, op := "OpName.FW_multiref", ins := [8588],
      outs := [15201, 15205, 15209, 15213, 15217], params := [5] }
    8588 15201 id (by native_decide) (by native_decide) (by decide)
    (fun st => applyNode_fw_multiref_first_out' pm st 1 4 8588 15201 [15205, 15209, 15213, 15217])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rs := l6d_float sm initSM 253 0 7727 5030 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l6d_float pm initPM 567 0 15178 8589 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l6d_float pm initPM 571 1 15201 8590 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  exact ⟨by rw [rs, ms, h.value, ← m0, ← m1, r0, r1],
    by rw [rs, ms]; exact h.full_shape, by rw [r0, m0]; exact h.shard0_shape,
    by rw [r1, m1]; exact h.shard1_shape, by decide⟩

/-- Pure-distributed exact 2-TP reconstruction of the first router `mref5` float. -/
theorem recon_intermediateGoal_5030_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5030
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5030 5030 8589 8590
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl
    (l6d_float5030_rel initSM initPM hSM hPM hInit)

private theorem l6d_logits5032_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5032)
      (denoteGraphDistributed pm initPM 8595) (denoteGraphDistributed pm initPM 8596)
      [4096, 64] [2048, 64] := by
  have h := l6d_float5030_rel initSM initPM hSM hPM hInit
  have hw := distributed_init_singleton_value initSM initPM hInit initGoal_5031
    (by native_decide) 5031 rfl rfl rfl rfl layer1_sm_nodes_nonempty
    (by native_decide) layer1_pm_nodes_nonempty (by native_decide)
  have hws := distributed_init_singleton_shape initSM initPM hInit initGoal_5031
    (by native_decide) 5031 [64, 1024] rfl rfl layer1_sm_nodes_nonempty (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5031).shape = [64, 1024] := by rw [← hw]; exact hws
  have rs := l6d_norm_linear sm initSM 257 0 5030 5031 5032 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l6d_norm_linear pm initPM 575 0 8589 5031 8595 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l6d_norm_linear pm initPM 579 1 8590 5031 8596 (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value, hw, fw_norm_linear_allGather0_commute_2 _ _ _ 2048 1024 64
      (by omega) (by omega) (by omega) h.shard0_shape h.shard1_shape hpw, r0, r1]
  · rw [rs]; exact fw_norm_linear_2d_shape 4096 1024 64 _ _ (by decide) h.full_shape hws
  · rw [r0]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) h.shard0_shape hpw
  · rw [r1]; exact fw_norm_linear_2d_shape 2048 1024 64 _ _ (by decide) h.shard1_shape hpw

/-- Pure-distributed exact 2-TP reconstruction of the router logits. -/
theorem recon_intermediateGoal_5032_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5032
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5032 5032 8595 8596
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl
    (l6d_logits5032_rel initSM initPM hSM hPM hInit)

private theorem l6d_distributed_reduce1_at (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (inTid outTid : Tid) (opfun : Tensor → Tensor)
    (hk : k < g.nodes.length) (hnode : g.nodes[k]'hk = node)
    (hmoe : node.op ≠ "OpName.FW_all2all_moe_gmm")
    (happly : applyNodeRingAttn g ((g.nodes.take k).foldl (applyNodeDistributed g) init) node outTid =
      opfun (((g.nodes.take k).foldl (applyNodeDistributed g) init) inTid))
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre : ∀ n ∈ g.nodes.drop k, inTid ∉ n.outs) :
    denoteGraphDistributed g init outTid = opfun (denoteGraphDistributed g init inTid) := by
  rw [distributed_node_core g init k node outTid hk hnode hmoe hdrop_nil hdrop,
    happly, distributed_prefix_read g init k inTid hpre_nil hpre]

private theorem l6d_topk_common (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5032)
      (denoteGraphDistributed pm initPM 8595) (denoteGraphDistributed pm initPM 8596)
      [4096, 64] [2048, 64]
    ∧ ((sm.nodes.take 261).foldl (applyNodeDistributed sm) initSM 5032).shape.reverse.head? = some 64
    ∧ ((pm.nodes.take 583).foldl (applyNodeDistributed pm) initPM 8595).shape.reverse.head? = some 64
    ∧ ((pm.nodes.take 587).foldl (applyNodeDistributed pm) initPM 8596).shape.reverse.head? = some 64 := by
  have h := l6d_logits5032_rel initSM initPM hSM hPM hInit
  refine ⟨h, ?_, ?_, ?_⟩
  · rw [distributed_prefix_read sm initSM 261 5032 (by native_decide) (by native_decide), h.full_shape]; rfl
  · rw [distributed_prefix_read pm initPM 583 8595 (by native_decide) (by native_decide), h.shard0_shape]; rfl
  · rw [distributed_prefix_read pm initPM 587 8596 (by native_decide) (by native_decide), h.shard1_shape]; rfl

private theorem l6d_topk5033_rel (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    Gather2Rel (denoteGraphDistributed sm initSM 5033)
      (denoteGraphDistributed pm initPM 8597) (denoteGraphDistributed pm initPM 8598)
      [4096, 64] [2048, 64] := by
  obtain ⟨h, ls, l0, l1⟩ := l6d_topk_common initSM initPM hSM hPM hInit
  have rs := l6d_distributed_reduce1_at sm initSM 261
    { rank := 0, op := "OpName.FW_topk_routing", ins := [5032], outs := [5033, 5034, 5035], params := [8, 1] }
    5032 5033 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_fst sm ((sm.nodes.take 261).foldl (applyNodeDistributed sm) initSM) 0 5032 5033 5034 5035 ls)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l6d_distributed_reduce1_at pm initPM 583
    { rank := 0, op := "OpName.FW_topk_routing", ins := [8595], outs := [8597, 8599, 8601], params := [8, 1] }
    8595 8597 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_fst pm ((pm.nodes.take 583).foldl (applyNodeDistributed pm) initPM) 0 8595 8597 8599 8601 l0)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l6d_distributed_reduce1_at pm initPM 587
    { rank := 1, op := "OpName.FW_topk_routing", ins := [8596], outs := [8598, 8600, 8602], params := [8, 1] }
    8596 8598 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_fst pm ((pm.nodes.take 587).foldl (applyNodeDistributed pm) initPM) 1 8596 8598 8600 8602 l1)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [rs, h.value,
      fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega)
        h.shard0_shape h.shard1_shape, r0, r1]
  · rw [rs]; exact fw_topk_routing_fst_shape _ 8 64 4096 (by rw [h.full_shape]; rfl)
  · rw [r0]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h.shard0_shape]; rfl)
  · rw [r1]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h.shard1_shape]; rfl)

/-- Pure-distributed exact 2-TP reconstruction of router routing probabilities. -/
theorem recon_intermediateGoal_5033_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5033
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) :=
  Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5033 5033 8597 8598
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl
    (l6d_topk5033_rel initSM initPM hSM hPM hInit)

/-- Pure-distributed exact 2-TP reconstruction of the router routing map. -/
theorem recon_intermediateGoal_5034_distributed (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5034
      (denoteGraphDistributed sm initSM) (denoteGraphDistributed pm initPM) := by
  obtain ⟨h, ls, l0, l1⟩ := l6d_topk_common initSM initPM hSM hPM hInit
  have rs := l6d_distributed_reduce1_at sm initSM 261
    { rank := 0, op := "OpName.FW_topk_routing", ins := [5032], outs := [5033, 5034, 5035], params := [8, 1] }
    5032 5034 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_snd sm ((sm.nodes.take 261).foldl (applyNodeDistributed sm) initSM) 0 5032 5033 5034 5035 (by decide) ls)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r0 := l6d_distributed_reduce1_at pm initPM 583
    { rank := 0, op := "OpName.FW_topk_routing", ins := [8595], outs := [8597, 8599, 8601], params := [8, 1] }
    8595 8599 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_snd pm ((pm.nodes.take 583).foldl (applyNodeDistributed pm) initPM) 0 8595 8597 8599 8601 (by decide) l0)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have r1 := l6d_distributed_reduce1_at pm initPM 587
    { rank := 1, op := "OpName.FW_topk_routing", ins := [8596], outs := [8598, 8600, 8602], params := [8, 1] }
    8596 8600 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide) (by decide)
    (applyNode_topk81_snd pm ((pm.nodes.take 587).foldl (applyNodeDistributed pm) initPM) 1 8596 8598 8600 8602 (by decide) l1)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rel : Gather2Rel (denoteGraphDistributed sm initSM 5034)
      (denoteGraphDistributed pm initPM 8599) (denoteGraphDistributed pm initPM 8600)
      [4096, 64] [2048, 64] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rs, h.value,
        fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega)
          h.shard0_shape h.shard1_shape, r0, r1]
    · rw [rs]; exact fw_topk_routing_snd_shape _ 8 64 4096 (by rw [h.full_shape]; rfl)
    · rw [r0]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [h.shard0_shape]; rfl)
    · rw [r1]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [h.shard1_shape]; rfl)
  exact Gather2Rel.to_initGoalHolds _ _ intermediateGoal_5034 5034 8599 8600
    [4096, 64] [2048, 64] rfl rfl rfl rfl rfl rfl rel

#print axioms recon_intermediateGoal_7679_distributed
#print axioms recon_intermediateGoal_4984_distributed
#print axioms recon_intermediateGoal_5006_distributed
#print axioms recon_intermediateGoal_5008_distributed
#print axioms recon_intermediateGoal_5010_distributed
#print axioms recon_intermediateGoal_5012_distributed
#print axioms recon_intermediateGoal_5014_distributed
#print axioms recon_intermediateGoal_5016_distributed
#print axioms recon_intermediateGoal_5017_distributed
#print axioms recon_intermediateGoal_5020_distributed
#print axioms recon_intermediateGoal_5021_distributed
#print axioms recon_intermediateGoal_5024_distributed
#print axioms recon_intermediateGoal_7699_distributed
#print axioms recon_intermediateGoal_5027_distributed
#print axioms recon_intermediateGoal_5029_distributed
#print axioms recon_intermediateGoal_5030_distributed
#print axioms recon_intermediateGoal_5032_distributed
#print axioms recon_intermediateGoal_5033_distributed
#print axioms recon_intermediateGoal_5034_distributed

end TrainVerify.Denote.GeneratedPatterns
