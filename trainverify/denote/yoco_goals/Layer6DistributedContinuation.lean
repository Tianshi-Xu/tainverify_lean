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

#print axioms recon_intermediateGoal_7679_distributed
#print axioms recon_intermediateGoal_4984_distributed
#print axioms recon_intermediateGoal_5006_distributed

end TrainVerify.Denote.GeneratedPatterns
