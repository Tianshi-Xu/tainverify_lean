import denote.yoco_goals.L10FaithfulReductionKit

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- L2 ordinary V relation, derived from the preceding MoE boundary and init weight. -/
theorem l2o_v5053_rel_from_boundary (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (h : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5045)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8082) (denoteGraphDistributedFaithful pm_goal_1 initPM 8083)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5053)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8110) (denoteGraphDistributedFaithful pm_goal_1 initPM 8111)
      [4096, 4, 64] [2048, 4, 64] := by
  have ms := l10f_reduce1 sm_goal_1 initSM 80
    { rank := 0, op := "OpName.FW_multiref", ins := [5045], outs := [7848, 7852], params := [2] }
    5045 7848 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 5045 [7848, 7852] 2 rfl 7848 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l10f_reduce1 pm_goal_1 initPM 200
    { rank := 0, op := "OpName.FW_multiref", ins := [8082], outs := [15502, 15506], params := [2] }
    8082 15502 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 8082 [15502, 15506] 2 rfl 15502 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l10f_reduce1 pm_goal_1 initPM 201
    { rank := 1, op := "OpName.FW_multiref", ins := [8083], outs := [15510, 15514], params := [2] }
    8083 15510 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 8083 [15510, 15514] 2 rfl 15510 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hw1 := l10f_init_value initSM initPM hInit initGoal_5046
    (by native_decide) 5046 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rs := l10f_rms sm_goal_1 initSM 81 0 7848 5046 5047
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10f_rms pm_goal_1 initPM 202 0 15502 5046 8086
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10f_rms pm_goal_1 initPM 203 1 15510 5046 8087
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have rmsRel : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5047)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8086) (denoteGraphDistributedFaithful pm_goal_1 initPM 8087)
      [4096, 1024] [2048, 1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rs, ms, h.value, ← m0, ← m1, hw1,
        ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega)
          (by rw [m0]; exact h.shard0_shape) (by rw [m1]; exact h.shard1_shape), r0, r1]
    · rw [rs]; exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024 (by rw [ms]; exact h.full_shape)
    · rw [r0]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m0]; exact h.shard0_shape)
    · rw [r1]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m1]; exact h.shard1_shape)
  have vs := l10f_reduce1 sm_goal_1 initSM 82
    { rank := 0, op := "OpName.FW_multiref", ins := [5047], outs := [7857, 7861, 7865], params := [3] }
    5047 7865 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 5047 [7857, 7861, 7865] 3 rfl 7865 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have v0 := l10f_reduce1 pm_goal_1 initPM 204
    { rank := 0, op := "OpName.FW_multiref", ins := [8086], outs := [15308, 12610, 12618], params := [3] }
    8086 12618 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 8086 [15308, 12610, 12618] 3 rfl 12618 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have v1 := l10f_reduce1 pm_goal_1 initPM 205
    { rank := 1, op := "OpName.FW_multiref", ins := [8087], outs := [15310, 12611, 12619], params := [3] }
    8087 12619 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 8087 [15310, 12611, 12619] 3 rfl 12619 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at vs v0 v1
  have hw := l10f_init_value initSM initPM hInit initGoal_5052
    (by native_decide) 5052 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hws := l10f_init_shape initSM initPM hInit initGoal_5052
    (by native_decide) 5052 [4, 64, 1024] rfl rfl (by native_decide)
  have hpw : (denoteGraphDistributedFaithful pm_goal_1 initPM 5052).shape = [4, 64, 1024] := by
    rw [← hw]; exact hws
  have ps := l10f_per_head sm_goal_1 initSM 85 0 7865 5052 5053
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have p0 := l10f_per_head pm_goal_1 initPM 207 0 12618 5052 8110
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have p1 := l10f_per_head pm_goal_1 initPM 210 1 12619 5052 8111
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 12618).shape = [2048, 1024] := by
    rw [v0]; exact rmsRel.shard0_shape
  have hs1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 12619).shape = [2048, 1024] := by
    rw [v1]; exact rmsRel.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [ps, vs, rmsRel.value, ← v0, ← v1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, p0, p1]
  · rw [ps]; exact l11o_per_head_shape _ _ 4096 1024 4 64
      (by rw [vs]; exact rmsRel.full_shape) hws
  · rw [p0]; exact l11o_per_head_shape _ _ 2048 1024 4 64 hs0 hpw
  · rw [p1]; exact l11o_per_head_shape _ _ 2048 1024 4 64 hs1 hpw

/-- L2 ordinary rotary Q/K relations, derived from the preceding MoE boundary. -/
theorem l2o_q5055_k5056_rels_from_boundary (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (h : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5045)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8082) (denoteGraphDistributedFaithful pm_goal_1 initPM 8083)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5055)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8122) (denoteGraphDistributedFaithful pm_goal_1 initPM 8123)
      [4096, 16, 64] [2048, 16, 64] ∧
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5056)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8124) (denoteGraphDistributedFaithful pm_goal_1 initPM 8125)
      [4096, 4, 64] [2048, 4, 64] := by
  have ms := l10f_reduce1 sm_goal_1 initSM 80
    { rank := 0, op := "OpName.FW_multiref", ins := [5045], outs := [7848, 7852], params := [2] }
    5045 7848 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 5045 [7848, 7852] 2 rfl 7848 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l10f_reduce1 pm_goal_1 initPM 200
    { rank := 0, op := "OpName.FW_multiref", ins := [8082], outs := [15502, 15506], params := [2] }
    8082 15502 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 8082 [15502, 15506] 2 rfl 15502 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l10f_reduce1 pm_goal_1 initPM 201
    { rank := 1, op := "OpName.FW_multiref", ins := [8083], outs := [15510, 15514], params := [2] }
    8083 15510 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 8083 [15510, 15514] 2 rfl 15510 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hw1 := l10f_init_value initSM initPM hInit initGoal_5046
    (by native_decide) 5046 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rs := l10f_rms sm_goal_1 initSM 81 0 7848 5046 5047
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10f_rms pm_goal_1 initPM 202 0 15502 5046 8086
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10f_rms pm_goal_1 initPM 203 1 15510 5046 8087
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have rmsRel : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5047)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8086) (denoteGraphDistributedFaithful pm_goal_1 initPM 8087)
      [4096, 1024] [2048, 1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rs, ms, h.value, ← m0, ← m1, hw1,
        ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega)
          (by rw [m0]; exact h.shard0_shape) (by rw [m1]; exact h.shard1_shape), r0, r1]
    · rw [rs]; exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024 (by rw [ms]; exact h.full_shape)
    · rw [r0]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m0]; exact h.shard0_shape)
    · rw [r1]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m1]; exact h.shard1_shape)

  have qmS := l10f_reduce1 sm_goal_1 initSM 82
    { rank := 0, op := "OpName.FW_multiref", ins := [5047], outs := [7857, 7861, 7865], params := [3] }
    5047 7857 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 5047 [7857, 7861, 7865] 3 rfl 7857 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have qm0 := l10f_reduce1 pm_goal_1 initPM 204
    { rank := 0, op := "OpName.FW_multiref", ins := [8086], outs := [15308, 12610, 12618], params := [3] }
    8086 15308 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 8086 [15308, 12610, 12618] 3 rfl 15308 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have qm1 := l10f_reduce1 pm_goal_1 initPM 205
    { rank := 1, op := "OpName.FW_multiref", ins := [8087], outs := [15310, 12611, 12619], params := [3] }
    8087 15310 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 8087 [15310, 12611, 12619] 3 rfl 15310 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at qmS qm0 qm1
  have qg := l10f_allgather2 pm_goal_1 initPM 208 0 15308 15310 11790
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hwq := l10f_init_value initSM initPM hInit initGoal_5048
    (by native_decide) 5048 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hswq := l10f_init_shape initSM initPM hInit initGoal_5048
    (by native_decide) 5048 [16, 64, 1024] rfl rfl (by native_decide)
  have hpwq : (denoteGraphDistributedFaithful pm_goal_1 initPM 5048).shape = [16, 64, 1024] := by
    rw [← hwq]; exact hswq
  have qs := l10f_per_head sm_goal_1 initSM 83 0 7857 5048 5049
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  -- The shared Q output is written twice in PM; reduce at the final writer (rank 1).
  have qp := l10f_per_head pm_goal_1 initPM 212 1 11790 5048 5049
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hpmR : pm_goal_1.numRanks = 2 := rfl
  rw [hpmR] at qg
  have qeq : denoteGraphDistributedFaithful sm_goal_1 initSM 5049 = denoteGraphDistributedFaithful pm_goal_1 initPM 5049 := by
    rw [qs, qmS, rmsRel.value, ← qm0, ← qm1, ← qg, hwq, ← qp]
  have hqfullS : (denoteGraphDistributedFaithful sm_goal_1 initSM 5049).shape = [4096, 16, 64] := by
    rw [qs]
    exact l11o_per_head_shape _ _ 4096 1024 16 64
      (by rw [qmS]; exact rmsRel.full_shape) hswq
  have hqfullP : (denoteGraphDistributedFaithful pm_goal_1 initPM 5049).shape = [4096, 16, 64] := by
    rw [← qeq]; exact hqfullS
  have cq0 := l10f_chunk pm_goal_1 initPM 213 0 5049 8088
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have cq1 := l10f_chunk pm_goal_1 initPM 214 1 5049 8089
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hpmR] at cq0 cq1
  have hq0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8088).shape = [2048, 16, 64] := by
    rw [cq0, chunkPrimDimN_shape 0 2 0 _ [4096, 16, 64] hqfullP (by omega)]
    rfl
  have hq1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8089).shape = [2048, 16, 64] := by
    rw [cq1, chunkPrimDimN_shape 0 2 1 _ [4096, 16, 64] hqfullP (by omega)]
    rfl
  have qRel : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5049)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8088) (denoteGraphDistributedFaithful pm_goal_1 initPM 8089)
      [4096, 16, 64] [2048, 16, 64] := by
    refine ⟨?_, hqfullS, hq0, hq1, by decide⟩
    rw [qeq, cq0, cq1]
    exact (l11o_allGather0_reconstruct_chunks_3d 2048 16 64 (by omega) (by omega) (by omega)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5049) (by simpa using hqfullP)).symm

  have kmS := l10f_reduce1 sm_goal_1 initSM 82
    { rank := 0, op := "OpName.FW_multiref", ins := [5047], outs := [7857, 7861, 7865], params := [3] }
    5047 7861 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 5047 [7857, 7861, 7865] 3 rfl 7861 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have km0 := l10f_reduce1 pm_goal_1 initPM 204
    { rank := 0, op := "OpName.FW_multiref", ins := [8086], outs := [15308, 12610, 12618], params := [3] }
    8086 12610 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 8086 [15308, 12610, 12618] 3 rfl 12610 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have km1 := l10f_reduce1 pm_goal_1 initPM 205
    { rank := 1, op := "OpName.FW_multiref", ins := [8087], outs := [15310, 12611, 12619], params := [3] }
    8087 12611 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 8087 [15310, 12611, 12619] 3 rfl 12611 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at kmS km0 km1
  have hwk := l10f_init_value initSM initPM hInit initGoal_5050
    (by native_decide) 5050 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hswk := l10f_init_shape initSM initPM hInit initGoal_5050
    (by native_decide) 5050 [4, 64, 1024] rfl rfl (by native_decide)
  have hpwk : (denoteGraphDistributedFaithful pm_goal_1 initPM 5050).shape = [4, 64, 1024] := by
    rw [← hwk]; exact hswk
  have ks := l10f_per_head sm_goal_1 initSM 84 0 7861 5050 5051
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have kp0 := l10f_per_head pm_goal_1 initPM 206 0 12610 5050 8100
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have kp1 := l10f_per_head pm_goal_1 initPM 209 1 12611 5050 8101
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have kRel : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5051)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8100) (denoteGraphDistributedFaithful pm_goal_1 initPM 8101)
      [4096, 4, 64] [2048, 4, 64] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [ks, kmS, rmsRel.value, ← km0, ← km1, hwk,
        fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
          (by omega) (by omega) (by omega) (by omega)
          (by rw [km0]; exact rmsRel.shard0_shape)
          (by rw [km1]; exact rmsRel.shard1_shape) hpwk, kp0, kp1]
    · rw [ks]; exact l11o_per_head_shape _ _ 4096 1024 4 64
        (by rw [kmS]; exact rmsRel.full_shape) hswk
    · rw [kp0]; exact l11o_per_head_shape _ _ 2048 1024 4 64
        (by rw [km0]; exact rmsRel.shard0_shape) hpwk
    · rw [kp1]; exact l11o_per_head_shape _ _ 2048 1024 4 64
        (by rw [km1]; exact rmsRel.shard1_shape) hpwk

  have hcache := l10f_init_value initSM initPM hInit initGoal_4944
    (by native_decide) 4944 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpos := l10f_init_value initSM initPM hInit initGoal_5054
    (by native_decide) 5054 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hspos := l10f_init_shape initSM initPM hInit initGoal_5054
    (by native_decide) 5054 [4096] rfl rfl (by native_decide)
  have pc0 := l10f_chunk pm_goal_1 initPM 3 0 5054 8120
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have pc1 := l10f_chunk pm_goal_1 initPM 17 1 5054 8121
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hpmR] at pc0 pc1
  have qS := l10f_reduce4 sm_goal_1 initSM 86
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 5054, 5049, 5051],
      outs := [5055, 5056], params := [16, 4] }
    4944 5054 5049 5051 5055
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).1)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_fst_out sm_goal_1 st 0 16 4 4944 5054 5049 5051 5055 5056)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have kS := l10f_reduce4 sm_goal_1 initSM 86
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 5054, 5049, 5051],
      outs := [5055, 5056], params := [16, 4] }
    4944 5054 5049 5051 5056
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).2)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_snd_out sm_goal_1 st 0 16 4 4944 5054 5049 5051 5055 5056 (by decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have q0 := l10f_reduce4 pm_goal_1 initPM 215
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 8120, 8088, 8100],
      outs := [8122, 8124], params := [16, 4] }
    4944 8120 8088 8100 8122
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).1)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_fst_out pm_goal_1 st 0 16 4 4944 8120 8088 8100 8122 8124)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have k0 := l10f_reduce4 pm_goal_1 initPM 215
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 8120, 8088, 8100],
      outs := [8122, 8124], params := [16, 4] }
    4944 8120 8088 8100 8124
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).2)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_snd_out pm_goal_1 st 0 16 4 4944 8120 8088 8100 8122 8124 (by decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have q1 := l10f_reduce4 pm_goal_1 initPM 216
    { rank := 1, op := "OpName.FW_rotary_embedding", ins := [4944, 8121, 8089, 8101],
      outs := [8123, 8125], params := [16, 4] }
    4944 8121 8089 8101 8123
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).1)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_fst_out pm_goal_1 st 1 16 4 4944 8121 8089 8101 8123 8125)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have k1 := l10f_reduce4 pm_goal_1 initPM 216
    { rank := 1, op := "OpName.FW_rotary_embedding", ins := [4944, 8121, 8089, 8101],
      outs := [8123, 8125], params := [16, 4] }
    4944 8121 8089 8101 8125
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).2)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_snd_out pm_goal_1 st 1 16 4 4944 8121 8089 8101 8123 8125 (by decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have qval : denoteGraphDistributedFaithful sm_goal_1 initSM 5055 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributedFaithful pm_goal_1 initPM 8122, denoteGraphDistributedFaithful pm_goal_1 initPM 8123] := by
    rw [qS]
    simp only [fw_rotary_embedding]
    rw [qRel.value, l11o_rotary_allGather0_1d (denoteGraphDistributedFaithful sm_goal_1 initSM 4944)
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5054) (denoteGraphDistributedFaithful pm_goal_1 initPM 8088)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8089) 2048 16 64 (by omega) (by omega) (by omega)
      hspos qRel.shard0_shape qRel.shard1_shape, hcache, hpos, ← pc0, ← pc1, q0, q1]
    simp only [fw_rotary_embedding]
  have kval : denoteGraphDistributedFaithful sm_goal_1 initSM 5056 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributedFaithful pm_goal_1 initPM 8124, denoteGraphDistributedFaithful pm_goal_1 initPM 8125] := by
    rw [kS]
    simp only [fw_rotary_embedding]
    rw [kRel.value, l11o_rotary_allGather0_1d (denoteGraphDistributedFaithful sm_goal_1 initSM 4944)
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5054) (denoteGraphDistributedFaithful pm_goal_1 initPM 8100)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8101) 2048 4 64 (by omega) (by omega) (by omega)
      hspos kRel.shard0_shape kRel.shard1_shape, hcache, hpos, ← pc0, ← pc1, k0, k1]
    simp only [fw_rotary_embedding]
  have qs0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8122).shape = [2048, 16, 64] := by
    rw [q0]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 qRel.shard0_shape
  have qs1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8123).shape = [2048, 16, 64] := by
    rw [q1]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 qRel.shard1_shape
  have ks0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8124).shape = [2048, 4, 64] := by
    rw [k0]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 kRel.shard0_shape
  have ks1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8125).shape = [2048, 4, 64] := by
    rw [k1]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 kRel.shard1_shape
  refine ⟨⟨qval, ?_, qs0, qs1, by decide⟩, ⟨kval, ?_, ks0, ks1, by decide⟩⟩
  · rw [qval, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [qs0])]
    rfl
  · rw [kval, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [ks0])]
    rfl

end TrainVerify.Denote.GeneratedPatterns


