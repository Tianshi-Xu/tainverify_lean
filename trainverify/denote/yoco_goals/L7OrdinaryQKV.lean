import denote.yoco_goals.L10FaithfulReductionKit

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- L7 ordinary V relation, derived from the preceding MoE boundary and init weight. -/
theorem l7o_v5328_rel_from_boundary (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (h : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5320)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8902) (denoteGraphDistributedFaithful pm_goal_1 initPM 8903)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5328)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8930) (denoteGraphDistributedFaithful pm_goal_1 initPM 8931)
      [4096, 4, 64] [2048, 4, 64] := by
  have ms := l10f_reduce1 sm_goal_1 initSM 275
    { rank := 0, op := "OpName.FW_multiref", ins := [5320], outs := [8108, 8112], params := [2] }
    5320 8108 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 5320 [8108, 8112] 2 rfl 8108 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l10f_reduce1 pm_goal_1 initPM 620
    { rank := 0, op := "OpName.FW_multiref", ins := [8902], outs := [15662, 15666], params := [2] }
    8902 15662 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 8902 [15662, 15666] 2 rfl 15662 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l10f_reduce1 pm_goal_1 initPM 621
    { rank := 1, op := "OpName.FW_multiref", ins := [8903], outs := [15670, 15674], params := [2] }
    8903 15670 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 8903 [15670, 15674] 2 rfl 15670 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hw1 := l10f_init_value initSM initPM hInit initGoal_5321
    (by native_decide) 5321 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rs := l10f_rms sm_goal_1 initSM 276 0 8108 5321 5322
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10f_rms pm_goal_1 initPM 622 0 15662 5321 8906
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10f_rms pm_goal_1 initPM 623 1 15670 5321 8907
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have rmsRel : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5322)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8906) (denoteGraphDistributedFaithful pm_goal_1 initPM 8907)
      [4096, 1024] [2048, 1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rs, ms, h.value, ← m0, ← m1, hw1,
        ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega)
          (by rw [m0]; exact h.shard0_shape) (by rw [m1]; exact h.shard1_shape), r0, r1]
    · rw [rs]; exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024 (by rw [ms]; exact h.full_shape)
    · rw [r0]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m0]; exact h.shard0_shape)
    · rw [r1]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m1]; exact h.shard1_shape)
  have vs := l10f_reduce1 sm_goal_1 initSM 277
    { rank := 0, op := "OpName.FW_multiref", ins := [5322], outs := [8117, 8121, 8125], params := [3] }
    5322 8125 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 5322 [8117, 8121, 8125] 3 rfl 8125 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have v0 := l10f_reduce1 pm_goal_1 initPM 624
    { rank := 0, op := "OpName.FW_multiref", ins := [8906], outs := [15348, 13240, 13248], params := [3] }
    8906 13248 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 8906 [15348, 13240, 13248] 3 rfl 13248 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have v1 := l10f_reduce1 pm_goal_1 initPM 625
    { rank := 1, op := "OpName.FW_multiref", ins := [8907], outs := [15350, 13241, 13249], params := [3] }
    8907 13249 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 8907 [15350, 13241, 13249] 3 rfl 13249 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at vs v0 v1
  have hw := l10f_init_value initSM initPM hInit initGoal_5327
    (by native_decide) 5327 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hws := l10f_init_shape initSM initPM hInit initGoal_5327
    (by native_decide) 5327 [4, 64, 1024] rfl rfl (by native_decide)
  have hpw : (denoteGraphDistributedFaithful pm_goal_1 initPM 5327).shape = [4, 64, 1024] := by
    rw [← hw]; exact hws
  have ps := l10f_per_head sm_goal_1 initSM 280 0 8125 5327 5328
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have p0 := l10f_per_head pm_goal_1 initPM 627 0 13248 5327 8930
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have p1 := l10f_per_head pm_goal_1 initPM 630 1 13249 5327 8931
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 13248).shape = [2048, 1024] := by
    rw [v0]; exact rmsRel.shard0_shape
  have hs1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 13249).shape = [2048, 1024] := by
    rw [v1]; exact rmsRel.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [ps, vs, rmsRel.value, ← v0, ← v1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, p0, p1]
  · rw [ps]; exact l11o_per_head_shape _ _ 4096 1024 4 64
      (by rw [vs]; exact rmsRel.full_shape) hws
  · rw [p0]; exact l11o_per_head_shape _ _ 2048 1024 4 64 hs0 hpw
  · rw [p1]; exact l11o_per_head_shape _ _ 2048 1024 4 64 hs1 hpw

/-- L7 ordinary rotary Q/K relations, derived from the preceding MoE boundary. -/
theorem l7o_q5330_k5331_rels_from_boundary (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (h : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5320)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8902) (denoteGraphDistributedFaithful pm_goal_1 initPM 8903)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5330)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8942) (denoteGraphDistributedFaithful pm_goal_1 initPM 8943)
      [4096, 16, 64] [2048, 16, 64] ∧
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5331)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8944) (denoteGraphDistributedFaithful pm_goal_1 initPM 8945)
      [4096, 4, 64] [2048, 4, 64] := by
  have ms := l10f_reduce1 sm_goal_1 initSM 275
    { rank := 0, op := "OpName.FW_multiref", ins := [5320], outs := [8108, 8112], params := [2] }
    5320 8108 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 5320 [8108, 8112] 2 rfl 8108 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l10f_reduce1 pm_goal_1 initPM 620
    { rank := 0, op := "OpName.FW_multiref", ins := [8902], outs := [15662, 15666], params := [2] }
    8902 15662 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 8902 [15662, 15666] 2 rfl 15662 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l10f_reduce1 pm_goal_1 initPM 621
    { rank := 1, op := "OpName.FW_multiref", ins := [8903], outs := [15670, 15674], params := [2] }
    8903 15670 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 8903 [15670, 15674] 2 rfl 15670 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hw1 := l10f_init_value initSM initPM hInit initGoal_5321
    (by native_decide) 5321 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rs := l10f_rms sm_goal_1 initSM 276 0 8108 5321 5322
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10f_rms pm_goal_1 initPM 622 0 15662 5321 8906
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10f_rms pm_goal_1 initPM 623 1 15670 5321 8907
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have rmsRel : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5322)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8906) (denoteGraphDistributedFaithful pm_goal_1 initPM 8907)
      [4096, 1024] [2048, 1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rs, ms, h.value, ← m0, ← m1, hw1,
        ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega)
          (by rw [m0]; exact h.shard0_shape) (by rw [m1]; exact h.shard1_shape), r0, r1]
    · rw [rs]; exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024 (by rw [ms]; exact h.full_shape)
    · rw [r0]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m0]; exact h.shard0_shape)
    · rw [r1]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m1]; exact h.shard1_shape)

  have qmS := l10f_reduce1 sm_goal_1 initSM 277
    { rank := 0, op := "OpName.FW_multiref", ins := [5322], outs := [8117, 8121, 8125], params := [3] }
    5322 8117 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 5322 [8117, 8121, 8125] 3 rfl 8117 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have qm0 := l10f_reduce1 pm_goal_1 initPM 624
    { rank := 0, op := "OpName.FW_multiref", ins := [8906], outs := [15348, 13240, 13248], params := [3] }
    8906 15348 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 8906 [15348, 13240, 13248] 3 rfl 15348 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have qm1 := l10f_reduce1 pm_goal_1 initPM 625
    { rank := 1, op := "OpName.FW_multiref", ins := [8907], outs := [15350, 13241, 13249], params := [3] }
    8907 15350 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 8907 [15350, 13241, 13249] 3 rfl 15350 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at qmS qm0 qm1
  have qg := l10f_allgather2 pm_goal_1 initPM 628 0 15348 15350 11950
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hwq := l10f_init_value initSM initPM hInit initGoal_5323
    (by native_decide) 5323 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hswq := l10f_init_shape initSM initPM hInit initGoal_5323
    (by native_decide) 5323 [16, 64, 1024] rfl rfl (by native_decide)
  have hpwq : (denoteGraphDistributedFaithful pm_goal_1 initPM 5323).shape = [16, 64, 1024] := by
    rw [← hwq]; exact hswq
  have qs := l10f_per_head sm_goal_1 initSM 278 0 8117 5323 5324
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  -- The shared Q output is written twice in PM; reduce at the final writer (rank 1).
  have qp := l10f_per_head pm_goal_1 initPM 632 1 11950 5323 5324
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hpmR : pm_goal_1.numRanks = 2 := rfl
  rw [hpmR] at qg
  have qeq : denoteGraphDistributedFaithful sm_goal_1 initSM 5324 = denoteGraphDistributedFaithful pm_goal_1 initPM 5324 := by
    rw [qs, qmS, rmsRel.value, ← qm0, ← qm1, ← qg, hwq, ← qp]
  have hqfullS : (denoteGraphDistributedFaithful sm_goal_1 initSM 5324).shape = [4096, 16, 64] := by
    rw [qs]
    exact l11o_per_head_shape _ _ 4096 1024 16 64
      (by rw [qmS]; exact rmsRel.full_shape) hswq
  have hqfullP : (denoteGraphDistributedFaithful pm_goal_1 initPM 5324).shape = [4096, 16, 64] := by
    rw [← qeq]; exact hqfullS
  have cq0 := l10f_chunk pm_goal_1 initPM 633 0 5324 8908
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have cq1 := l10f_chunk pm_goal_1 initPM 634 1 5324 8909
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hpmR] at cq0 cq1
  have hq0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8908).shape = [2048, 16, 64] := by
    rw [cq0, chunkPrimDimN_shape 0 2 0 _ [4096, 16, 64] hqfullP (by omega)]
    rfl
  have hq1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8909).shape = [2048, 16, 64] := by
    rw [cq1, chunkPrimDimN_shape 0 2 1 _ [4096, 16, 64] hqfullP (by omega)]
    rfl
  have qRel : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5324)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8908) (denoteGraphDistributedFaithful pm_goal_1 initPM 8909)
      [4096, 16, 64] [2048, 16, 64] := by
    refine ⟨?_, hqfullS, hq0, hq1, by decide⟩
    rw [qeq, cq0, cq1]
    exact (l11o_allGather0_reconstruct_chunks_3d 2048 16 64 (by omega) (by omega) (by omega)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5324) (by simpa using hqfullP)).symm

  have kmS := l10f_reduce1 sm_goal_1 initSM 277
    { rank := 0, op := "OpName.FW_multiref", ins := [5322], outs := [8117, 8121, 8125], params := [3] }
    5322 8121 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 5322 [8117, 8121, 8125] 3 rfl 8121 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have km0 := l10f_reduce1 pm_goal_1 initPM 624
    { rank := 0, op := "OpName.FW_multiref", ins := [8906], outs := [15348, 13240, 13248], params := [3] }
    8906 13240 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 8906 [15348, 13240, 13248] 3 rfl 13240 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have km1 := l10f_reduce1 pm_goal_1 initPM 625
    { rank := 1, op := "OpName.FW_multiref", ins := [8907], outs := [15350, 13241, 13249], params := [3] }
    8907 13241 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 8907 [15350, 13241, 13249] 3 rfl 13241 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at kmS km0 km1
  have hwk := l10f_init_value initSM initPM hInit initGoal_5325
    (by native_decide) 5325 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hswk := l10f_init_shape initSM initPM hInit initGoal_5325
    (by native_decide) 5325 [4, 64, 1024] rfl rfl (by native_decide)
  have hpwk : (denoteGraphDistributedFaithful pm_goal_1 initPM 5325).shape = [4, 64, 1024] := by
    rw [← hwk]; exact hswk
  have ks := l10f_per_head sm_goal_1 initSM 279 0 8121 5325 5326
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have kp0 := l10f_per_head pm_goal_1 initPM 626 0 13240 5325 8920
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have kp1 := l10f_per_head pm_goal_1 initPM 629 1 13241 5325 8921
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have kRel : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5326)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8920) (denoteGraphDistributedFaithful pm_goal_1 initPM 8921)
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
  have hpos := l10f_init_value initSM initPM hInit initGoal_5329
    (by native_decide) 5329 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hspos := l10f_init_shape initSM initPM hInit initGoal_5329
    (by native_decide) 5329 [4096] rfl rfl (by native_decide)
  have pc0 := l10f_chunk pm_goal_1 initPM 8 0 5329 8940
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have pc1 := l10f_chunk pm_goal_1 initPM 22 1 5329 8941
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hpmR] at pc0 pc1
  have qS := l10f_reduce4 sm_goal_1 initSM 281
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 5329, 5324, 5326],
      outs := [5330, 5331], params := [16, 4] }
    4944 5329 5324 5326 5330
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).1)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_fst_out sm_goal_1 st 0 16 4 4944 5329 5324 5326 5330 5331)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have kS := l10f_reduce4 sm_goal_1 initSM 281
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 5329, 5324, 5326],
      outs := [5330, 5331], params := [16, 4] }
    4944 5329 5324 5326 5331
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).2)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_snd_out sm_goal_1 st 0 16 4 4944 5329 5324 5326 5330 5331 (by decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have q0 := l10f_reduce4 pm_goal_1 initPM 635
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 8940, 8908, 8920],
      outs := [8942, 8944], params := [16, 4] }
    4944 8940 8908 8920 8942
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).1)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_fst_out pm_goal_1 st 0 16 4 4944 8940 8908 8920 8942 8944)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have k0 := l10f_reduce4 pm_goal_1 initPM 635
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 8940, 8908, 8920],
      outs := [8942, 8944], params := [16, 4] }
    4944 8940 8908 8920 8944
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).2)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_snd_out pm_goal_1 st 0 16 4 4944 8940 8908 8920 8942 8944 (by decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have q1 := l10f_reduce4 pm_goal_1 initPM 636
    { rank := 1, op := "OpName.FW_rotary_embedding", ins := [4944, 8941, 8909, 8921],
      outs := [8943, 8945], params := [16, 4] }
    4944 8941 8909 8921 8943
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).1)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_fst_out pm_goal_1 st 1 16 4 4944 8941 8909 8921 8943 8945)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have k1 := l10f_reduce4 pm_goal_1 initPM 636
    { rank := 1, op := "OpName.FW_rotary_embedding", ins := [4944, 8941, 8909, 8921],
      outs := [8943, 8945], params := [16, 4] }
    4944 8941 8909 8921 8945
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).2)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_snd_out pm_goal_1 st 1 16 4 4944 8941 8909 8921 8943 8945 (by decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have qval : denoteGraphDistributedFaithful sm_goal_1 initSM 5330 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributedFaithful pm_goal_1 initPM 8942, denoteGraphDistributedFaithful pm_goal_1 initPM 8943] := by
    rw [qS]
    simp only [fw_rotary_embedding]
    rw [qRel.value, l11o_rotary_allGather0_1d (denoteGraphDistributedFaithful sm_goal_1 initSM 4944)
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5329) (denoteGraphDistributedFaithful pm_goal_1 initPM 8908)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8909) 2048 16 64 (by omega) (by omega) (by omega)
      hspos qRel.shard0_shape qRel.shard1_shape, hcache, hpos, ← pc0, ← pc1, q0, q1]
    simp only [fw_rotary_embedding]
  have kval : denoteGraphDistributedFaithful sm_goal_1 initSM 5331 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributedFaithful pm_goal_1 initPM 8944, denoteGraphDistributedFaithful pm_goal_1 initPM 8945] := by
    rw [kS]
    simp only [fw_rotary_embedding]
    rw [kRel.value, l11o_rotary_allGather0_1d (denoteGraphDistributedFaithful sm_goal_1 initSM 4944)
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5329) (denoteGraphDistributedFaithful pm_goal_1 initPM 8920)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8921) 2048 4 64 (by omega) (by omega) (by omega)
      hspos kRel.shard0_shape kRel.shard1_shape, hcache, hpos, ← pc0, ← pc1, k0, k1]
    simp only [fw_rotary_embedding]
  have qs0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8942).shape = [2048, 16, 64] := by
    rw [q0]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 qRel.shard0_shape
  have qs1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8943).shape = [2048, 16, 64] := by
    rw [q1]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 qRel.shard1_shape
  have ks0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8944).shape = [2048, 4, 64] := by
    rw [k0]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 kRel.shard0_shape
  have ks1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8945).shape = [2048, 4, 64] := by
    rw [k1]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 kRel.shard1_shape
  refine ⟨⟨qval, ?_, qs0, qs1, by decide⟩, ⟨kval, ?_, ks0, ks1, by decide⟩⟩
  · rw [qval, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [qs0])]
    rfl
  · rw [kval, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [ks0])]
    rfl

end TrainVerify.Denote.GeneratedPatterns
