import denote.yoco_goals.L10FaithfulReductionKit

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- L5 ordinary V relation, derived from the preceding MoE boundary and init weight. -/
theorem l5o_v5218_rel_from_boundary (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (h : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5210)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8574) (denoteGraphDistributedFaithful pm_goal_1 initPM 8575)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5218)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8602) (denoteGraphDistributedFaithful pm_goal_1 initPM 8603)
      [4096, 4, 64] [2048, 4, 64] := by
  have ms := l10f_reduce1 sm_goal_1 initSM 197
    { rank := 0, op := "OpName.FW_multiref", ins := [5210], outs := [8004, 8008], params := [2] }
    5210 8004 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 5210 [8004, 8008] 2 rfl 8004 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l10f_reduce1 pm_goal_1 initPM 452
    { rank := 0, op := "OpName.FW_multiref", ins := [8574], outs := [15598, 15602], params := [2] }
    8574 15598 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 8574 [15598, 15602] 2 rfl 15598 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l10f_reduce1 pm_goal_1 initPM 453
    { rank := 1, op := "OpName.FW_multiref", ins := [8575], outs := [15606, 15610], params := [2] }
    8575 15606 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 8575 [15606, 15610] 2 rfl 15606 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hw1 := l10f_init_value initSM initPM hInit initGoal_5211
    (by native_decide) 5211 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rs := l10f_rms sm_goal_1 initSM 198 0 8004 5211 5212
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10f_rms pm_goal_1 initPM 454 0 15598 5211 8578
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10f_rms pm_goal_1 initPM 455 1 15606 5211 8579
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have rmsRel : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5212)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8578) (denoteGraphDistributedFaithful pm_goal_1 initPM 8579)
      [4096, 1024] [2048, 1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rs, ms, h.value, ← m0, ← m1, hw1,
        ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega)
          (by rw [m0]; exact h.shard0_shape) (by rw [m1]; exact h.shard1_shape), r0, r1]
    · rw [rs]; exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024 (by rw [ms]; exact h.full_shape)
    · rw [r0]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m0]; exact h.shard0_shape)
    · rw [r1]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m1]; exact h.shard1_shape)
  have vs := l10f_reduce1 sm_goal_1 initSM 199
    { rank := 0, op := "OpName.FW_multiref", ins := [5212], outs := [8013, 8017, 8021], params := [3] }
    5212 8021 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 5212 [8013, 8017, 8021] 3 rfl 8021 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have v0 := l10f_reduce1 pm_goal_1 initPM 456
    { rank := 0, op := "OpName.FW_multiref", ins := [8578], outs := [15332, 12988, 12996], params := [3] }
    8578 12996 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 8578 [15332, 12988, 12996] 3 rfl 12996 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have v1 := l10f_reduce1 pm_goal_1 initPM 457
    { rank := 1, op := "OpName.FW_multiref", ins := [8579], outs := [15334, 12989, 12997], params := [3] }
    8579 12997 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 8579 [15334, 12989, 12997] 3 rfl 12997 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at vs v0 v1
  have hw := l10f_init_value initSM initPM hInit initGoal_5217
    (by native_decide) 5217 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hws := l10f_init_shape initSM initPM hInit initGoal_5217
    (by native_decide) 5217 [4, 64, 1024] rfl rfl (by native_decide)
  have hpw : (denoteGraphDistributedFaithful pm_goal_1 initPM 5217).shape = [4, 64, 1024] := by
    rw [← hw]; exact hws
  have ps := l10f_per_head sm_goal_1 initSM 202 0 8021 5217 5218
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have p0 := l10f_per_head pm_goal_1 initPM 459 0 12996 5217 8602
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have p1 := l10f_per_head pm_goal_1 initPM 462 1 12997 5217 8603
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 12996).shape = [2048, 1024] := by
    rw [v0]; exact rmsRel.shard0_shape
  have hs1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 12997).shape = [2048, 1024] := by
    rw [v1]; exact rmsRel.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [ps, vs, rmsRel.value, ← v0, ← v1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, p0, p1]
  · rw [ps]; exact l11o_per_head_shape _ _ 4096 1024 4 64
      (by rw [vs]; exact rmsRel.full_shape) hws
  · rw [p0]; exact l11o_per_head_shape _ _ 2048 1024 4 64 hs0 hpw
  · rw [p1]; exact l11o_per_head_shape _ _ 2048 1024 4 64 hs1 hpw

/-- L5 ordinary rotary Q/K relations, derived from the preceding MoE boundary. -/
theorem l5o_q5220_k5221_rels_from_boundary (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (h : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5210)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8574) (denoteGraphDistributedFaithful pm_goal_1 initPM 8575)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5220)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8614) (denoteGraphDistributedFaithful pm_goal_1 initPM 8615)
      [4096, 16, 64] [2048, 16, 64] ∧
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5221)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8616) (denoteGraphDistributedFaithful pm_goal_1 initPM 8617)
      [4096, 4, 64] [2048, 4, 64] := by
  have ms := l10f_reduce1 sm_goal_1 initSM 197
    { rank := 0, op := "OpName.FW_multiref", ins := [5210], outs := [8004, 8008], params := [2] }
    5210 8004 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 5210 [8004, 8008] 2 rfl 8004 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l10f_reduce1 pm_goal_1 initPM 452
    { rank := 0, op := "OpName.FW_multiref", ins := [8574], outs := [15598, 15602], params := [2] }
    8574 15598 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 8574 [15598, 15602] 2 rfl 15598 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l10f_reduce1 pm_goal_1 initPM 453
    { rank := 1, op := "OpName.FW_multiref", ins := [8575], outs := [15606, 15610], params := [2] }
    8575 15606 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 8575 [15606, 15610] 2 rfl 15606 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hw1 := l10f_init_value initSM initPM hInit initGoal_5211
    (by native_decide) 5211 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rs := l10f_rms sm_goal_1 initSM 198 0 8004 5211 5212
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10f_rms pm_goal_1 initPM 454 0 15598 5211 8578
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10f_rms pm_goal_1 initPM 455 1 15606 5211 8579
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have rmsRel : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5212)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8578) (denoteGraphDistributedFaithful pm_goal_1 initPM 8579)
      [4096, 1024] [2048, 1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rs, ms, h.value, ← m0, ← m1, hw1,
        ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega)
          (by rw [m0]; exact h.shard0_shape) (by rw [m1]; exact h.shard1_shape), r0, r1]
    · rw [rs]; exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024 (by rw [ms]; exact h.full_shape)
    · rw [r0]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m0]; exact h.shard0_shape)
    · rw [r1]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m1]; exact h.shard1_shape)

  have qmS := l10f_reduce1 sm_goal_1 initSM 199
    { rank := 0, op := "OpName.FW_multiref", ins := [5212], outs := [8013, 8017, 8021], params := [3] }
    5212 8013 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 5212 [8013, 8017, 8021] 3 rfl 8013 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have qm0 := l10f_reduce1 pm_goal_1 initPM 456
    { rank := 0, op := "OpName.FW_multiref", ins := [8578], outs := [15332, 12988, 12996], params := [3] }
    8578 15332 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 8578 [15332, 12988, 12996] 3 rfl 15332 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have qm1 := l10f_reduce1 pm_goal_1 initPM 457
    { rank := 1, op := "OpName.FW_multiref", ins := [8579], outs := [15334, 12989, 12997], params := [3] }
    8579 15334 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 8579 [15334, 12989, 12997] 3 rfl 15334 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at qmS qm0 qm1
  have qg := l10f_allgather2 pm_goal_1 initPM 460 0 15332 15334 11886
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hwq := l10f_init_value initSM initPM hInit initGoal_5213
    (by native_decide) 5213 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hswq := l10f_init_shape initSM initPM hInit initGoal_5213
    (by native_decide) 5213 [16, 64, 1024] rfl rfl (by native_decide)
  have hpwq : (denoteGraphDistributedFaithful pm_goal_1 initPM 5213).shape = [16, 64, 1024] := by
    rw [← hwq]; exact hswq
  have qs := l10f_per_head sm_goal_1 initSM 200 0 8013 5213 5214
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  -- The shared Q output is written twice in PM; reduce at the final writer (rank 1).
  have qp := l10f_per_head pm_goal_1 initPM 464 1 11886 5213 5214
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hpmR : pm_goal_1.numRanks = 2 := rfl
  rw [hpmR] at qg
  have qeq : denoteGraphDistributedFaithful sm_goal_1 initSM 5214 = denoteGraphDistributedFaithful pm_goal_1 initPM 5214 := by
    rw [qs, qmS, rmsRel.value, ← qm0, ← qm1, ← qg, hwq, ← qp]
  have hqfullS : (denoteGraphDistributedFaithful sm_goal_1 initSM 5214).shape = [4096, 16, 64] := by
    rw [qs]
    exact l11o_per_head_shape _ _ 4096 1024 16 64
      (by rw [qmS]; exact rmsRel.full_shape) hswq
  have hqfullP : (denoteGraphDistributedFaithful pm_goal_1 initPM 5214).shape = [4096, 16, 64] := by
    rw [← qeq]; exact hqfullS
  have cq0 := l10f_chunk pm_goal_1 initPM 465 0 5214 8580
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have cq1 := l10f_chunk pm_goal_1 initPM 466 1 5214 8581
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hpmR] at cq0 cq1
  have hq0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8580).shape = [2048, 16, 64] := by
    rw [cq0, chunkPrimDimN_shape 0 2 0 _ [4096, 16, 64] hqfullP (by omega)]
    rfl
  have hq1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8581).shape = [2048, 16, 64] := by
    rw [cq1, chunkPrimDimN_shape 0 2 1 _ [4096, 16, 64] hqfullP (by omega)]
    rfl
  have qRel : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5214)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8580) (denoteGraphDistributedFaithful pm_goal_1 initPM 8581)
      [4096, 16, 64] [2048, 16, 64] := by
    refine ⟨?_, hqfullS, hq0, hq1, by decide⟩
    rw [qeq, cq0, cq1]
    exact (l11o_allGather0_reconstruct_chunks_3d 2048 16 64 (by omega) (by omega) (by omega)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5214) (by simpa using hqfullP)).symm

  have kmS := l10f_reduce1 sm_goal_1 initSM 199
    { rank := 0, op := "OpName.FW_multiref", ins := [5212], outs := [8013, 8017, 8021], params := [3] }
    5212 8017 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 5212 [8013, 8017, 8021] 3 rfl 8017 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have km0 := l10f_reduce1 pm_goal_1 initPM 456
    { rank := 0, op := "OpName.FW_multiref", ins := [8578], outs := [15332, 12988, 12996], params := [3] }
    8578 12988 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 8578 [15332, 12988, 12996] 3 rfl 12988 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have km1 := l10f_reduce1 pm_goal_1 initPM 457
    { rank := 1, op := "OpName.FW_multiref", ins := [8579], outs := [15334, 12989, 12997], params := [3] }
    8579 12989 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 8579 [15334, 12989, 12997] 3 rfl 12989 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at kmS km0 km1
  have hwk := l10f_init_value initSM initPM hInit initGoal_5215
    (by native_decide) 5215 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hswk := l10f_init_shape initSM initPM hInit initGoal_5215
    (by native_decide) 5215 [4, 64, 1024] rfl rfl (by native_decide)
  have hpwk : (denoteGraphDistributedFaithful pm_goal_1 initPM 5215).shape = [4, 64, 1024] := by
    rw [← hwk]; exact hswk
  have ks := l10f_per_head sm_goal_1 initSM 201 0 8017 5215 5216
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have kp0 := l10f_per_head pm_goal_1 initPM 458 0 12988 5215 8592
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have kp1 := l10f_per_head pm_goal_1 initPM 461 1 12989 5215 8593
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have kRel : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5216)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8592) (denoteGraphDistributedFaithful pm_goal_1 initPM 8593)
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
  have hpos := l10f_init_value initSM initPM hInit initGoal_5219
    (by native_decide) 5219 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hspos := l10f_init_shape initSM initPM hInit initGoal_5219
    (by native_decide) 5219 [4096] rfl rfl (by native_decide)
  have pc0 := l10f_chunk pm_goal_1 initPM 6 0 5219 8612
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have pc1 := l10f_chunk pm_goal_1 initPM 20 1 5219 8613
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hpmR] at pc0 pc1
  have qS := l10f_reduce4 sm_goal_1 initSM 203
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 5219, 5214, 5216],
      outs := [5220, 5221], params := [16, 4] }
    4944 5219 5214 5216 5220
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).1)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_fst_out sm_goal_1 st 0 16 4 4944 5219 5214 5216 5220 5221)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have kS := l10f_reduce4 sm_goal_1 initSM 203
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 5219, 5214, 5216],
      outs := [5220, 5221], params := [16, 4] }
    4944 5219 5214 5216 5221
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).2)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_snd_out sm_goal_1 st 0 16 4 4944 5219 5214 5216 5220 5221 (by decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have q0 := l10f_reduce4 pm_goal_1 initPM 467
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 8612, 8580, 8592],
      outs := [8614, 8616], params := [16, 4] }
    4944 8612 8580 8592 8614
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).1)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_fst_out pm_goal_1 st 0 16 4 4944 8612 8580 8592 8614 8616)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have k0 := l10f_reduce4 pm_goal_1 initPM 467
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 8612, 8580, 8592],
      outs := [8614, 8616], params := [16, 4] }
    4944 8612 8580 8592 8616
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).2)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_snd_out pm_goal_1 st 0 16 4 4944 8612 8580 8592 8614 8616 (by decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have q1 := l10f_reduce4 pm_goal_1 initPM 468
    { rank := 1, op := "OpName.FW_rotary_embedding", ins := [4944, 8613, 8581, 8593],
      outs := [8615, 8617], params := [16, 4] }
    4944 8613 8581 8593 8615
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).1)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_fst_out pm_goal_1 st 1 16 4 4944 8613 8581 8593 8615 8617)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have k1 := l10f_reduce4 pm_goal_1 initPM 468
    { rank := 1, op := "OpName.FW_rotary_embedding", ins := [4944, 8613, 8581, 8593],
      outs := [8615, 8617], params := [16, 4] }
    4944 8613 8581 8593 8617
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).2)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_snd_out pm_goal_1 st 1 16 4 4944 8613 8581 8593 8615 8617 (by decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have qval : denoteGraphDistributedFaithful sm_goal_1 initSM 5220 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributedFaithful pm_goal_1 initPM 8614, denoteGraphDistributedFaithful pm_goal_1 initPM 8615] := by
    rw [qS]
    simp only [fw_rotary_embedding]
    rw [qRel.value, l11o_rotary_allGather0_1d (denoteGraphDistributedFaithful sm_goal_1 initSM 4944)
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5219) (denoteGraphDistributedFaithful pm_goal_1 initPM 8580)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8581) 2048 16 64 (by omega) (by omega) (by omega)
      hspos qRel.shard0_shape qRel.shard1_shape, hcache, hpos, ← pc0, ← pc1, q0, q1]
    simp only [fw_rotary_embedding]
  have kval : denoteGraphDistributedFaithful sm_goal_1 initSM 5221 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributedFaithful pm_goal_1 initPM 8616, denoteGraphDistributedFaithful pm_goal_1 initPM 8617] := by
    rw [kS]
    simp only [fw_rotary_embedding]
    rw [kRel.value, l11o_rotary_allGather0_1d (denoteGraphDistributedFaithful sm_goal_1 initSM 4944)
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5219) (denoteGraphDistributedFaithful pm_goal_1 initPM 8592)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8593) 2048 4 64 (by omega) (by omega) (by omega)
      hspos kRel.shard0_shape kRel.shard1_shape, hcache, hpos, ← pc0, ← pc1, k0, k1]
    simp only [fw_rotary_embedding]
  have qs0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8614).shape = [2048, 16, 64] := by
    rw [q0]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 qRel.shard0_shape
  have qs1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8615).shape = [2048, 16, 64] := by
    rw [q1]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 qRel.shard1_shape
  have ks0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8616).shape = [2048, 4, 64] := by
    rw [k0]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 kRel.shard0_shape
  have ks1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8617).shape = [2048, 4, 64] := by
    rw [k1]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 kRel.shard1_shape
  refine ⟨⟨qval, ?_, qs0, qs1, by decide⟩, ⟨kval, ?_, ks0, ks1, by decide⟩⟩
  · rw [qval, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [qs0])]
    rfl
  · rw [kval, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [ks0])]
    rfl

end TrainVerify.Denote.GeneratedPatterns
