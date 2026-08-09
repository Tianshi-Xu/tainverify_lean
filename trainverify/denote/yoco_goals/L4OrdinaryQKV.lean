import denote.yoco_goals.L10FaithfulReductionKit

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- L4 ordinary V relation, derived from the preceding MoE boundary and init weight. -/
theorem l4o_v5163_rel_from_boundary (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (h : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5155)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8410) (denoteGraphDistributedFaithful pm_goal_1 initPM 8411)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5163)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8438) (denoteGraphDistributedFaithful pm_goal_1 initPM 8439)
      [4096, 4, 64] [2048, 4, 64] := by
  have ms := l10f_reduce1 sm_goal_1 initSM 158
    { rank := 0, op := "OpName.FW_multiref", ins := [5155], outs := [7952, 7956], params := [2] }
    5155 7952 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 5155 [7952, 7956] 2 rfl 7952 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l10f_reduce1 pm_goal_1 initPM 368
    { rank := 0, op := "OpName.FW_multiref", ins := [8410], outs := [15566, 15570], params := [2] }
    8410 15566 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 8410 [15566, 15570] 2 rfl 15566 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l10f_reduce1 pm_goal_1 initPM 369
    { rank := 1, op := "OpName.FW_multiref", ins := [8411], outs := [15574, 15578], params := [2] }
    8411 15574 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 8411 [15574, 15578] 2 rfl 15574 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hw1 := l10f_init_value initSM initPM hInit initGoal_5156
    (by native_decide) 5156 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rs := l10f_rms sm_goal_1 initSM 159 0 7952 5156 5157
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10f_rms pm_goal_1 initPM 370 0 15566 5156 8414
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10f_rms pm_goal_1 initPM 371 1 15574 5156 8415
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have rmsRel : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5157)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8414) (denoteGraphDistributedFaithful pm_goal_1 initPM 8415)
      [4096, 1024] [2048, 1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rs, ms, h.value, ← m0, ← m1, hw1,
        ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega)
          (by rw [m0]; exact h.shard0_shape) (by rw [m1]; exact h.shard1_shape), r0, r1]
    · rw [rs]; exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024 (by rw [ms]; exact h.full_shape)
    · rw [r0]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m0]; exact h.shard0_shape)
    · rw [r1]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m1]; exact h.shard1_shape)
  have vs := l10f_reduce1 sm_goal_1 initSM 160
    { rank := 0, op := "OpName.FW_multiref", ins := [5157], outs := [7961, 7965, 7969], params := [3] }
    5157 7969 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 5157 [7961, 7965, 7969] 3 rfl 7969 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have v0 := l10f_reduce1 pm_goal_1 initPM 372
    { rank := 0, op := "OpName.FW_multiref", ins := [8414], outs := [15324, 12862, 12870], params := [3] }
    8414 12870 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 8414 [15324, 12862, 12870] 3 rfl 12870 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have v1 := l10f_reduce1 pm_goal_1 initPM 373
    { rank := 1, op := "OpName.FW_multiref", ins := [8415], outs := [15326, 12863, 12871], params := [3] }
    8415 12871 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 8415 [15326, 12863, 12871] 3 rfl 12871 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at vs v0 v1
  have hw := l10f_init_value initSM initPM hInit initGoal_5162
    (by native_decide) 5162 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hws := l10f_init_shape initSM initPM hInit initGoal_5162
    (by native_decide) 5162 [4, 64, 1024] rfl rfl (by native_decide)
  have hpw : (denoteGraphDistributedFaithful pm_goal_1 initPM 5162).shape = [4, 64, 1024] := by
    rw [← hw]; exact hws
  have ps := l10f_per_head sm_goal_1 initSM 163 0 7969 5162 5163
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have p0 := l10f_per_head pm_goal_1 initPM 375 0 12870 5162 8438
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have p1 := l10f_per_head pm_goal_1 initPM 378 1 12871 5162 8439
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 12870).shape = [2048, 1024] := by
    rw [v0]; exact rmsRel.shard0_shape
  have hs1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 12871).shape = [2048, 1024] := by
    rw [v1]; exact rmsRel.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [ps, vs, rmsRel.value, ← v0, ← v1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, p0, p1]
  · rw [ps]; exact l11o_per_head_shape _ _ 4096 1024 4 64
      (by rw [vs]; exact rmsRel.full_shape) hws
  · rw [p0]; exact l11o_per_head_shape _ _ 2048 1024 4 64 hs0 hpw
  · rw [p1]; exact l11o_per_head_shape _ _ 2048 1024 4 64 hs1 hpw

/-- L4 ordinary rotary Q/K relations, derived from the preceding MoE boundary. -/
theorem l4o_q5165_k5166_rels_from_boundary (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (h : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5155)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8410) (denoteGraphDistributedFaithful pm_goal_1 initPM 8411)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5165)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8450) (denoteGraphDistributedFaithful pm_goal_1 initPM 8451)
      [4096, 16, 64] [2048, 16, 64] ∧
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5166)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8452) (denoteGraphDistributedFaithful pm_goal_1 initPM 8453)
      [4096, 4, 64] [2048, 4, 64] := by
  have ms := l10f_reduce1 sm_goal_1 initSM 158
    { rank := 0, op := "OpName.FW_multiref", ins := [5155], outs := [7952, 7956], params := [2] }
    5155 7952 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 5155 [7952, 7956] 2 rfl 7952 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l10f_reduce1 pm_goal_1 initPM 368
    { rank := 0, op := "OpName.FW_multiref", ins := [8410], outs := [15566, 15570], params := [2] }
    8410 15566 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 8410 [15566, 15570] 2 rfl 15566 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l10f_reduce1 pm_goal_1 initPM 369
    { rank := 1, op := "OpName.FW_multiref", ins := [8411], outs := [15574, 15578], params := [2] }
    8411 15574 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 8411 [15574, 15578] 2 rfl 15574 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hw1 := l10f_init_value initSM initPM hInit initGoal_5156
    (by native_decide) 5156 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rs := l10f_rms sm_goal_1 initSM 159 0 7952 5156 5157
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10f_rms pm_goal_1 initPM 370 0 15566 5156 8414
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10f_rms pm_goal_1 initPM 371 1 15574 5156 8415
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have rmsRel : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5157)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8414) (denoteGraphDistributedFaithful pm_goal_1 initPM 8415)
      [4096, 1024] [2048, 1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rs, ms, h.value, ← m0, ← m1, hw1,
        ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega)
          (by rw [m0]; exact h.shard0_shape) (by rw [m1]; exact h.shard1_shape), r0, r1]
    · rw [rs]; exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024 (by rw [ms]; exact h.full_shape)
    · rw [r0]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m0]; exact h.shard0_shape)
    · rw [r1]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m1]; exact h.shard1_shape)

  have qmS := l10f_reduce1 sm_goal_1 initSM 160
    { rank := 0, op := "OpName.FW_multiref", ins := [5157], outs := [7961, 7965, 7969], params := [3] }
    5157 7961 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 5157 [7961, 7965, 7969] 3 rfl 7961 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have qm0 := l10f_reduce1 pm_goal_1 initPM 372
    { rank := 0, op := "OpName.FW_multiref", ins := [8414], outs := [15324, 12862, 12870], params := [3] }
    8414 15324 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 8414 [15324, 12862, 12870] 3 rfl 15324 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have qm1 := l10f_reduce1 pm_goal_1 initPM 373
    { rank := 1, op := "OpName.FW_multiref", ins := [8415], outs := [15326, 12863, 12871], params := [3] }
    8415 15326 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 8415 [15326, 12863, 12871] 3 rfl 15326 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at qmS qm0 qm1
  have qg := l10f_allgather2 pm_goal_1 initPM 376 0 15324 15326 11854
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hwq := l10f_init_value initSM initPM hInit initGoal_5158
    (by native_decide) 5158 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hswq := l10f_init_shape initSM initPM hInit initGoal_5158
    (by native_decide) 5158 [16, 64, 1024] rfl rfl (by native_decide)
  have hpwq : (denoteGraphDistributedFaithful pm_goal_1 initPM 5158).shape = [16, 64, 1024] := by
    rw [← hwq]; exact hswq
  have qs := l10f_per_head sm_goal_1 initSM 161 0 7961 5158 5159
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  -- The shared Q output is written twice in PM; reduce at the final writer (rank 1).
  have qp := l10f_per_head pm_goal_1 initPM 380 1 11854 5158 5159
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hpmR : pm_goal_1.numRanks = 2 := rfl
  rw [hpmR] at qg
  have qeq : denoteGraphDistributedFaithful sm_goal_1 initSM 5159 = denoteGraphDistributedFaithful pm_goal_1 initPM 5159 := by
    rw [qs, qmS, rmsRel.value, ← qm0, ← qm1, ← qg, hwq, ← qp]
  have hqfullS : (denoteGraphDistributedFaithful sm_goal_1 initSM 5159).shape = [4096, 16, 64] := by
    rw [qs]
    exact l11o_per_head_shape _ _ 4096 1024 16 64
      (by rw [qmS]; exact rmsRel.full_shape) hswq
  have hqfullP : (denoteGraphDistributedFaithful pm_goal_1 initPM 5159).shape = [4096, 16, 64] := by
    rw [← qeq]; exact hqfullS
  have cq0 := l10f_chunk pm_goal_1 initPM 381 0 5159 8416
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have cq1 := l10f_chunk pm_goal_1 initPM 382 1 5159 8417
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hpmR] at cq0 cq1
  have hq0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8416).shape = [2048, 16, 64] := by
    rw [cq0, chunkPrimDimN_shape 0 2 0 _ [4096, 16, 64] hqfullP (by omega)]
    rfl
  have hq1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8417).shape = [2048, 16, 64] := by
    rw [cq1, chunkPrimDimN_shape 0 2 1 _ [4096, 16, 64] hqfullP (by omega)]
    rfl
  have qRel : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5159)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8416) (denoteGraphDistributedFaithful pm_goal_1 initPM 8417)
      [4096, 16, 64] [2048, 16, 64] := by
    refine ⟨?_, hqfullS, hq0, hq1, by decide⟩
    rw [qeq, cq0, cq1]
    exact (l11o_allGather0_reconstruct_chunks_3d 2048 16 64 (by omega) (by omega) (by omega)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 5159) (by simpa using hqfullP)).symm

  have kmS := l10f_reduce1 sm_goal_1 initSM 160
    { rank := 0, op := "OpName.FW_multiref", ins := [5157], outs := [7961, 7965, 7969], params := [3] }
    5157 7965 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 5157 [7961, 7965, 7969] 3 rfl 7965 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have km0 := l10f_reduce1 pm_goal_1 initPM 372
    { rank := 0, op := "OpName.FW_multiref", ins := [8414], outs := [15324, 12862, 12870], params := [3] }
    8414 12862 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 8414 [15324, 12862, 12870] 3 rfl 12862 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have km1 := l10f_reduce1 pm_goal_1 initPM 373
    { rank := 1, op := "OpName.FW_multiref", ins := [8415], outs := [15326, 12863, 12871], params := [3] }
    8415 12863 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 8415 [15326, 12863, 12871] 3 rfl 12863 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at kmS km0 km1
  have hwk := l10f_init_value initSM initPM hInit initGoal_5160
    (by native_decide) 5160 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hswk := l10f_init_shape initSM initPM hInit initGoal_5160
    (by native_decide) 5160 [4, 64, 1024] rfl rfl (by native_decide)
  have hpwk : (denoteGraphDistributedFaithful pm_goal_1 initPM 5160).shape = [4, 64, 1024] := by
    rw [← hwk]; exact hswk
  have ks := l10f_per_head sm_goal_1 initSM 162 0 7965 5160 5161
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have kp0 := l10f_per_head pm_goal_1 initPM 374 0 12862 5160 8428
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have kp1 := l10f_per_head pm_goal_1 initPM 377 1 12863 5160 8429
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have kRel : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5161)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8428) (denoteGraphDistributedFaithful pm_goal_1 initPM 8429)
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
  have hpos := l10f_init_value initSM initPM hInit initGoal_5164
    (by native_decide) 5164 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hspos := l10f_init_shape initSM initPM hInit initGoal_5164
    (by native_decide) 5164 [4096] rfl rfl (by native_decide)
  have pc0 := l10f_chunk pm_goal_1 initPM 5 0 5164 8448
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have pc1 := l10f_chunk pm_goal_1 initPM 19 1 5164 8449
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hpmR] at pc0 pc1
  have qS := l10f_reduce4 sm_goal_1 initSM 164
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 5164, 5159, 5161],
      outs := [5165, 5166], params := [16, 4] }
    4944 5164 5159 5161 5165
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).1)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_fst_out sm_goal_1 st 0 16 4 4944 5164 5159 5161 5165 5166)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have kS := l10f_reduce4 sm_goal_1 initSM 164
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 5164, 5159, 5161],
      outs := [5165, 5166], params := [16, 4] }
    4944 5164 5159 5161 5166
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).2)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_snd_out sm_goal_1 st 0 16 4 4944 5164 5159 5161 5165 5166 (by decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have q0 := l10f_reduce4 pm_goal_1 initPM 383
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 8448, 8416, 8428],
      outs := [8450, 8452], params := [16, 4] }
    4944 8448 8416 8428 8450
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).1)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_fst_out pm_goal_1 st 0 16 4 4944 8448 8416 8428 8450 8452)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have k0 := l10f_reduce4 pm_goal_1 initPM 383
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 8448, 8416, 8428],
      outs := [8450, 8452], params := [16, 4] }
    4944 8448 8416 8428 8452
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).2)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_snd_out pm_goal_1 st 0 16 4 4944 8448 8416 8428 8450 8452 (by decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have q1 := l10f_reduce4 pm_goal_1 initPM 384
    { rank := 1, op := "OpName.FW_rotary_embedding", ins := [4944, 8449, 8417, 8429],
      outs := [8451, 8453], params := [16, 4] }
    4944 8449 8417 8429 8451
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).1)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_fst_out pm_goal_1 st 1 16 4 4944 8449 8417 8429 8451 8453)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have k1 := l10f_reduce4 pm_goal_1 initPM 384
    { rank := 1, op := "OpName.FW_rotary_embedding", ins := [4944, 8449, 8417, 8429],
      outs := [8451, 8453], params := [16, 4] }
    4944 8449 8417 8429 8453
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).2)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_snd_out pm_goal_1 st 1 16 4 4944 8449 8417 8429 8451 8453 (by decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have qval : denoteGraphDistributedFaithful sm_goal_1 initSM 5165 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributedFaithful pm_goal_1 initPM 8450, denoteGraphDistributedFaithful pm_goal_1 initPM 8451] := by
    rw [qS]
    simp only [fw_rotary_embedding]
    rw [qRel.value, l11o_rotary_allGather0_1d (denoteGraphDistributedFaithful sm_goal_1 initSM 4944)
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5164) (denoteGraphDistributedFaithful pm_goal_1 initPM 8416)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8417) 2048 16 64 (by omega) (by omega) (by omega)
      hspos qRel.shard0_shape qRel.shard1_shape, hcache, hpos, ← pc0, ← pc1, q0, q1]
    simp only [fw_rotary_embedding]
  have kval : denoteGraphDistributedFaithful sm_goal_1 initSM 5166 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributedFaithful pm_goal_1 initPM 8452, denoteGraphDistributedFaithful pm_goal_1 initPM 8453] := by
    rw [kS]
    simp only [fw_rotary_embedding]
    rw [kRel.value, l11o_rotary_allGather0_1d (denoteGraphDistributedFaithful sm_goal_1 initSM 4944)
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5164) (denoteGraphDistributedFaithful pm_goal_1 initPM 8428)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 8429) 2048 4 64 (by omega) (by omega) (by omega)
      hspos kRel.shard0_shape kRel.shard1_shape, hcache, hpos, ← pc0, ← pc1, k0, k1]
    simp only [fw_rotary_embedding]
  have qs0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8450).shape = [2048, 16, 64] := by
    rw [q0]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 qRel.shard0_shape
  have qs1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8451).shape = [2048, 16, 64] := by
    rw [q1]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 qRel.shard1_shape
  have ks0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8452).shape = [2048, 4, 64] := by
    rw [k0]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 kRel.shard0_shape
  have ks1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 8453).shape = [2048, 4, 64] := by
    rw [k1]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 kRel.shard1_shape
  refine ⟨⟨qval, ?_, qs0, qs1, by decide⟩, ⟨kval, ?_, ks0, ks1, by decide⟩⟩
  · rw [qval, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [qs0])]
    rfl
  · rw [kval, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [ks0])]
    rfl

end TrainVerify.Denote.GeneratedPatterns
