import denote.yoco_goals.L10FaithfulReductionKit

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- L0 ordinary V relation, derived from the preceding MoE boundary and init weight. -/
theorem l0o_v4942_rel_from_boundary (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (h : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4934)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7754) (denoteGraphDistributedFaithful pm_goal_1 initPM 7755)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4942)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7782) (denoteGraphDistributedFaithful pm_goal_1 initPM 7783)
      [4096, 4, 64] [2048, 4, 64] := by
  have ms := l10f_reduce1 sm_goal_1 initSM 2
    { rank := 0, op := "OpName.FW_multiref", ins := [4934], outs := [7744, 7748], params := [2] }
    4934 7744 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 4934 [7744, 7748] 2 rfl 7744 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l10f_reduce1 pm_goal_1 initPM 32
    { rank := 0, op := "OpName.FW_multiref", ins := [7754], outs := [15438, 15442], params := [2] }
    7754 15438 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 7754 [15438, 15442] 2 rfl 15438 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l10f_reduce1 pm_goal_1 initPM 33
    { rank := 1, op := "OpName.FW_multiref", ins := [7755], outs := [15446, 15450], params := [2] }
    7755 15446 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 7755 [15446, 15450] 2 rfl 15446 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hw1 := l10f_init_value initSM initPM hInit initGoal_4935
    (by native_decide) 4935 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rs := l10f_rms sm_goal_1 initSM 3 0 7744 4935 4936
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10f_rms pm_goal_1 initPM 34 0 15438 4935 7758
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10f_rms pm_goal_1 initPM 35 1 15446 4935 7759
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have rmsRel : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4936)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7758) (denoteGraphDistributedFaithful pm_goal_1 initPM 7759)
      [4096, 1024] [2048, 1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rs, ms, h.value, ← m0, ← m1, hw1,
        ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega)
          (by rw [m0]; exact h.shard0_shape) (by rw [m1]; exact h.shard1_shape), r0, r1]
    · rw [rs]; exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024 (by rw [ms]; exact h.full_shape)
    · rw [r0]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m0]; exact h.shard0_shape)
    · rw [r1]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m1]; exact h.shard1_shape)
  have vs := l10f_reduce1 sm_goal_1 initSM 4
    { rank := 0, op := "OpName.FW_multiref", ins := [4936], outs := [7753, 7757, 7761], params := [3] }
    4936 7761 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 4936 [7753, 7757, 7761] 3 rfl 7761 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have v0 := l10f_reduce1 pm_goal_1 initPM 36
    { rank := 0, op := "OpName.FW_multiref", ins := [7758], outs := [15292, 12358, 12366], params := [3] }
    7758 12366 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 7758 [15292, 12358, 12366] 3 rfl 12366 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have v1 := l10f_reduce1 pm_goal_1 initPM 37
    { rank := 1, op := "OpName.FW_multiref", ins := [7759], outs := [15294, 12359, 12367], params := [3] }
    7759 12367 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 7759 [15294, 12359, 12367] 3 rfl 12367 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at vs v0 v1
  have hw := l10f_init_value initSM initPM hInit initGoal_4941
    (by native_decide) 4941 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hws := l10f_init_shape initSM initPM hInit initGoal_4941
    (by native_decide) 4941 [4, 64, 1024] rfl rfl (by native_decide)
  have hpw : (denoteGraphDistributedFaithful pm_goal_1 initPM 4941).shape = [4, 64, 1024] := by
    rw [← hw]; exact hws
  have ps := l10f_per_head sm_goal_1 initSM 7 0 7761 4941 4942
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have p0 := l10f_per_head pm_goal_1 initPM 39 0 12366 4941 7782
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have p1 := l10f_per_head pm_goal_1 initPM 42 1 12367 4941 7783
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 12366).shape = [2048, 1024] := by
    rw [v0]; exact rmsRel.shard0_shape
  have hs1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 12367).shape = [2048, 1024] := by
    rw [v1]; exact rmsRel.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [ps, vs, rmsRel.value, ← v0, ← v1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, p0, p1]
  · rw [ps]; exact l11o_per_head_shape _ _ 4096 1024 4 64
      (by rw [vs]; exact rmsRel.full_shape) hws
  · rw [p0]; exact l11o_per_head_shape _ _ 2048 1024 4 64 hs0 hpw
  · rw [p1]; exact l11o_per_head_shape _ _ 2048 1024 4 64 hs1 hpw

/-- L0 ordinary rotary Q/K relations, derived from the preceding MoE boundary. -/
theorem l0o_q4945_k4946_rels_from_boundary (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (h : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4934)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7754) (denoteGraphDistributedFaithful pm_goal_1 initPM 7755)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4945)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7794) (denoteGraphDistributedFaithful pm_goal_1 initPM 7795)
      [4096, 16, 64] [2048, 16, 64] ∧
    Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4946)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7796) (denoteGraphDistributedFaithful pm_goal_1 initPM 7797)
      [4096, 4, 64] [2048, 4, 64] := by
  have ms := l10f_reduce1 sm_goal_1 initSM 2
    { rank := 0, op := "OpName.FW_multiref", ins := [4934], outs := [7744, 7748], params := [2] }
    4934 7744 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 4934 [7744, 7748] 2 rfl 7744 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l10f_reduce1 pm_goal_1 initPM 32
    { rank := 0, op := "OpName.FW_multiref", ins := [7754], outs := [15438, 15442], params := [2] }
    7754 15438 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 7754 [15438, 15442] 2 rfl 15438 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l10f_reduce1 pm_goal_1 initPM 33
    { rank := 1, op := "OpName.FW_multiref", ins := [7755], outs := [15446, 15450], params := [2] }
    7755 15446 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 7755 [15446, 15450] 2 rfl 15446 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hw1 := l10f_init_value initSM initPM hInit initGoal_4935
    (by native_decide) 4935 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rs := l10f_rms sm_goal_1 initSM 3 0 7744 4935 4936
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l10f_rms pm_goal_1 initPM 34 0 15438 4935 7758
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l10f_rms pm_goal_1 initPM 35 1 15446 4935 7759
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have rmsRel : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4936)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7758) (denoteGraphDistributedFaithful pm_goal_1 initPM 7759)
      [4096, 1024] [2048, 1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rs, ms, h.value, ← m0, ← m1, hw1,
        ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega)
          (by rw [m0]; exact h.shard0_shape) (by rw [m1]; exact h.shard1_shape), r0, r1]
    · rw [rs]; exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024 (by rw [ms]; exact h.full_shape)
    · rw [r0]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m0]; exact h.shard0_shape)
    · rw [r1]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m1]; exact h.shard1_shape)

  have qmS := l10f_reduce1 sm_goal_1 initSM 4
    { rank := 0, op := "OpName.FW_multiref", ins := [4936], outs := [7753, 7757, 7761], params := [3] }
    4936 7753 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 4936 [7753, 7757, 7761] 3 rfl 7753 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have qm0 := l10f_reduce1 pm_goal_1 initPM 36
    { rank := 0, op := "OpName.FW_multiref", ins := [7758], outs := [15292, 12358, 12366], params := [3] }
    7758 15292 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 7758 [15292, 12358, 12366] 3 rfl 15292 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have qm1 := l10f_reduce1 pm_goal_1 initPM 37
    { rank := 1, op := "OpName.FW_multiref", ins := [7759], outs := [15294, 12359, 12367], params := [3] }
    7759 15294 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 7759 [15294, 12359, 12367] 3 rfl 15294 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at qmS qm0 qm1
  have qg := l10f_allgather2 pm_goal_1 initPM 40 0 15292 15294 11726
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hwq := l10f_init_value initSM initPM hInit initGoal_4937
    (by native_decide) 4937 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hswq := l10f_init_shape initSM initPM hInit initGoal_4937
    (by native_decide) 4937 [16, 64, 1024] rfl rfl (by native_decide)
  have hpwq : (denoteGraphDistributedFaithful pm_goal_1 initPM 4937).shape = [16, 64, 1024] := by
    rw [← hwq]; exact hswq
  have qs := l10f_per_head sm_goal_1 initSM 5 0 7753 4937 4938
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  -- The shared Q output is written twice in PM; reduce at the final writer (rank 1).
  have qp := l10f_per_head pm_goal_1 initPM 44 1 11726 4937 4938
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hpmR : pm_goal_1.numRanks = 2 := rfl
  rw [hpmR] at qg
  have qeq : denoteGraphDistributedFaithful sm_goal_1 initSM 4938 = denoteGraphDistributedFaithful pm_goal_1 initPM 4938 := by
    rw [qs, qmS, rmsRel.value, ← qm0, ← qm1, ← qg, hwq, ← qp]
  have hqfullS : (denoteGraphDistributedFaithful sm_goal_1 initSM 4938).shape = [4096, 16, 64] := by
    rw [qs]
    exact l11o_per_head_shape _ _ 4096 1024 16 64
      (by rw [qmS]; exact rmsRel.full_shape) hswq
  have hqfullP : (denoteGraphDistributedFaithful pm_goal_1 initPM 4938).shape = [4096, 16, 64] := by
    rw [← qeq]; exact hqfullS
  have cq0 := l10f_chunk pm_goal_1 initPM 45 0 4938 7760
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have cq1 := l10f_chunk pm_goal_1 initPM 46 1 4938 7761
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hpmR] at cq0 cq1
  have hq0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 7760).shape = [2048, 16, 64] := by
    rw [cq0, chunkPrimDimN_shape 0 2 0 _ [4096, 16, 64] hqfullP (by omega)]
    rfl
  have hq1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 7761).shape = [2048, 16, 64] := by
    rw [cq1, chunkPrimDimN_shape 0 2 1 _ [4096, 16, 64] hqfullP (by omega)]
    rfl
  have qRel : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4938)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7760) (denoteGraphDistributedFaithful pm_goal_1 initPM 7761)
      [4096, 16, 64] [2048, 16, 64] := by
    refine ⟨?_, hqfullS, hq0, hq1, by decide⟩
    rw [qeq, cq0, cq1]
    exact (l11o_allGather0_reconstruct_chunks_3d 2048 16 64 (by omega) (by omega) (by omega)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 4938) (by simpa using hqfullP)).symm

  have kmS := l10f_reduce1 sm_goal_1 initSM 4
    { rank := 0, op := "OpName.FW_multiref", ins := [4936], outs := [7753, 7757, 7761], params := [3] }
    4936 7757 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at sm_goal_1 st 0 4936 [7753, 7757, 7761] 3 rfl 7757 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have km0 := l10f_reduce1 pm_goal_1 initPM 36
    { rank := 0, op := "OpName.FW_multiref", ins := [7758], outs := [15292, 12358, 12366], params := [3] }
    7758 12358 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 0 7758 [15292, 12358, 12366] 3 rfl 12358 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have km1 := l10f_reduce1 pm_goal_1 initPM 37
    { rank := 1, op := "OpName.FW_multiref", ins := [7759], outs := [15294, 12359, 12367], params := [3] }
    7759 12359 id (by native_decide) (by native_decide) (by decide)
    (fun st => l10f_apply_multiref_at pm_goal_1 st 1 7759 [15294, 12359, 12367] 3 rfl 12359 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at kmS km0 km1
  have hwk := l10f_init_value initSM initPM hInit initGoal_4939
    (by native_decide) 4939 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hswk := l10f_init_shape initSM initPM hInit initGoal_4939
    (by native_decide) 4939 [4, 64, 1024] rfl rfl (by native_decide)
  have hpwk : (denoteGraphDistributedFaithful pm_goal_1 initPM 4939).shape = [4, 64, 1024] := by
    rw [← hwk]; exact hswk
  have ks := l10f_per_head sm_goal_1 initSM 6 0 7757 4939 4940
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have kp0 := l10f_per_head pm_goal_1 initPM 38 0 12358 4939 7772
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have kp1 := l10f_per_head pm_goal_1 initPM 41 1 12359 4939 7773
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have kRel : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 4940)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7772) (denoteGraphDistributedFaithful pm_goal_1 initPM 7773)
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
  have hpos := l10f_init_value initSM initPM hInit initGoal_4943
    (by native_decide) 4943 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hspos := l10f_init_shape initSM initPM hInit initGoal_4943
    (by native_decide) 4943 [4096] rfl rfl (by native_decide)
  have pc0 := l10f_chunk pm_goal_1 initPM 1 0 4943 7792
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have pc1 := l10f_chunk pm_goal_1 initPM 15 1 4943 7793
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hpmR] at pc0 pc1
  have qS := l10f_reduce4 sm_goal_1 initSM 8
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 4943, 4938, 4940],
      outs := [4945, 4946], params := [16, 4] }
    4944 4943 4938 4940 4945
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).1)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_fst_out sm_goal_1 st 0 16 4 4944 4943 4938 4940 4945 4946)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have kS := l10f_reduce4 sm_goal_1 initSM 8
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 4943, 4938, 4940],
      outs := [4945, 4946], params := [16, 4] }
    4944 4943 4938 4940 4946
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).2)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring sm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_snd_out sm_goal_1 st 0 16 4 4944 4943 4938 4940 4945 4946 (by decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have q0 := l10f_reduce4 pm_goal_1 initPM 47
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 7792, 7760, 7772],
      outs := [7794, 7796], params := [16, 4] }
    4944 7792 7760 7772 7794
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).1)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_fst_out pm_goal_1 st 0 16 4 4944 7792 7760 7772 7794 7796)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have k0 := l10f_reduce4 pm_goal_1 initPM 47
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 7792, 7760, 7772],
      outs := [7794, 7796], params := [16, 4] }
    4944 7792 7760 7772 7796
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).2)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_snd_out pm_goal_1 st 0 16 4 4944 7792 7760 7772 7794 7796 (by decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have q1 := l10f_reduce4 pm_goal_1 initPM 48
    { rank := 1, op := "OpName.FW_rotary_embedding", ins := [4944, 7793, 7761, 7773],
      outs := [7795, 7797], params := [16, 4] }
    4944 7793 7761 7773 7795
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).1)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_fst_out pm_goal_1 st 1 16 4 4944 7793 7761 7773 7795 7797)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have k1 := l10f_reduce4 pm_goal_1 initPM 48
    { rank := 1, op := "OpName.FW_rotary_embedding", ins := [4944, 7793, 7761, 7773],
      outs := [7795, 7797], params := [16, 4] }
    4944 7793 7761 7773 7797
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).2)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide) (by decide)]
      unfold applyNodeDistributed
      rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring pm_goal_1 st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_snd_out pm_goal_1 st 1 16 4 4944 7793 7761 7773 7795 7797 (by decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have qval : denoteGraphDistributedFaithful sm_goal_1 initSM 4945 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributedFaithful pm_goal_1 initPM 7794, denoteGraphDistributedFaithful pm_goal_1 initPM 7795] := by
    rw [qS]
    simp only [fw_rotary_embedding]
    rw [qRel.value, l11o_rotary_allGather0_1d (denoteGraphDistributedFaithful sm_goal_1 initSM 4944)
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4943) (denoteGraphDistributedFaithful pm_goal_1 initPM 7760)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7761) 2048 16 64 (by omega) (by omega) (by omega)
      hspos qRel.shard0_shape qRel.shard1_shape, hcache, hpos, ← pc0, ← pc1, q0, q1]
    simp only [fw_rotary_embedding]
  have kval : denoteGraphDistributedFaithful sm_goal_1 initSM 4946 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributedFaithful pm_goal_1 initPM 7796, denoteGraphDistributedFaithful pm_goal_1 initPM 7797] := by
    rw [kS]
    simp only [fw_rotary_embedding]
    rw [kRel.value, l11o_rotary_allGather0_1d (denoteGraphDistributedFaithful sm_goal_1 initSM 4944)
      (denoteGraphDistributedFaithful sm_goal_1 initSM 4943) (denoteGraphDistributedFaithful pm_goal_1 initPM 7772)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 7773) 2048 4 64 (by omega) (by omega) (by omega)
      hspos kRel.shard0_shape kRel.shard1_shape, hcache, hpos, ← pc0, ← pc1, k0, k1]
    simp only [fw_rotary_embedding]
  have qs0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 7794).shape = [2048, 16, 64] := by
    rw [q0]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 qRel.shard0_shape
  have qs1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 7795).shape = [2048, 16, 64] := by
    rw [q1]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 qRel.shard1_shape
  have ks0 : (denoteGraphDistributedFaithful pm_goal_1 initPM 7796).shape = [2048, 4, 64] := by
    rw [k0]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 kRel.shard0_shape
  have ks1 : (denoteGraphDistributedFaithful pm_goal_1 initPM 7797).shape = [2048, 4, 64] := by
    rw [k1]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 kRel.shard1_shape
  refine ⟨⟨qval, ?_, qs0, qs1, by decide⟩, ⟨kval, ?_, ks0, ks1, by decide⟩⟩
  · rw [qval, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [qs0])]
    rfl
  · rw [kval, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [ks0])]
    rfl

end TrainVerify.Denote.GeneratedPatterns
