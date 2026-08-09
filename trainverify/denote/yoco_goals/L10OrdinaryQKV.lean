import denote.yoco_goals.L11OrdinaryQKV

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- L10 ordinary V relation, derived from the preceding MoE boundary and init weight. -/
theorem l10o_v5493_rel_from_boundary (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (h : Gather2Rel (denoteGraphDistributed sm initSM 5485)
      (denoteGraphDistributed pm initPM 9394) (denoteGraphDistributed pm initPM 9395)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributed sm initSM 5493)
      (denoteGraphDistributed pm initPM 9422) (denoteGraphDistributed pm initPM 9423)
      [4096, 4, 64] [2048, 4, 64] := by
  have ms := l11o_reduce1 sm initSM 392
    { rank := 0, op := "OpName.FW_multiref", ins := [5485], outs := [8264, 8268], params := [2] }
    5485 8264 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at sm st 0 5485 [8264, 8268] 2 rfl 8264 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l11o_reduce1 pm initPM 872
    { rank := 0, op := "OpName.FW_multiref", ins := [9394], outs := [15758, 15762], params := [2] }
    9394 15758 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm st 0 9394 [15758, 15762] 2 rfl 15758 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l11o_reduce1 pm initPM 873
    { rank := 1, op := "OpName.FW_multiref", ins := [9395], outs := [15766, 15770], params := [2] }
    9395 15766 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm st 1 9395 [15766, 15770] 2 rfl 15766 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hw1 := l11o_init_value initSM initPM hInit initGoal_5486
    (by native_decide) 5486 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rs := l11o_rms sm initSM 393 0 8264 5486 5487
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l11o_rms pm initPM 874 0 15758 5486 9398
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l11o_rms pm initPM 875 1 15766 5486 9399
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have rmsRel : Gather2Rel (denoteGraphDistributed sm initSM 5487)
      (denoteGraphDistributed pm initPM 9398) (denoteGraphDistributed pm initPM 9399)
      [4096, 1024] [2048, 1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rs, ms, h.value, ← m0, ← m1, hw1,
        ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega)
          (by rw [m0]; exact h.shard0_shape) (by rw [m1]; exact h.shard1_shape), r0, r1]
    · rw [rs]; exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024 (by rw [ms]; exact h.full_shape)
    · rw [r0]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m0]; exact h.shard0_shape)
    · rw [r1]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m1]; exact h.shard1_shape)
  have vs := l11o_reduce1 sm initSM 394
    { rank := 0, op := "OpName.FW_multiref", ins := [5487], outs := [8273, 8277, 8281], params := [3] }
    5487 8281 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at sm st 0 5487 [8273, 8277, 8281] 3 rfl 8281 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have v0 := l11o_reduce1 pm initPM 876
    { rank := 0, op := "OpName.FW_multiref", ins := [9398], outs := [15372, 13618, 13626], params := [3] }
    9398 13626 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm st 0 9398 [15372, 13618, 13626] 3 rfl 13626 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have v1 := l11o_reduce1 pm initPM 877
    { rank := 1, op := "OpName.FW_multiref", ins := [9399], outs := [15374, 13619, 13627], params := [3] }
    9399 13627 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm st 1 9399 [15374, 13619, 13627] 3 rfl 13627 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at vs v0 v1
  have hw := l11o_init_value initSM initPM hInit initGoal_5492
    (by native_decide) 5492 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hws := l11o_init_shape initSM initPM hInit initGoal_5492
    (by native_decide) 5492 [4, 64, 1024] rfl rfl (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5492).shape = [4, 64, 1024] := by
    rw [← hw]; exact hws
  have ps := l11o_per_head sm initSM 397 0 8281 5492 5493
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have p0 := l11o_per_head pm initPM 879 0 13626 5492 9422
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have p1 := l11o_per_head pm initPM 882 1 13627 5492 9423
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 13626).shape = [2048, 1024] := by
    rw [v0]; exact rmsRel.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 13627).shape = [2048, 1024] := by
    rw [v1]; exact rmsRel.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [ps, vs, rmsRel.value, ← v0, ← v1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, p0, p1]
  · rw [ps]; exact l11o_per_head_shape _ _ 4096 1024 4 64
      (by rw [vs]; exact rmsRel.full_shape) hws
  · rw [p0]; exact l11o_per_head_shape _ _ 2048 1024 4 64 hs0 hpw
  · rw [p1]; exact l11o_per_head_shape _ _ 2048 1024 4 64 hs1 hpw

/-- L10 ordinary rotary Q/K relations, derived from the preceding MoE boundary. -/
theorem l10o_q5495_k5496_rels_from_boundary (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (h : Gather2Rel (denoteGraphDistributed sm initSM 5485)
      (denoteGraphDistributed pm initPM 9394) (denoteGraphDistributed pm initPM 9395)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributed sm initSM 5495)
      (denoteGraphDistributed pm initPM 9434) (denoteGraphDistributed pm initPM 9435)
      [4096, 16, 64] [2048, 16, 64] ∧
    Gather2Rel (denoteGraphDistributed sm initSM 5496)
      (denoteGraphDistributed pm initPM 9436) (denoteGraphDistributed pm initPM 9437)
      [4096, 4, 64] [2048, 4, 64] := by
  have ms := l11o_reduce1 sm initSM 392
    { rank := 0, op := "OpName.FW_multiref", ins := [5485], outs := [8264, 8268], params := [2] }
    5485 8264 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at sm st 0 5485 [8264, 8268] 2 rfl 8264 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l11o_reduce1 pm initPM 872
    { rank := 0, op := "OpName.FW_multiref", ins := [9394], outs := [15758, 15762], params := [2] }
    9394 15758 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm st 0 9394 [15758, 15762] 2 rfl 15758 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l11o_reduce1 pm initPM 873
    { rank := 1, op := "OpName.FW_multiref", ins := [9395], outs := [15766, 15770], params := [2] }
    9395 15766 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm st 1 9395 [15766, 15770] 2 rfl 15766 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hw1 := l11o_init_value initSM initPM hInit initGoal_5486
    (by native_decide) 5486 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rs := l11o_rms sm initSM 393 0 8264 5486 5487
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l11o_rms pm initPM 874 0 15758 5486 9398
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l11o_rms pm initPM 875 1 15766 5486 9399
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have rmsRel : Gather2Rel (denoteGraphDistributed sm initSM 5487)
      (denoteGraphDistributed pm initPM 9398) (denoteGraphDistributed pm initPM 9399)
      [4096, 1024] [2048, 1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rs, ms, h.value, ← m0, ← m1, hw1,
        ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega)
          (by rw [m0]; exact h.shard0_shape) (by rw [m1]; exact h.shard1_shape), r0, r1]
    · rw [rs]; exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024 (by rw [ms]; exact h.full_shape)
    · rw [r0]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m0]; exact h.shard0_shape)
    · rw [r1]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m1]; exact h.shard1_shape)

  have qmS := l11o_reduce1 sm initSM 394
    { rank := 0, op := "OpName.FW_multiref", ins := [5487], outs := [8273, 8277, 8281], params := [3] }
    5487 8273 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at sm st 0 5487 [8273, 8277, 8281] 3 rfl 8273 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have qm0 := l11o_reduce1 pm initPM 876
    { rank := 0, op := "OpName.FW_multiref", ins := [9398], outs := [15372, 13618, 13626], params := [3] }
    9398 15372 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm st 0 9398 [15372, 13618, 13626] 3 rfl 15372 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have qm1 := l11o_reduce1 pm initPM 877
    { rank := 1, op := "OpName.FW_multiref", ins := [9399], outs := [15374, 13619, 13627], params := [3] }
    9399 15374 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm st 1 9399 [15374, 13619, 13627] 3 rfl 15374 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at qmS qm0 qm1
  have qg := l11o_allgather2 pm initPM 880 0 15372 15374 12046
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hwq := l11o_init_value initSM initPM hInit initGoal_5488
    (by native_decide) 5488 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hswq := l11o_init_shape initSM initPM hInit initGoal_5488
    (by native_decide) 5488 [16, 64, 1024] rfl rfl (by native_decide)
  have hpwq : (denoteGraphDistributed pm initPM 5488).shape = [16, 64, 1024] := by
    rw [← hwq]; exact hswq
  have qs := l11o_per_head sm initSM 395 0 8273 5488 5489
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  -- The shared Q output is written twice in PM; reduce at the final writer (rank 1).
  have qp := l11o_per_head pm initPM 884 1 12046 5488 5489
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hpmR : pm.numRanks = 2 := rfl
  rw [hpmR] at qg
  have qeq : denoteGraphDistributed sm initSM 5489 = denoteGraphDistributed pm initPM 5489 := by
    rw [qs, qmS, rmsRel.value, ← qm0, ← qm1, ← qg, hwq, ← qp]
  have hqfullS : (denoteGraphDistributed sm initSM 5489).shape = [4096, 16, 64] := by
    rw [qs]
    exact l11o_per_head_shape _ _ 4096 1024 16 64
      (by rw [qmS]; exact rmsRel.full_shape) hswq
  have hqfullP : (denoteGraphDistributed pm initPM 5489).shape = [4096, 16, 64] := by
    rw [← qeq]; exact hqfullS
  have cq0 := l11o_chunk pm initPM 885 0 5489 9400
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have cq1 := l11o_chunk pm initPM 886 1 5489 9401
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hpmR] at cq0 cq1
  have hq0 : (denoteGraphDistributed pm initPM 9400).shape = [2048, 16, 64] := by
    rw [cq0, chunkPrimDimN_shape 0 2 0 _ [4096, 16, 64] hqfullP (by omega)]
    rfl
  have hq1 : (denoteGraphDistributed pm initPM 9401).shape = [2048, 16, 64] := by
    rw [cq1, chunkPrimDimN_shape 0 2 1 _ [4096, 16, 64] hqfullP (by omega)]
    rfl
  have qRel : Gather2Rel (denoteGraphDistributed sm initSM 5489)
      (denoteGraphDistributed pm initPM 9400) (denoteGraphDistributed pm initPM 9401)
      [4096, 16, 64] [2048, 16, 64] := by
    refine ⟨?_, hqfullS, hq0, hq1, by decide⟩
    rw [qeq, cq0, cq1]
    exact (l11o_allGather0_reconstruct_chunks_3d 2048 16 64 (by omega) (by omega) (by omega)
      (denoteGraphDistributed pm initPM 5489) (by simpa using hqfullP)).symm

  have kmS := l11o_reduce1 sm initSM 394
    { rank := 0, op := "OpName.FW_multiref", ins := [5487], outs := [8273, 8277, 8281], params := [3] }
    5487 8277 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at sm st 0 5487 [8273, 8277, 8281] 3 rfl 8277 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have km0 := l11o_reduce1 pm initPM 876
    { rank := 0, op := "OpName.FW_multiref", ins := [9398], outs := [15372, 13618, 13626], params := [3] }
    9398 13618 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm st 0 9398 [15372, 13618, 13626] 3 rfl 13618 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have km1 := l11o_reduce1 pm initPM 877
    { rank := 1, op := "OpName.FW_multiref", ins := [9399], outs := [15374, 13619, 13627], params := [3] }
    9399 13619 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm st 1 9399 [15374, 13619, 13627] 3 rfl 13619 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at kmS km0 km1
  have hwk := l11o_init_value initSM initPM hInit initGoal_5490
    (by native_decide) 5490 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hswk := l11o_init_shape initSM initPM hInit initGoal_5490
    (by native_decide) 5490 [4, 64, 1024] rfl rfl (by native_decide)
  have hpwk : (denoteGraphDistributed pm initPM 5490).shape = [4, 64, 1024] := by
    rw [← hwk]; exact hswk
  have ks := l11o_per_head sm initSM 396 0 8277 5490 5491
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have kp0 := l11o_per_head pm initPM 878 0 13618 5490 9412
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have kp1 := l11o_per_head pm initPM 881 1 13619 5490 9413
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have kRel : Gather2Rel (denoteGraphDistributed sm initSM 5491)
      (denoteGraphDistributed pm initPM 9412) (denoteGraphDistributed pm initPM 9413)
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

  have hcache := l11o_init_value initSM initPM hInit initGoal_4944
    (by native_decide) 4944 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hpos := l11o_init_value initSM initPM hInit initGoal_5494
    (by native_decide) 5494 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hspos := l11o_init_shape initSM initPM hInit initGoal_5494
    (by native_decide) 5494 [4096] rfl rfl (by native_decide)
  have pc0 := l11o_chunk pm initPM 11 0 5494 9432
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have pc1 := l11o_chunk pm initPM 25 1 5494 9433
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hpmR] at pc0 pc1
  have qS := l11o_reduce4 sm initSM 398
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 5494, 5489, 5491],
      outs := [5495, 5496], params := [16, 4] }
    4944 5494 5489 5491 5495
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).1)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeRingAttn_eq_applyNode_of_not_ring sm st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_fst_out sm st 0 16 4 4944 5494 5489 5491 5495 5496)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have kS := l11o_reduce4 sm initSM 398
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 5494, 5489, 5491],
      outs := [5495, 5496], params := [16, 4] }
    4944 5494 5489 5491 5496
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).2)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeRingAttn_eq_applyNode_of_not_ring sm st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_snd_out sm st 0 16 4 4944 5494 5489 5491 5495 5496 (by decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have q0 := l11o_reduce4 pm initPM 887
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 9432, 9400, 9412],
      outs := [9434, 9436], params := [16, 4] }
    4944 9432 9400 9412 9434
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).1)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_fst_out pm st 0 16 4 4944 9432 9400 9412 9434 9436)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have k0 := l11o_reduce4 pm initPM 887
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 9432, 9400, 9412],
      outs := [9434, 9436], params := [16, 4] }
    4944 9432 9400 9412 9436
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).2)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_snd_out pm st 0 16 4 4944 9432 9400 9412 9434 9436 (by decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have q1 := l11o_reduce4 pm initPM 888
    { rank := 1, op := "OpName.FW_rotary_embedding", ins := [4944, 9433, 9401, 9413],
      outs := [9435, 9437], params := [16, 4] }
    4944 9433 9401 9413 9435
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).1)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_fst_out pm st 1 16 4 4944 9433 9401 9413 9435 9437)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have k1 := l11o_reduce4 pm initPM 888
    { rank := 1, op := "OpName.FW_rotary_embedding", ins := [4944, 9433, 9401, 9413],
      outs := [9435, 9437], params := [16, 4] }
    4944 9433 9401 9413 9437
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).2)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_snd_out pm st 1 16 4 4944 9433 9401 9413 9435 9437 (by decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have qval : denoteGraphDistributed sm initSM 5495 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 9434, denoteGraphDistributed pm initPM 9435] := by
    rw [qS]
    simp only [fw_rotary_embedding]
    rw [qRel.value, l11o_rotary_allGather0_1d (denoteGraphDistributed sm initSM 4944)
      (denoteGraphDistributed sm initSM 5494) (denoteGraphDistributed pm initPM 9400)
      (denoteGraphDistributed pm initPM 9401) 2048 16 64 (by omega) (by omega) (by omega)
      hspos qRel.shard0_shape qRel.shard1_shape, hcache, hpos, ← pc0, ← pc1, q0, q1]
    simp only [fw_rotary_embedding]
  have kval : denoteGraphDistributed sm initSM 5496 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 9436, denoteGraphDistributed pm initPM 9437] := by
    rw [kS]
    simp only [fw_rotary_embedding]
    rw [kRel.value, l11o_rotary_allGather0_1d (denoteGraphDistributed sm initSM 4944)
      (denoteGraphDistributed sm initSM 5494) (denoteGraphDistributed pm initPM 9412)
      (denoteGraphDistributed pm initPM 9413) 2048 4 64 (by omega) (by omega) (by omega)
      hspos kRel.shard0_shape kRel.shard1_shape, hcache, hpos, ← pc0, ← pc1, k0, k1]
    simp only [fw_rotary_embedding]
  have qs0 : (denoteGraphDistributed pm initPM 9434).shape = [2048, 16, 64] := by
    rw [q0]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 qRel.shard0_shape
  have qs1 : (denoteGraphDistributed pm initPM 9435).shape = [2048, 16, 64] := by
    rw [q1]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 qRel.shard1_shape
  have ks0 : (denoteGraphDistributed pm initPM 9436).shape = [2048, 4, 64] := by
    rw [k0]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 kRel.shard0_shape
  have ks1 : (denoteGraphDistributed pm initPM 9437).shape = [2048, 4, 64] := by
    rw [k1]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 kRel.shard1_shape
  refine ⟨⟨qval, ?_, qs0, qs1, by decide⟩, ⟨kval, ?_, ks0, ks1, by decide⟩⟩
  · rw [qval, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [qs0])]
    rfl
  · rw [kval, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [ks0])]
    rfl

end TrainVerify.Denote.GeneratedPatterns
