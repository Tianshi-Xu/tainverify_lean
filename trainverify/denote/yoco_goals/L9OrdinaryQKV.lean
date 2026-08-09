import denote.yoco_goals.L11OrdinaryQKV

set_option linter.style.longLine false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- L9 ordinary V relation, derived from the preceding MoE boundary and init weight. -/
theorem l9o_v5438_rel_from_boundary (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (h : Gather2Rel (denoteGraphDistributed sm initSM 5430)
      (denoteGraphDistributed pm initPM 9230) (denoteGraphDistributed pm initPM 9231)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributed sm initSM 5438)
      (denoteGraphDistributed pm initPM 9258) (denoteGraphDistributed pm initPM 9259)
      [4096, 4, 64] [2048, 4, 64] := by
  have ms := l11o_reduce1 sm initSM 353
    { rank := 0, op := "OpName.FW_multiref", ins := [5430], outs := [8212, 8216], params := [2] }
    5430 8212 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at sm st 0 5430 [8212, 8216] 2 rfl 8212 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l11o_reduce1 pm initPM 788
    { rank := 0, op := "OpName.FW_multiref", ins := [9230], outs := [15726, 15730], params := [2] }
    9230 15726 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm st 0 9230 [15726, 15730] 2 rfl 15726 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l11o_reduce1 pm initPM 789
    { rank := 1, op := "OpName.FW_multiref", ins := [9231], outs := [15734, 15738], params := [2] }
    9231 15734 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm st 1 9231 [15734, 15738] 2 rfl 15734 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hw1 := l11o_init_value initSM initPM hInit initGoal_5431
    (by native_decide) 5431 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rs := l11o_rms sm initSM 354 0 8212 5431 5432
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l11o_rms pm initPM 790 0 15726 5431 9234
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l11o_rms pm initPM 791 1 15734 5431 9235
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have rmsRel : Gather2Rel (denoteGraphDistributed sm initSM 5432)
      (denoteGraphDistributed pm initPM 9234) (denoteGraphDistributed pm initPM 9235)
      [4096, 1024] [2048, 1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rs, ms, h.value, ← m0, ← m1, hw1,
        ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega)
          (by rw [m0]; exact h.shard0_shape) (by rw [m1]; exact h.shard1_shape), r0, r1]
    · rw [rs]; exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024 (by rw [ms]; exact h.full_shape)
    · rw [r0]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m0]; exact h.shard0_shape)
    · rw [r1]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m1]; exact h.shard1_shape)
  have vs := l11o_reduce1 sm initSM 355
    { rank := 0, op := "OpName.FW_multiref", ins := [5432], outs := [8221, 8225, 8229], params := [3] }
    5432 8229 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at sm st 0 5432 [8221, 8225, 8229] 3 rfl 8229 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have v0 := l11o_reduce1 pm initPM 792
    { rank := 0, op := "OpName.FW_multiref", ins := [9234], outs := [15364, 13492, 13500], params := [3] }
    9234 13500 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm st 0 9234 [15364, 13492, 13500] 3 rfl 13500 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have v1 := l11o_reduce1 pm initPM 793
    { rank := 1, op := "OpName.FW_multiref", ins := [9235], outs := [15366, 13493, 13501], params := [3] }
    9235 13501 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm st 1 9235 [15366, 13493, 13501] 3 rfl 13501 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at vs v0 v1
  have hw := l11o_init_value initSM initPM hInit initGoal_5437
    (by native_decide) 5437 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hws := l11o_init_shape initSM initPM hInit initGoal_5437
    (by native_decide) 5437 [4, 64, 1024] rfl rfl (by native_decide)
  have hpw : (denoteGraphDistributed pm initPM 5437).shape = [4, 64, 1024] := by
    rw [← hw]; exact hws
  have ps := l11o_per_head sm initSM 358 0 8229 5437 5438
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have p0 := l11o_per_head pm initPM 795 0 13500 5437 9258
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have p1 := l11o_per_head pm initPM 798 1 13501 5437 9259
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hs0 : (denoteGraphDistributed pm initPM 13500).shape = [2048, 1024] := by
    rw [v0]; exact rmsRel.shard0_shape
  have hs1 : (denoteGraphDistributed pm initPM 13501).shape = [2048, 1024] := by
    rw [v1]; exact rmsRel.shard1_shape
  refine ⟨?_, ?_, ?_, ?_, by decide⟩
  · rw [ps, vs, rmsRel.value, ← v0, ← v1, hw,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ _ 2048 1024 4 64
        (by omega) (by omega) (by omega) (by omega) hs0 hs1 hpw, p0, p1]
  · rw [ps]; exact l11o_per_head_shape _ _ 4096 1024 4 64
      (by rw [vs]; exact rmsRel.full_shape) hws
  · rw [p0]; exact l11o_per_head_shape _ _ 2048 1024 4 64 hs0 hpw
  · rw [p1]; exact l11o_per_head_shape _ _ 2048 1024 4 64 hs1 hpw

/-- L9 ordinary rotary Q/K relations, derived from the preceding MoE boundary. -/
theorem l9o_q5440_k5441_rels_from_boundary (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (h : Gather2Rel (denoteGraphDistributed sm initSM 5430)
      (denoteGraphDistributed pm initPM 9230) (denoteGraphDistributed pm initPM 9231)
      [4096, 1024] [2048, 1024]) :
    Gather2Rel (denoteGraphDistributed sm initSM 5440)
      (denoteGraphDistributed pm initPM 9270) (denoteGraphDistributed pm initPM 9271)
      [4096, 16, 64] [2048, 16, 64] ∧
    Gather2Rel (denoteGraphDistributed sm initSM 5441)
      (denoteGraphDistributed pm initPM 9272) (denoteGraphDistributed pm initPM 9273)
      [4096, 4, 64] [2048, 4, 64] := by
  have ms := l11o_reduce1 sm initSM 353
    { rank := 0, op := "OpName.FW_multiref", ins := [5430], outs := [8212, 8216], params := [2] }
    5430 8212 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at sm st 0 5430 [8212, 8216] 2 rfl 8212 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m0 := l11o_reduce1 pm initPM 788
    { rank := 0, op := "OpName.FW_multiref", ins := [9230], outs := [15726, 15730], params := [2] }
    9230 15726 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm st 0 9230 [15726, 15730] 2 rfl 15726 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have m1 := l11o_reduce1 pm initPM 789
    { rank := 1, op := "OpName.FW_multiref", ins := [9231], outs := [15734, 15738], params := [2] }
    9231 15734 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm st 1 9231 [15734, 15738] 2 rfl 15734 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at ms m0 m1
  have hw1 := l11o_init_value initSM initPM hInit initGoal_5431
    (by native_decide) 5431 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have rs := l11o_rms sm initSM 354 0 8212 5431 5432
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r0 := l11o_rms pm initPM 790 0 15726 5431 9234
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have r1 := l11o_rms pm initPM 791 1 15734 5431 9235
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have rmsRel : Gather2Rel (denoteGraphDistributed sm initSM 5432)
      (denoteGraphDistributed pm initPM 9234) (denoteGraphDistributed pm initPM 9235)
      [4096, 1024] [2048, 1024] := by
    refine ⟨?_, ?_, ?_, ?_, by decide⟩
    · rw [rs, ms, h.value, ← m0, ← m1, hw1,
        ordinary_fw_rms_norm_allGather0_commute_2 _ _ _ 2048 1024 (by omega) (by omega)
          (by rw [m0]; exact h.shard0_shape) (by rw [m1]; exact h.shard1_shape), r0, r1]
    · rw [rs]; exact ordinary_fw_rms_norm_shape2 _ _ 4096 1024 (by rw [ms]; exact h.full_shape)
    · rw [r0]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m0]; exact h.shard0_shape)
    · rw [r1]; exact ordinary_fw_rms_norm_shape2 _ _ 2048 1024 (by rw [m1]; exact h.shard1_shape)

  have qmS := l11o_reduce1 sm initSM 355
    { rank := 0, op := "OpName.FW_multiref", ins := [5432], outs := [8221, 8225, 8229], params := [3] }
    5432 8221 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at sm st 0 5432 [8221, 8225, 8229] 3 rfl 8221 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have qm0 := l11o_reduce1 pm initPM 792
    { rank := 0, op := "OpName.FW_multiref", ins := [9234], outs := [15364, 13492, 13500], params := [3] }
    9234 15364 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm st 0 9234 [15364, 13492, 13500] 3 rfl 15364 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have qm1 := l11o_reduce1 pm initPM 793
    { rank := 1, op := "OpName.FW_multiref", ins := [9235], outs := [15366, 13493, 13501], params := [3] }
    9235 15366 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm st 1 9235 [15366, 13493, 13501] 3 rfl 15366 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at qmS qm0 qm1
  have qg := l11o_allgather2 pm initPM 796 0 15364 15366 12014
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hwq := l11o_init_value initSM initPM hInit initGoal_5433
    (by native_decide) 5433 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hswq := l11o_init_shape initSM initPM hInit initGoal_5433
    (by native_decide) 5433 [16, 64, 1024] rfl rfl (by native_decide)
  have hpwq : (denoteGraphDistributed pm initPM 5433).shape = [16, 64, 1024] := by
    rw [← hwq]; exact hswq
  have qs := l11o_per_head sm initSM 356 0 8221 5433 5434
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  -- The shared Q output is written twice in PM; reduce at the final writer (rank 1).
  have qp := l11o_per_head pm initPM 800 1 12014 5433 5434
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have hpmR : pm.numRanks = 2 := rfl
  rw [hpmR] at qg
  have qeq : denoteGraphDistributed sm initSM 5434 = denoteGraphDistributed pm initPM 5434 := by
    rw [qs, qmS, rmsRel.value, ← qm0, ← qm1, ← qg, hwq, ← qp]
  have hqfullS : (denoteGraphDistributed sm initSM 5434).shape = [4096, 16, 64] := by
    rw [qs]
    exact l11o_per_head_shape _ _ 4096 1024 16 64
      (by rw [qmS]; exact rmsRel.full_shape) hswq
  have hqfullP : (denoteGraphDistributed pm initPM 5434).shape = [4096, 16, 64] := by
    rw [← qeq]; exact hqfullS
  have cq0 := l11o_chunk pm initPM 801 0 5434 9236
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have cq1 := l11o_chunk pm initPM 802 1 5434 9237
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hpmR] at cq0 cq1
  have hq0 : (denoteGraphDistributed pm initPM 9236).shape = [2048, 16, 64] := by
    rw [cq0, chunkPrimDimN_shape 0 2 0 _ [4096, 16, 64] hqfullP (by omega)]
    rfl
  have hq1 : (denoteGraphDistributed pm initPM 9237).shape = [2048, 16, 64] := by
    rw [cq1, chunkPrimDimN_shape 0 2 1 _ [4096, 16, 64] hqfullP (by omega)]
    rfl
  have qRel : Gather2Rel (denoteGraphDistributed sm initSM 5434)
      (denoteGraphDistributed pm initPM 9236) (denoteGraphDistributed pm initPM 9237)
      [4096, 16, 64] [2048, 16, 64] := by
    refine ⟨?_, hqfullS, hq0, hq1, by decide⟩
    rw [qeq, cq0, cq1]
    exact (l11o_allGather0_reconstruct_chunks_3d 2048 16 64 (by omega) (by omega) (by omega)
      (denoteGraphDistributed pm initPM 5434) (by simpa using hqfullP)).symm

  have kmS := l11o_reduce1 sm initSM 355
    { rank := 0, op := "OpName.FW_multiref", ins := [5432], outs := [8221, 8225, 8229], params := [3] }
    5432 8225 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at sm st 0 5432 [8221, 8225, 8229] 3 rfl 8225 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have km0 := l11o_reduce1 pm initPM 792
    { rank := 0, op := "OpName.FW_multiref", ins := [9234], outs := [15364, 13492, 13500], params := [3] }
    9234 13492 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm st 0 9234 [15364, 13492, 13500] 3 rfl 13492 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have km1 := l11o_reduce1 pm initPM 793
    { rank := 1, op := "OpName.FW_multiref", ins := [9235], outs := [15366, 13493, 13501], params := [3] }
    9235 13493 id (by native_decide) (by native_decide) (by decide)
    (fun st => l11o_apply_multiref_at pm st 1 9235 [15366, 13493, 13501] 3 rfl 13493 (by decide))
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  simp only [id_eq] at kmS km0 km1
  have hwk := l11o_init_value initSM initPM hInit initGoal_5435
    (by native_decide) 5435 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hswk := l11o_init_shape initSM initPM hInit initGoal_5435
    (by native_decide) 5435 [4, 64, 1024] rfl rfl (by native_decide)
  have hpwk : (denoteGraphDistributed pm initPM 5435).shape = [4, 64, 1024] := by
    rw [← hwk]; exact hswk
  have ks := l11o_per_head sm initSM 357 0 8225 5435 5436
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have kp0 := l11o_per_head pm initPM 794 0 13492 5435 9248
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have kp1 := l11o_per_head pm initPM 797 1 13493 5435 9249
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  have kRel : Gather2Rel (denoteGraphDistributed sm initSM 5436)
      (denoteGraphDistributed pm initPM 9248) (denoteGraphDistributed pm initPM 9249)
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
  have hpos := l11o_init_value initSM initPM hInit initGoal_5439
    (by native_decide) 5439 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hspos := l11o_init_shape initSM initPM hInit initGoal_5439
    (by native_decide) 5439 [4096] rfl rfl (by native_decide)
  have pc0 := l11o_chunk pm initPM 10 0 5439 9268
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  have pc1 := l11o_chunk pm initPM 24 1 5439 9269
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  rw [hpmR] at pc0 pc1
  have qS := l11o_reduce4 sm initSM 359
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 5439, 5434, 5436],
      outs := [5440, 5441], params := [16, 4] }
    4944 5439 5434 5436 5440
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).1)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeRingAttn_eq_applyNode_of_not_ring sm st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_fst_out sm st 0 16 4 4944 5439 5434 5436 5440 5441)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have kS := l11o_reduce4 sm initSM 359
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 5439, 5434, 5436],
      outs := [5440, 5441], params := [16, 4] }
    4944 5439 5434 5436 5441
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).2)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeRingAttn_eq_applyNode_of_not_ring sm st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_snd_out sm st 0 16 4 4944 5439 5434 5436 5440 5441 (by decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have q0 := l11o_reduce4 pm initPM 803
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 9268, 9236, 9248],
      outs := [9270, 9272], params := [16, 4] }
    4944 9268 9236 9248 9270
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).1)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_fst_out pm st 0 16 4 4944 9268 9236 9248 9270 9272)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have k0 := l11o_reduce4 pm initPM 803
    { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4944, 9268, 9236, 9248],
      outs := [9270, 9272], params := [16, 4] }
    4944 9268 9236 9248 9272
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).2)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_snd_out pm st 0 16 4 4944 9268 9236 9248 9270 9272 (by decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have q1 := l11o_reduce4 pm initPM 804
    { rank := 1, op := "OpName.FW_rotary_embedding", ins := [4944, 9269, 9237, 9249],
      outs := [9271, 9273], params := [16, 4] }
    4944 9269 9237 9249 9271
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).1)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_fst_out pm st 1 16 4 4944 9269 9237 9249 9271 9273)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have k1 := l11o_reduce4 pm initPM 804
    { rank := 1, op := "OpName.FW_rotary_embedding", ins := [4944, 9269, 9237, 9249],
      outs := [9271, 9273], params := [16, 4] }
    4944 9269 9237 9249 9273
    (fun cs pos q k => (fw_rotary_embedding cs pos q k 16 4).2)
    (by native_decide) (by native_decide) (by decide)
    (fun st => by
      rw [applyNodeRingAttn_eq_applyNode_of_not_ring pm st _ (by decide) (by decide)]
      exact applyNode_fw_rotary_embedding_snd_out pm st 1 16 4 4944 9269 9237 9249 9271 9273 (by decide))
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have qval : denoteGraphDistributed sm initSM 5440 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 9270, denoteGraphDistributed pm initPM 9271] := by
    rw [qS]
    simp only [fw_rotary_embedding]
    rw [qRel.value, l11o_rotary_allGather0_1d (denoteGraphDistributed sm initSM 4944)
      (denoteGraphDistributed sm initSM 5439) (denoteGraphDistributed pm initPM 9236)
      (denoteGraphDistributed pm initPM 9237) 2048 16 64 (by omega) (by omega) (by omega)
      hspos qRel.shard0_shape qRel.shard1_shape, hcache, hpos, ← pc0, ← pc1, q0, q1]
    simp only [fw_rotary_embedding]
  have kval : denoteGraphDistributed sm initSM 5441 = allGatherPrimDimN 0 2 0
      [denoteGraphDistributed pm initPM 9272, denoteGraphDistributed pm initPM 9273] := by
    rw [kS]
    simp only [fw_rotary_embedding]
    rw [kRel.value, l11o_rotary_allGather0_1d (denoteGraphDistributed sm initSM 4944)
      (denoteGraphDistributed sm initSM 5439) (denoteGraphDistributed pm initPM 9248)
      (denoteGraphDistributed pm initPM 9249) 2048 4 64 (by omega) (by omega) (by omega)
      hspos kRel.shard0_shape kRel.shard1_shape, hcache, hpos, ← pc0, ← pc1, k0, k1]
    simp only [fw_rotary_embedding]
  have qs0 : (denoteGraphDistributed pm initPM 9270).shape = [2048, 16, 64] := by
    rw [q0]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 qRel.shard0_shape
  have qs1 : (denoteGraphDistributed pm initPM 9271).shape = [2048, 16, 64] := by
    rw [q1]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 16 64 qRel.shard1_shape
  have ks0 : (denoteGraphDistributed pm initPM 9272).shape = [2048, 4, 64] := by
    rw [k0]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 kRel.shard0_shape
  have ks1 : (denoteGraphDistributed pm initPM 9273).shape = [2048, 4, 64] := by
    rw [k1]
    simp only [fw_rotary_embedding]
    exact fw_rotary_apply_shape_c2a _ _ _ 2048 4 64 kRel.shard1_shape
  refine ⟨⟨qval, ?_, qs0, qs1, by decide⟩, ⟨kval, ?_, ks0, ks1, by decide⟩⟩
  · rw [qval, allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by simp [qs0])]
    rfl
  · rw [kval, allGatherPrimDimN_shape 0 2 _ [2048, 4, 64] (by simp [ks0])]
    rfl

end TrainVerify.Denote.GeneratedPatterns
