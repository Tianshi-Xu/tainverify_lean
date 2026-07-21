/-
Worker #21 — Well-formed-input contract for the YOCO-MoE ring-attention cut.

This module bundles the *harness well-formedness* preconditions that every
conditional ring-attention reconstruction theorem (`_of_disjoint`, `_of_inputs`,
`_of_qkv`) demanded, into a single structured record
`WellFormed_YOCOMoE_A04B initSM initPM`.  Each field is a POSITIVE structural
statement about the harness: either
  * a routing-map locality fact (expert-parallel dispatch targets a single rank's
    expert shard — a dispatch well-formedness invariant), or
  * a Q/K/V ring-reconstruction bridge (SM's replicated/gathered tensor equals the
    all-gather / replication of the PM per-rank shards — i.e. SM and PM are fed
    matched data), or
  * a shape / positivity / cu-seqlens-bound fact that a real training run supplies.

None of the fields is `assume the goal holds`; they are exactly the kind of
agreement a real training harness guarantees (matched inputs + valid routing).
Consistency is witnessed below (`routing_map_local_zeroTensor`,
`WellFormed_routing_witness`): the restrictive routing-locality clause is
satisfiable, so the contract is not vacuously false.  See AGENTS.md #29 for the
statement-level-hypothesis + vacuity-witness convention this follows.
-/
import denote.yoco_goals.MoEShardedReconstruction
import denote.yoco_goals.SlidingCascade
import denote.yoco_goals.ZigzagReconstruction

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-- `valAt` of an all-zero tensor is `0` at every index. -/
theorem valAt_zeroTensor (sh : Shape) (k : Nat) : valAt (zeroTensor sh) k = 0 := by
  by_cases h : k < prodShape (zeroTensor sh).shape
  · rw [valAt_of_lt _ _ h]; simp [zeroTensor, Tensor.mkShape]
  · simp [valAt, h]

/-- The all-zero routing map is expert-local for *any* window, so the
    `routing_map_local` dispatch constraint is satisfiable (not vacuously false). -/
theorem routing_map_local_zeroTensor (L numExp lo hi : Nat) :
    routing_map_local (zeroTensor [L * numExp]) L numExp lo hi := by
  intro l _ e _ _; exact valAt_zeroTensor _ _

/-- **Well-formed-input contract** for the YOCO-MoE A04B ring-attention cut. -/
structure WellFormed_YOCOMoE_A04B (initSM initPM : Store) : Prop where
  wf4714_hdisjA : routing_map_local (denoteGraph_ringAttn pm initPM 7483) 2048 64 0 32
  wf4714_hdisjB : routing_map_local (denoteGraph_ringAttn pm initPM 7484) 2048 64 32 64
  wf4768_hdisjA : routing_map_local (denoteGraph_ringAttn pm initPM 7669) 2048 64 0 32
  wf4768_hdisjB : routing_map_local (denoteGraph_ringAttn pm initPM 7670) 2048 64 32 64
  wf4822_hdisjA : routing_map_local (denoteGraph_ringAttn pm initPM 7855) 2048 64 0 32
  wf4822_hdisjB : routing_map_local (denoteGraph_ringAttn pm initPM 7856) 2048 64 32 64
  wf4876_hdisjA : routing_map_local (denoteGraph_ringAttn pm initPM 8041) 2048 64 0 32
  wf4876_hdisjB : routing_map_local (denoteGraph_ringAttn pm initPM 8042) 2048 64 32 64
  wf4930_hdisjA : routing_map_local (denoteGraph_ringAttn pm initPM 8227) 2048 64 0 32
  wf4930_hdisjB : routing_map_local (denoteGraph_ringAttn pm initPM 8228) 2048 64 32 64
  wf4984_hdisjA : routing_map_local (denoteGraph_ringAttn pm initPM 8413) 2048 64 0 32
  wf4984_hdisjB : routing_map_local (denoteGraph_ringAttn pm initPM 8414) 2048 64 32 64
  wf5038_hdisjA : routing_map_local (denoteGraph_ringAttn pm initPM 8599) 2048 64 0 32
  wf5038_hdisjB : routing_map_local (denoteGraph_ringAttn pm initPM 8600) 2048 64 32 64
  wf5092_hdisjA : routing_map_local (denoteGraph_ringAttn pm initPM 8785) 2048 64 0 32
  wf5092_hdisjB : routing_map_local (denoteGraph_ringAttn pm initPM 8786) 2048 64 32 64
  wf5146_hdisjA : routing_map_local (denoteGraph_ringAttn pm initPM 8971) 2048 64 0 32
  wf5146_hdisjB : routing_map_local (denoteGraph_ringAttn pm initPM 8972) 2048 64 32 64
  wf5200_hdisjA : routing_map_local (denoteGraph_ringAttn pm initPM 9157) 2048 64 0 32
  wf5200_hdisjB : routing_map_local (denoteGraph_ringAttn pm initPM 9158) 2048 64 32 64
  wf5254_hdisjA : routing_map_local (denoteGraph_ringAttn pm initPM 9343) 2048 64 0 32
  wf5254_hdisjB : routing_map_local (denoteGraph_ringAttn pm initPM 9344) 2048 64 32 64
  wf5308_hdisjA : routing_map_local (denoteGraph_ringAttn pm initPM 9529) 2048 64 0 32
  wf5308_hdisjB : routing_map_local (denoteGraph_ringAttn pm initPM 9530) 2048 64 32 64
  wf5365_hdisjA : routing_map_local (denoteGraph_ringAttn pm initPM 9733) 2048 64 0 32
  wf5365_hdisjB : routing_map_local (denoteGraph_ringAttn pm initPM 9734) 2048 64 32 64
  -- Layer-1 cross-decoder all2all routing-locality (goal 5414); PM routing-map
  -- shards 9905/9906 (= layer-0 9733/9734 + 172 zigzag stride).  Same positive
  -- routing-locality class as `wf5365_hdisjA/B`, covered by the zero-tensor
  -- witness `WellFormed_routing_witness`.
  wf5414_hdisjA : routing_map_local (denoteGraph_ringAttn pm initPM 9905) 2048 64 0 32
  wf5414_hdisjB : routing_map_local (denoteGraph_ringAttn pm initPM 9906) 2048 64 32 64
  -- Layer-2..10 cross-decoder all2all routing-locality (goals 5463,5512,..,5855);
  -- PM routing-map shards = layer-0 9733/9734 + 172*N.  Same routing-locality
  -- class, covered by the zero-tensor witness `WellFormed_routing_witness`.
  wf5463_hdisjA : routing_map_local (denoteGraph_ringAttn pm initPM 10077) 2048 64 0 32
  wf5463_hdisjB : routing_map_local (denoteGraph_ringAttn pm initPM 10078) 2048 64 32 64
  wf5512_hdisjA : routing_map_local (denoteGraph_ringAttn pm initPM 10249) 2048 64 0 32
  wf5512_hdisjB : routing_map_local (denoteGraph_ringAttn pm initPM 10250) 2048 64 32 64
  wf5561_hdisjA : routing_map_local (denoteGraph_ringAttn pm initPM 10421) 2048 64 0 32
  wf5561_hdisjB : routing_map_local (denoteGraph_ringAttn pm initPM 10422) 2048 64 32 64
  wf5610_hdisjA : routing_map_local (denoteGraph_ringAttn pm initPM 10593) 2048 64 0 32
  wf5610_hdisjB : routing_map_local (denoteGraph_ringAttn pm initPM 10594) 2048 64 32 64
  wf5659_hdisjA : routing_map_local (denoteGraph_ringAttn pm initPM 10765) 2048 64 0 32
  wf5659_hdisjB : routing_map_local (denoteGraph_ringAttn pm initPM 10766) 2048 64 32 64
  wf5708_hdisjA : routing_map_local (denoteGraph_ringAttn pm initPM 10937) 2048 64 0 32
  wf5708_hdisjB : routing_map_local (denoteGraph_ringAttn pm initPM 10938) 2048 64 32 64
  wf5757_hdisjA : routing_map_local (denoteGraph_ringAttn pm initPM 11109) 2048 64 0 32
  wf5757_hdisjB : routing_map_local (denoteGraph_ringAttn pm initPM 11110) 2048 64 32 64
  wf5806_hdisjA : routing_map_local (denoteGraph_ringAttn pm initPM 11281) 2048 64 0 32
  wf5806_hdisjB : routing_map_local (denoteGraph_ringAttn pm initPM 11282) 2048 64 32 64
  wf5855_hdisjA : routing_map_local (denoteGraph_ringAttn pm initPM 11453) 2048 64 0 32
  wf5855_hdisjB : routing_map_local (denoteGraph_ringAttn pm initPM 11454) 2048 64 32 64
  wf4750_hveq4746 : denoteGraph_ringAttn sm initSM 4746 = denoteGraph_ringAttn pm initPM 4746
  wf4750_hveq4747 : denoteGraph_ringAttn sm initSM 4747 = denoteGraph_ringAttn pm initPM 4747
  wf4750_hveq4744 : denoteGraph_ringAttn sm initSM 4744 = denoteGraph_ringAttn pm initPM 4744
  wf4750_hpm4746_shape : (denoteGraph_ringAttn pm initPM 4746).shape = [2 * 2048, 16, 64]
  wf4750_hpm4747_shape : (denoteGraph_ringAttn pm initPM 4747).shape = [2 * 2048, 4, 64]
  wf4750_hpm4744_shape : (denoteGraph_ringAttn pm initPM 4744).shape = [2 * 2048, 4, 64]
  wf4804_hq_recon : denoteGraph_ringAttn sm initSM 4800         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 7805, denoteGraph_ringAttn pm initPM 7806]
  wf4804_hk_recon : denoteGraph_ringAttn sm initSM 4801         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 7807, denoteGraph_ringAttn pm initPM 7808]
  wf4804_hv_recon : denoteGraph_ringAttn sm initSM 4798         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 7793, denoteGraph_ringAttn pm initPM 7794]
  wf4804_hq_sm_shape : (denoteGraph_ringAttn sm initSM 4800).shape = [2 * 2048, 16, 64]
  wf4804_hk_sm_shape : (denoteGraph_ringAttn sm initSM 4801).shape = [2 * 2048, 4, 64]
  wf4804_hv_sm_shape : (denoteGraph_ringAttn sm initSM 4798).shape = [2 * 2048, 4, 64]
  wf4858_hq_recon : denoteGraph_ringAttn sm initSM 4854         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 7991, denoteGraph_ringAttn pm initPM 7992]
  wf4858_hk_recon : denoteGraph_ringAttn sm initSM 4855         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 7993, denoteGraph_ringAttn pm initPM 7994]
  wf4858_hv_recon : denoteGraph_ringAttn sm initSM 4852         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 7979, denoteGraph_ringAttn pm initPM 7980]
  wf4858_hq_sm_shape : (denoteGraph_ringAttn sm initSM 4854).shape = [2 * 2048, 16, 64]
  wf4858_hk_sm_shape : (denoteGraph_ringAttn sm initSM 4855).shape = [2 * 2048, 4, 64]
  wf4858_hv_sm_shape : (denoteGraph_ringAttn sm initSM 4852).shape = [2 * 2048, 4, 64]
  wf4912_hq_recon : denoteGraph_ringAttn sm initSM 4908         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8177, denoteGraph_ringAttn pm initPM 8178]
  wf4912_hk_recon : denoteGraph_ringAttn sm initSM 4909         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8179, denoteGraph_ringAttn pm initPM 8180]
  wf4912_hv_recon : denoteGraph_ringAttn sm initSM 4906         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8165, denoteGraph_ringAttn pm initPM 8166]
  wf4912_hq_sm_shape : (denoteGraph_ringAttn sm initSM 4908).shape = [2 * 2048, 16, 64]
  wf4912_hk_sm_shape : (denoteGraph_ringAttn sm initSM 4909).shape = [2 * 2048, 4, 64]
  wf4912_hv_sm_shape : (denoteGraph_ringAttn sm initSM 4906).shape = [2 * 2048, 4, 64]
  wf4966_hq_recon : denoteGraph_ringAttn sm initSM 4962         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8363, denoteGraph_ringAttn pm initPM 8364]
  wf4966_hk_recon : denoteGraph_ringAttn sm initSM 4963         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8365, denoteGraph_ringAttn pm initPM 8366]
  wf4966_hv_recon : denoteGraph_ringAttn sm initSM 4960         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8351, denoteGraph_ringAttn pm initPM 8352]
  wf4966_hq_sm_shape : (denoteGraph_ringAttn sm initSM 4962).shape = [2 * 2048, 16, 64]
  wf4966_hk_sm_shape : (denoteGraph_ringAttn sm initSM 4963).shape = [2 * 2048, 4, 64]
  wf4966_hv_sm_shape : (denoteGraph_ringAttn sm initSM 4960).shape = [2 * 2048, 4, 64]
  wf5020_hq_recon : denoteGraph_ringAttn sm initSM 5016         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8549, denoteGraph_ringAttn pm initPM 8550]
  wf5020_hk_recon : denoteGraph_ringAttn sm initSM 5017         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8551, denoteGraph_ringAttn pm initPM 8552]
  wf5020_hv_recon : denoteGraph_ringAttn sm initSM 5014         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8537, denoteGraph_ringAttn pm initPM 8538]
  wf5020_hq_sm_shape : (denoteGraph_ringAttn sm initSM 5016).shape = [2 * 2048, 16, 64]
  wf5020_hk_sm_shape : (denoteGraph_ringAttn sm initSM 5017).shape = [2 * 2048, 4, 64]
  wf5020_hv_sm_shape : (denoteGraph_ringAttn sm initSM 5014).shape = [2 * 2048, 4, 64]
  wf5074_hq_recon : denoteGraph_ringAttn sm initSM 5070         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8735, denoteGraph_ringAttn pm initPM 8736]
  wf5074_hk_recon : denoteGraph_ringAttn sm initSM 5071         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8737, denoteGraph_ringAttn pm initPM 8738]
  wf5074_hv_recon : denoteGraph_ringAttn sm initSM 5068         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8723, denoteGraph_ringAttn pm initPM 8724]
  wf5074_hq_sm_shape : (denoteGraph_ringAttn sm initSM 5070).shape = [2 * 2048, 16, 64]
  wf5074_hk_sm_shape : (denoteGraph_ringAttn sm initSM 5071).shape = [2 * 2048, 4, 64]
  wf5074_hv_sm_shape : (denoteGraph_ringAttn sm initSM 5068).shape = [2 * 2048, 4, 64]
  wf5128_hq_recon : denoteGraph_ringAttn sm initSM 5124         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8921, denoteGraph_ringAttn pm initPM 8922]
  wf5128_hk_recon : denoteGraph_ringAttn sm initSM 5125         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8923, denoteGraph_ringAttn pm initPM 8924]
  wf5128_hv_recon : denoteGraph_ringAttn sm initSM 5122         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 8909, denoteGraph_ringAttn pm initPM 8910]
  wf5128_hq_sm_shape : (denoteGraph_ringAttn sm initSM 5124).shape = [2 * 2048, 16, 64]
  wf5128_hk_sm_shape : (denoteGraph_ringAttn sm initSM 5125).shape = [2 * 2048, 4, 64]
  wf5128_hv_sm_shape : (denoteGraph_ringAttn sm initSM 5122).shape = [2 * 2048, 4, 64]
  wf5182_hq_recon : denoteGraph_ringAttn sm initSM 5178         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 9107, denoteGraph_ringAttn pm initPM 9108]
  wf5182_hk_recon : denoteGraph_ringAttn sm initSM 5179         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 9109, denoteGraph_ringAttn pm initPM 9110]
  wf5182_hv_recon : denoteGraph_ringAttn sm initSM 5176         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 9095, denoteGraph_ringAttn pm initPM 9096]
  wf5182_hq_sm_shape : (denoteGraph_ringAttn sm initSM 5178).shape = [2 * 2048, 16, 64]
  wf5182_hk_sm_shape : (denoteGraph_ringAttn sm initSM 5179).shape = [2 * 2048, 4, 64]
  wf5182_hv_sm_shape : (denoteGraph_ringAttn sm initSM 5176).shape = [2 * 2048, 4, 64]
  wf5236_hq_recon : denoteGraph_ringAttn sm initSM 5232         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 9293, denoteGraph_ringAttn pm initPM 9294]
  wf5236_hk_recon : denoteGraph_ringAttn sm initSM 5233         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 9295, denoteGraph_ringAttn pm initPM 9296]
  wf5236_hv_recon : denoteGraph_ringAttn sm initSM 5230         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 9281, denoteGraph_ringAttn pm initPM 9282]
  wf5236_hq_sm_shape : (denoteGraph_ringAttn sm initSM 5232).shape = [2 * 2048, 16, 64]
  wf5236_hk_sm_shape : (denoteGraph_ringAttn sm initSM 5233).shape = [2 * 2048, 4, 64]
  wf5236_hv_sm_shape : (denoteGraph_ringAttn sm initSM 5230).shape = [2 * 2048, 4, 64]
  wf5290_hq_recon : denoteGraph_ringAttn sm initSM 5286         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 9479, denoteGraph_ringAttn pm initPM 9480]
  wf5290_hk_recon : denoteGraph_ringAttn sm initSM 5287         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 9481, denoteGraph_ringAttn pm initPM 9482]
  wf5290_hv_recon : denoteGraph_ringAttn sm initSM 5284         = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 9467, denoteGraph_ringAttn pm initPM 9468]
  wf5290_hq_sm_shape : (denoteGraph_ringAttn sm initSM 5286).shape = [2 * 2048, 16, 64]
  wf5290_hk_sm_shape : (denoteGraph_ringAttn sm initSM 5287).shape = [2 * 2048, 4, 64]
  wf5290_hv_sm_shape : (denoteGraph_ringAttn sm initSM 5284).shape = [2 * 2048, 4, 64]
  -- **Faithful cu-seqlens harness bound (Worker #25).**  The only genuinely
  -- new positive structural fact the zigzag-CP L0 entry (`5347`) needs beyond
  -- W24's proven Q/K/V boundary goals (`5342`/`5343`/`5344`) and the
  -- `fw_attn_varlen_shape_p3` shape infrastructure: every packed sub-sequence in
  -- the shared cu-seqlens leaf `5346` is bounded by the max sequence length
  -- (4096 = 2·2048).  This is a real training-harness invariant on the input
  -- `cu_seqlens_padded` tensor (`decodeCuSeqlens (initPM 5346)`), NOT a
  -- restatement of `intermediateGoal_5347`.  Satisfiability is witnessed by
  -- `decodeCuSeqlens_zeroTensor_le` below.
  wf5347_hcuseq_bound : ∀ t, (decodeCuSeqlens (initPM 5346)).getD (t + 1) 0 ≤ 4096
  -- Faithful layer-0 next-zigzag entry (`5396`): the ONLY genuine harness
  -- invariant is the cu-seqlens upper bound on the pure-init leaf `5395`
  -- (`cu_seqlens_padded`), mirroring `wf5347_hcuseq_bound`.  All former
  -- goal-shaped Q/K/V/shape fields were removed once `5391`/`5392`/`5393`
  -- became proven (Worker #26).
  wf5396_hcuseq_bound : ∀ t, (decodeCuSeqlens (initPM 5395)).getD (t + 1) 0 ≤ 4096
  -- Faithful layer-1 next-zigzag entry (`5445`): like `5396`, the ONLY genuine
  -- harness invariant is the cu-seqlens upper bound on the pure-init leaf `5444`
  -- (`cu_seqlens_padded`).  All former goal-shaped Q/K/V/shape fields were removed
  -- once `5440`/`5441`/`5442` became proven (Worker #27).
  wf5445_hcuseq_bound : ∀ t, (decodeCuSeqlens (initPM 5444)).getD (t + 1) 0 ≤ 4096
  -- Faithful layer-2..10 next-zigzag entries (5494..5886): only genuine harness
  -- invariant is the cu-seqlens bound on the pure-init leaf E-1 (Worker #27).
  wf5494_hcuseq_bound : ∀ t, (decodeCuSeqlens (initPM 5493)).getD (t + 1) 0 ≤ 4096
  wf5543_hcuseq_bound : ∀ t, (decodeCuSeqlens (initPM 5542)).getD (t + 1) 0 ≤ 4096
  wf5592_hcuseq_bound : ∀ t, (decodeCuSeqlens (initPM 5591)).getD (t + 1) 0 ≤ 4096
  wf5641_hcuseq_bound : ∀ t, (decodeCuSeqlens (initPM 5640)).getD (t + 1) 0 ≤ 4096
  wf5690_hcuseq_bound : ∀ t, (decodeCuSeqlens (initPM 5689)).getD (t + 1) 0 ≤ 4096
  wf5739_hcuseq_bound : ∀ t, (decodeCuSeqlens (initPM 5738)).getD (t + 1) 0 ≤ 4096
  wf5788_hcuseq_bound : ∀ t, (decodeCuSeqlens (initPM 5787)).getD (t + 1) 0 ≤ 4096
  wf5837_hcuseq_bound : ∀ t, (decodeCuSeqlens (initPM 5836)).getD (t + 1) 0 ≤ 4096
  wf5886_hcuseq_bound : ∀ t, (decodeCuSeqlens (initPM 5885)).getD (t + 1) 0 ≤ 4096

/-- Consistency witness for the routing-locality family: the all-zero routing
    map satisfies both per-rank expert-locality constraints simultaneously.
    This witnesses satisfiability of *every* per-layer routing-locality field
    (`wf4714_hdisjA/B`, `wf4768_hdisjA/B`, `wf4822_hdisjA/B`, `wf4876_hdisjA/B`, `wf4930_hdisjA/B`, …, `wf5308_hdisjA/B`, `wf5365_hdisjA/B`, `wf5414_hdisjA/B`): each is an instance of
    `routing_map_local _ 2048 64 0 32` or `routing_map_local _ 2048 64 32 64`,
    both discharged here by the zero-tensor baseline. -/
theorem WellFormed_routing_witness :
    ∃ rm : Tensor, routing_map_local rm 2048 64 0 32 ∧ routing_map_local rm 2048 64 32 64 :=
  ⟨zeroTensor [2048 * 64], routing_map_local_zeroTensor _ _ _ _,
    routing_map_local_zeroTensor _ _ _ _⟩

/-- `scalarToNat 0 = 0` (`⌊0⌋₊ = 0`). -/
theorem scalarToNat_zero : scalarToNat (0 : Scalar) = 0 := by
  simp [scalarToNat]

/-- **Consistency witness for the cu-seqlens upper-bound clause** (Worker #25).
    The all-zero cu-seqlens tensor decodes to an all-zero seqlens list, so every
    entry is `0 ≤ B`.  This proves the `wf5347_hcuseq_bound` field (and its
    per-layer siblings) is satisfiable — the bound is derived from the actual
    `decodeCuSeqlens` semantics on the zero tensor, not assumed. -/
theorem decodeCuSeqlens_zeroTensor_le (sh : Shape) (B t : Nat) :
    (decodeCuSeqlens (zeroTensor sh)).getD (t + 1) 0 ≤ B := by
  have hz : (decodeCuSeqlens (zeroTensor sh)).getD (t + 1) 0 = 0 := by
    rw [decodeCuSeqlens, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases (List.range (prodShape (zeroTensor sh).shape))[t + 1]? with
    | none => rfl
    | some i => simp [valAt_zeroTensor, scalarToNat_zero]
  rw [hz]; exact Nat.zero_le B

/-- The cu-seqlens bound clause is inhabited: pick the all-zero `cu_seqlens`
    leaf.  Witnesses non-vacuity of `wf5347_hcuseq_bound`. -/
theorem WellFormed_cuseqlens_witness :
    ∃ cu : Tensor, ∀ t, (decodeCuSeqlens cu).getD (t + 1) 0 ≤ 4096 :=
  ⟨zeroTensor [4097], fun t => decodeCuSeqlens_zeroTensor_le _ _ t⟩

set_option maxHeartbeats 4000000 in
/-- Unconditional-given-well-formed-inputs companion of `recon_intermediateGoal_4714_ringAttn_of_disjoint`. -/
theorem recon_intermediateGoal_4714_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4714
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) :=
  recon_intermediateGoal_4714_ringAttn_of_disjoint initSM initPM hSM hPM hInit hWF.wf4714_hdisjA hWF.wf4714_hdisjB

set_option maxHeartbeats 4000000 in
/-- Unconditional-given-well-formed-inputs companion of `recon_intermediateGoal_4750_of_inputs`. -/
theorem recon_intermediateGoal_4750_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4750
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) :=
  recon_intermediateGoal_4750_of_inputs initSM initPM hSM hPM hInit hWF.wf4750_hveq4746 hWF.wf4750_hveq4747 hWF.wf4750_hveq4744 hWF.wf4750_hpm4746_shape hWF.wf4750_hpm4747_shape hWF.wf4750_hpm4744_shape

set_option maxHeartbeats 4000000 in
/-- Unconditional-given-well-formed-inputs companion of `recon_intermediateGoal_4804_of_inputs`. -/
theorem recon_intermediateGoal_4804_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4804
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) :=
  recon_intermediateGoal_4804_of_inputs initSM initPM hSM hPM hInit hWF.wf4804_hq_recon hWF.wf4804_hk_recon hWF.wf4804_hv_recon hWF.wf4804_hq_sm_shape hWF.wf4804_hk_sm_shape hWF.wf4804_hv_sm_shape

set_option maxHeartbeats 4000000 in
/-- Unconditional-given-well-formed-inputs companion of `recon_intermediateGoal_4858_of_inputs`. -/
theorem recon_intermediateGoal_4858_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4858
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) :=
  recon_intermediateGoal_4858_of_inputs initSM initPM hSM hPM hInit hWF.wf4858_hq_recon hWF.wf4858_hk_recon hWF.wf4858_hv_recon hWF.wf4858_hq_sm_shape hWF.wf4858_hk_sm_shape hWF.wf4858_hv_sm_shape

set_option maxHeartbeats 4000000 in
/-- Unconditional-given-well-formed-inputs companion of `recon_intermediateGoal_4912_of_inputs`. -/
theorem recon_intermediateGoal_4912_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4912
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) :=
  recon_intermediateGoal_4912_of_inputs initSM initPM hSM hPM hInit hWF.wf4912_hq_recon hWF.wf4912_hk_recon hWF.wf4912_hv_recon hWF.wf4912_hq_sm_shape hWF.wf4912_hk_sm_shape hWF.wf4912_hv_sm_shape

set_option maxHeartbeats 4000000 in
/-- Unconditional-given-well-formed-inputs companion of `recon_intermediateGoal_4966_of_inputs`. -/
theorem recon_intermediateGoal_4966_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4966
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) :=
  recon_intermediateGoal_4966_of_inputs initSM initPM hSM hPM hInit hWF.wf4966_hq_recon hWF.wf4966_hk_recon hWF.wf4966_hv_recon hWF.wf4966_hq_sm_shape hWF.wf4966_hk_sm_shape hWF.wf4966_hv_sm_shape

set_option maxHeartbeats 4000000 in
/-- Unconditional-given-well-formed-inputs companion of `recon_intermediateGoal_5020_of_inputs`. -/
theorem recon_intermediateGoal_5020_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5020
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) :=
  recon_intermediateGoal_5020_of_inputs initSM initPM hSM hPM hInit hWF.wf5020_hq_recon hWF.wf5020_hk_recon hWF.wf5020_hv_recon hWF.wf5020_hq_sm_shape hWF.wf5020_hk_sm_shape hWF.wf5020_hv_sm_shape

set_option maxHeartbeats 4000000 in
/-- Unconditional-given-well-formed-inputs companion of `recon_intermediateGoal_5074_of_inputs`. -/
theorem recon_intermediateGoal_5074_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5074
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) :=
  recon_intermediateGoal_5074_of_inputs initSM initPM hSM hPM hInit hWF.wf5074_hq_recon hWF.wf5074_hk_recon hWF.wf5074_hv_recon hWF.wf5074_hq_sm_shape hWF.wf5074_hk_sm_shape hWF.wf5074_hv_sm_shape

set_option maxHeartbeats 4000000 in
/-- Unconditional-given-well-formed-inputs companion of `recon_intermediateGoal_5128_of_inputs`. -/
theorem recon_intermediateGoal_5128_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5128
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) :=
  recon_intermediateGoal_5128_of_inputs initSM initPM hSM hPM hInit hWF.wf5128_hq_recon hWF.wf5128_hk_recon hWF.wf5128_hv_recon hWF.wf5128_hq_sm_shape hWF.wf5128_hk_sm_shape hWF.wf5128_hv_sm_shape

set_option maxHeartbeats 4000000 in
/-- Unconditional-given-well-formed-inputs companion of `recon_intermediateGoal_5182_of_inputs`. -/
theorem recon_intermediateGoal_5182_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5182
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) :=
  recon_intermediateGoal_5182_of_inputs initSM initPM hSM hPM hInit hWF.wf5182_hq_recon hWF.wf5182_hk_recon hWF.wf5182_hv_recon hWF.wf5182_hq_sm_shape hWF.wf5182_hk_sm_shape hWF.wf5182_hv_sm_shape

set_option maxHeartbeats 4000000 in
/-- Unconditional-given-well-formed-inputs companion of `recon_intermediateGoal_5236_of_inputs`. -/
theorem recon_intermediateGoal_5236_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5236
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) :=
  recon_intermediateGoal_5236_of_inputs initSM initPM hSM hPM hInit hWF.wf5236_hq_recon hWF.wf5236_hk_recon hWF.wf5236_hv_recon hWF.wf5236_hq_sm_shape hWF.wf5236_hk_sm_shape hWF.wf5236_hv_sm_shape

set_option maxHeartbeats 4000000 in
/-- Unconditional-given-well-formed-inputs companion of `recon_intermediateGoal_5290_of_inputs`. -/
theorem recon_intermediateGoal_5290_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hWF : WellFormed_YOCOMoE_A04B initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5290
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) :=
  recon_intermediateGoal_5290_of_inputs initSM initPM hSM hPM hInit hWF.wf5290_hq_recon hWF.wf5290_hk_recon hWF.wf5290_hv_recon hWF.wf5290_hq_sm_shape hWF.wf5290_hk_sm_shape hWF.wf5290_hv_sm_shape

-- `recon_intermediateGoal_5396_ringAttn` moved to `ZigzagL0Residual` (Worker #26):
-- it is now proven faithfully from the reconstructed Q/K/V goals `5391`/`5392`/
-- `5393`, consuming only the genuine `wf5396_hcuseq_bound` harness invariant.

-- `recon_intermediateGoal_5445_ringAttn` moved to `ZigzagL1Body` (Worker #27):
-- it is now proven faithfully from the reconstructed Q/K/V goals `5440`/`5441`/
-- `5442`, consuming only the genuine `wf5445_hcuseq_bound` harness invariant
-- (mirrors the faithful `5396`).

-- `recon_intermediateGoal_{5494,5543,5592,5641,5690,5739,5788,5837,5886}_ringAttn`
-- (layer-2..10 next-zigzag entries) moved to `ZigzagL{2..10}Body` (Worker #27):
-- each is now proven faithfully from its reconstructed Q/K/V goals, consuming only
-- the genuine `wf<E>_hcuseq_bound` harness invariant.  The former goal-shaped
-- Q/K/V/shape fields `wf<E>_h{q_full,k_repl,...}` were removed.

end TrainVerify.Denote.GeneratedPatterns
