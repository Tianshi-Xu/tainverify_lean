import denote.yoco_goals.L12FaithfulMaybeShuffle

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

-- All large generated-graph scans are shared here.  The whitelist contains exactly
-- the prefix/suffix reads used by the three faithful singleton reconstructions.
set_option maxRecDepth 1000000 in
private theorem l12_boundary_sm_facts :
    sm.nodes[470]'(by native_decide) =
      { rank := 0, op := "OpName.FW_multiref", ins := [5330], outs := [8007, 8011], params := [2] } ∧
    sm.nodes[471]'(by native_decide) =
      { rank := 0, op := "OpName.FW_rms_norm", ins := [8007, 5331], outs := [5332] } ∧
    sm.nodes[473]'(by native_decide) =
      { rank := 0, op := "OpName.FW_multiref", ins := [5332], outs := [8015, 8019], params := [2] } ∧
    sm.nodes[475]'(by native_decide) =
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [8015, 5333], outs := [5334] } ∧
    sm.nodes[476]'(by native_decide) =
      { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [8019, 5335], outs := [5336] } ∧
    (∀ n ∈ sm.nodes, 5331 ∉ n.outs ∧ 5333 ∉ n.outs ∧ 5335 ∉ n.outs) ∧
    (∀ n ∈ sm.nodes.take 472,
      n.op ≠ "OpName.FW_maybe_shuffle" ∧ n.op ≠ "OpName.FW_maybe_unshuffle") := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l12_boundary_pm_facts :
    pm.nodes[1001]'(by native_decide) =
      { rank := 0, op := "OpName.FW_multiref", ins := [9625], outs := [14597, 13257], params := [2] } ∧
    pm.nodes[1002]'(by native_decide) =
      { rank := 1, op := "OpName.FW_multiref", ins := [9626], outs := [14599, 13258], params := [2] } ∧
    pm.nodes[1004]'(by native_decide) =
      { rank := 0, op := "OpName.AllGatherPrim", ins := [14597, 14599], outs := [11917], params := [0] } ∧
    pm.nodes[1008]'(by native_decide) =
      { rank := 1, op := "OpName.FW_rms_norm", ins := [11917, 5331], outs := [5332] } ∧
    pm.nodes[1012]'(by native_decide) =
      { rank := 1, op := "OpName.FW_multiref", ins := [5332], outs := [15749, 15753], params := [2] } ∧
    pm.nodes[1017]'(by native_decide) =
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15749, 5333], outs := [5334] } ∧
    pm.nodes[1018]'(by native_decide) =
      { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15753, 5335], outs := [5336] } ∧
    (∀ n ∈ pm.nodes, 5331 ∉ n.outs ∧ 5333 ∉ n.outs ∧ 5335 ∉ n.outs) ∧
    (∀ n ∈ pm.nodes.take 1003,
      n.op ≠ "OpName.FW_maybe_shuffle" ∧ n.op ≠ "OpName.FW_maybe_unshuffle") := by
  native_decide

private theorem l12_boundary_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈
      [(471, 8007), (470, 5330), (472, 5330), (472, 5332),
       (471, 5331), (474, 8015), (474, 8019), (473, 5332),
       (476, 5334), (475, 8015), (475, 5333),
       (477, 5336), (476, 8019), (476, 5335)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

private theorem l12_boundary_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈
      [(1002, 14597), (1001, 9625), (1003, 9625),
       (1003, 14599), (1002, 9626), (1003, 9626),
       (1005, 11917), (1004, 14597), (1004, 14599),
       (1009, 5332), (1008, 11917), (1008, 5331),
       (1013, 15749), (1013, 15753), (1012, 5332),
       (1018, 5334), (1017, 15749), (1017, 5333),
       (1019, 5336), (1018, 15753), (1018, 5335)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;> native_decide +revert

private theorem faithful_nonempty_sm (k : Nat) : ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem faithful_nonempty_pm (k : Nat) : ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem faithful_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (tid : Tid) (goal : LineageGoal)
    (hmem : goal ∈ initGoals)
    (htp : goal.tps = [{rank := 0, tid := tid}]) (hgd : goal.gatherDim = 0)
    (hrep : goal.replicated = false) (hts : goal.ts = tid)
    (hsm : ∀ n ∈ sm.nodes, tid ∉ n.outs)
    (hpm : ∀ n ∈ pm.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful sm initSM tid =
      denoteGraphDistributedFaithful pm initPM tid := by
  have hg := hInit goal hmem
  unfold InitGoalHolds at hg
  have hi := hg.2.2
  rw [reconstructForGoal_of_not_replicated goal pm.numRanks _ hrep, htp, hts, hgd] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM tid
      layer1_sm_nodes_nonempty hsm,
    foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM tid
      layer1_pm_nodes_nonempty hpm]
  exact hi

private theorem faithful_weight_shape (initSM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (tid : Tid) (shape : List Nat)
    (henv : smInitEnv tid = some shape)
    (hsm : ∀ n ∈ sm.nodes, tid ∉ n.outs) :
    (denoteGraphDistributedFaithful sm initSM tid).shape = shape := by
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM tid
      layer1_sm_nodes_nonempty hsm]
  exact hSM tid shape henv

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
/-- Faithful replicated boundary RMSNorm, with the generated singleton goal unchanged. -/
theorem recon_intermediateGoal_5332_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5332
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have h30 := Gather2Rel.of_initGoalHolds _ _ intermediateGoal_5330 5330 9625 9626
    [4096, 1024] [2048, 1024] rfl rfl rfl rfl rfl rfl (by decide)
    (recon_intermediateGoal_5330_distributed initSM initPM hSM hPM hInit)
  rcases l12_boundary_sm_facts with ⟨sn470, sn471, _, _, _, sweight, sprefix⟩
  rcases l12_boundary_pm_facts with
    ⟨pn1001, pn1002, pn1004, pn1008, _, _, _, pweight, pprefix⟩
  have sbridge : denoteGraphDistributedFaithful sm initSM 5330 =
      denoteGraphDistributed sm initSM 5330 :=
    denoteGraphDistributedFaithful_eq_distributed_of_prefix sm initSM 5330 472
      sprefix (faithful_nonempty_sm 472) (l12_boundary_sm_not_written 472 5330 (by decide))
  have pbridge0 : denoteGraphDistributedFaithful pm initPM 9625 =
      denoteGraphDistributed pm initPM 9625 :=
    denoteGraphDistributedFaithful_eq_distributed_of_prefix pm initPM 9625 1003
      pprefix (faithful_nonempty_pm 1003) (l12_boundary_pm_not_written 1003 9625 (by decide))
  have pbridge1 : denoteGraphDistributedFaithful pm initPM 9626 =
      denoteGraphDistributed pm initPM 9626 :=
    denoteGraphDistributedFaithful_eq_distributed_of_prefix pm initPM 9626 1003
      pprefix (faithful_nonempty_pm 1003) (l12_boundary_pm_not_written 1003 9626 (by decide))
  have s8007 : denoteGraphDistributedFaithful sm initSM 8007 =
      denoteGraphDistributedFaithful sm initSM 5330 := by
    have h := denoteGraphDistributedFaithful_reduce1 sm initSM 470
      { rank := 0, op := "OpName.FW_multiref", ins := [5330], outs := [8007, 8011], params := [2] }
      5330 8007 id (by native_decide) sn470 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
          (by decide) (by decide)]
        exact applyNode_fw_multiref2_first_out sm s 0 5330 8007 8011)
      (faithful_nonempty_sm 471) (l12_boundary_sm_not_written 471 8007 (by decide))
      (faithful_nonempty_sm 470) (l12_boundary_sm_not_written 470 5330 (by decide))
    simpa only [id_eq] using h
  have p14597 : denoteGraphDistributedFaithful pm initPM 14597 =
      denoteGraphDistributedFaithful pm initPM 9625 := by
    have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1001
      { rank := 0, op := "OpName.FW_multiref", ins := [9625], outs := [14597, 13257], params := [2] }
      9625 14597 id (by native_decide) pn1001 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
          (by decide) (by decide)]
        exact applyNode_fw_multiref2_first_out pm s 0 9625 14597 13257)
      (faithful_nonempty_pm 1002) (l12_boundary_pm_not_written 1002 14597 (by decide))
      (faithful_nonempty_pm 1001) (l12_boundary_pm_not_written 1001 9625 (by decide))
    simpa only [id_eq] using h
  have p14599 : denoteGraphDistributedFaithful pm initPM 14599 =
      denoteGraphDistributedFaithful pm initPM 9626 := by
    have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1002
      { rank := 1, op := "OpName.FW_multiref", ins := [9626], outs := [14599, 13258], params := [2] }
      9626 14599 id (by native_decide) pn1002 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
          (by decide) (by decide)]
        exact applyNode_fw_multiref2_first_out pm s 1 9626 14599 13258)
      (faithful_nonempty_pm 1003) (l12_boundary_pm_not_written 1003 14599 (by decide))
      (faithful_nonempty_pm 1002) (l12_boundary_pm_not_written 1002 9626 (by decide))
    simpa only [id_eq] using h
  have p11917 : denoteGraphDistributedFaithful pm initPM 11917 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm initPM 14597,
         denoteGraphDistributedFaithful pm initPM 14599] := by
    exact denoteGraphDistributedFaithful_reduce2 pm initPM 1004
      { rank := 0, op := "OpName.AllGatherPrim", ins := [14597, 14599], outs := [11917], params := [0] }
      14597 14599 11917 (fun a b => allGatherPrimDimN 0 2 0 [a, b])
      (by native_decide) pn1004 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
          (by decide) (by decide)]
        exact applyNode_allGatherPrimDimN_out_thm pm s 0 [14597, 14599] 11917 0)
      (faithful_nonempty_pm 1005) (l12_boundary_pm_not_written 1005 11917 (by decide))
      (faithful_nonempty_pm 1004) (l12_boundary_pm_not_written 1004 14597 (by decide))
      (l12_boundary_pm_not_written 1004 14599 (by decide))
  have hw := faithful_weight_eq initSM initPM hInit 5331 initGoal_5331
    (by native_decide) rfl rfl rfl rfl
    (fun n hn => (sweight n hn).1) (fun n hn => (pweight n hn).1)
  have rSM : denoteGraphDistributedFaithful sm initSM 5332 =
      fw_rms_norm (denoteGraphDistributedFaithful sm initSM 8007)
        (denoteGraphDistributedFaithful sm initSM 5331) := by
    exact denoteGraphDistributedFaithful_reduce2 sm initSM 471
      { rank := 0, op := "OpName.FW_rms_norm", ins := [8007, 5331], outs := [5332] }
      8007 5331 5332 fw_rms_norm (by native_decide) sn471 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
          (by decide) (by decide)]
        exact applyNode_fw_rms_norm_out_1p sm s 0 8007 5331 5332)
      (faithful_nonempty_sm 472) (l12_boundary_sm_not_written 472 5332 (by decide))
      (faithful_nonempty_sm 471) (l12_boundary_sm_not_written 471 8007 (by decide))
      (l12_boundary_sm_not_written 471 5331 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5332 =
      fw_rms_norm (denoteGraphDistributedFaithful pm initPM 11917)
        (denoteGraphDistributedFaithful pm initPM 5331) := by
    exact denoteGraphDistributedFaithful_reduce2 pm initPM 1008
      { rank := 1, op := "OpName.FW_rms_norm", ins := [11917, 5331], outs := [5332] }
      11917 5331 5332 fw_rms_norm (by native_decide) pn1008 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
          (by decide) (by decide)]
        exact applyNode_fw_rms_norm_out_1p pm s 1 11917 5331 5332)
      (faithful_nonempty_pm 1009) (l12_boundary_pm_not_written 1009 5332 (by decide))
      (faithful_nonempty_pm 1008) (l12_boundary_pm_not_written 1008 11917 (by decide))
      (l12_boundary_pm_not_written 1008 5331 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5332 =
      denoteGraphDistributedFaithful pm initPM 5332 := by
    rw [rSM, rPM, s8007, sbridge, h30.value, p11917, p14597, p14599,
      pbridge0, pbridge1, hw]
  have hs8007 : (denoteGraphDistributedFaithful sm initSM 8007).shape = [4096, 1024] := by
    rw [s8007, sbridge]
    exact h30.full_shape
  have hshape : (denoteGraphDistributedFaithful sm initSM 5332).shape = [4096, 1024] := by
    rw [rSM]
    exact fw_rms_norm_shape2 _ _ 4096 1024 hs8007
  exact wrap_1tp_gen _ _ intermediateGoal_5332 5332 [4096, 1024]
    rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
/-- Faithful replicated K projection at the L12 boundary. -/
theorem recon_intermediateGoal_5334_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5334
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have h32 := recon_intermediateGoal_5332_faithful initSM initPM hSM hPM hInit
  have hv32 := oneTp_valeq intermediateGoal_5332 _ _ 5332 rfl rfl rfl rfl h32
  have hs32 : (denoteGraphDistributedFaithful sm initSM 5332).shape = [4096, 1024] := by
    have h := h32.1
    simpa [intermediateGoal_5332] using h
  rcases l12_boundary_sm_facts with ⟨_, _, sn473, sn475, _, sweight, _⟩
  rcases l12_boundary_pm_facts with ⟨_, _, _, _, pn1012, pn1017, _, pweight, _⟩
  have s8015 : denoteGraphDistributedFaithful sm initSM 8015 =
      denoteGraphDistributedFaithful sm initSM 5332 := by
    have h := denoteGraphDistributedFaithful_reduce1 sm initSM 473
      { rank := 0, op := "OpName.FW_multiref", ins := [5332], outs := [8015, 8019], params := [2] }
      5332 8015 id (by native_decide) sn473 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_multiref2_first_out sm s 0 5332 8015 8019)
      (faithful_nonempty_sm 474) (l12_boundary_sm_not_written 474 8015 (by decide))
      (faithful_nonempty_sm 473) (l12_boundary_sm_not_written 473 5332 (by decide))
    simpa only [id_eq] using h
  have p15749 : denoteGraphDistributedFaithful pm initPM 15749 =
      denoteGraphDistributedFaithful pm initPM 5332 := by
    have h := denoteGraphDistributedFaithful_reduce1 pm initPM 1012
      { rank := 1, op := "OpName.FW_multiref", ins := [5332], outs := [15749, 15753], params := [2] }
      5332 15749 id (by native_decide) pn1012 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_multiref2_first_out pm s 1 5332 15749 15753)
      (faithful_nonempty_pm 1013) (l12_boundary_pm_not_written 1013 15749 (by decide))
      (faithful_nonempty_pm 1012) (l12_boundary_pm_not_written 1012 5332 (by decide))
    simpa only [id_eq] using h
  have hw := faithful_weight_eq initSM initPM hInit 5333 initGoal_5333
    (by native_decide) rfl rfl rfl rfl
    (fun n hn => (sweight n hn).2.1) (fun n hn => (pweight n hn).2.1)
  have hsw := faithful_weight_shape initSM hSM 5333 [4, 64, 1024]
    (by native_decide) (fun n hn => (sweight n hn).2.1)
  have rSM : denoteGraphDistributedFaithful sm initSM 5334 =
      fw_per_head_linear (denoteGraphDistributedFaithful sm initSM 8015)
        (denoteGraphDistributedFaithful sm initSM 5333) := by
    exact denoteGraphDistributedFaithful_reduce2 sm initSM 475 _ 8015 5333 5334
      fw_per_head_linear (by native_decide) sn475 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_per_head_mix_precision_linear_out sm s 0 8015 5333 5334 [])
      (faithful_nonempty_sm 476) (l12_boundary_sm_not_written 476 5334 (by decide))
      (faithful_nonempty_sm 475) (l12_boundary_sm_not_written 475 8015 (by decide)) (l12_boundary_sm_not_written 475 5333 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5334 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 15749)
        (denoteGraphDistributedFaithful pm initPM 5333) := by
    exact denoteGraphDistributedFaithful_reduce2 pm initPM 1017 _ 15749 5333 5334
      fw_per_head_linear (by native_decide) pn1017 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_per_head_mix_precision_linear_out pm s 1 15749 5333 5334 [])
      (faithful_nonempty_pm 1018) (l12_boundary_pm_not_written 1018 5334 (by decide))
      (faithful_nonempty_pm 1017) (l12_boundary_pm_not_written 1017 15749 (by decide)) (l12_boundary_pm_not_written 1017 5333 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5334 =
      denoteGraphDistributedFaithful pm initPM 5334 := by
    rw [rSM, rPM, s8015, p15749, hv32, hw]
  have hshape : (denoteGraphDistributedFaithful sm initSM 5334).shape = [4096, 4, 64] := by
    rw [rSM, s8015]
    exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64 hs32 hsw
  exact wrap_1tp_gen _ _ intermediateGoal_5334 5334 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
/-- Faithful replicated V projection at the L12 boundary. -/
theorem recon_intermediateGoal_5336_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_5336
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have h32 := recon_intermediateGoal_5332_faithful initSM initPM hSM hPM hInit
  have hv32 := oneTp_valeq intermediateGoal_5332 _ _ 5332 rfl rfl rfl rfl h32
  have hs32 : (denoteGraphDistributedFaithful sm initSM 5332).shape = [4096, 1024] := by
    have h := h32.1
    simpa [intermediateGoal_5332] using h
  rcases l12_boundary_sm_facts with ⟨_, _, sn473, _, sn476, sweight, _⟩
  rcases l12_boundary_pm_facts with ⟨_, _, _, _, pn1012, _, pn1018, pweight, _⟩
  have s8019 : denoteGraphDistributedFaithful sm initSM 8019 =
      denoteGraphDistributedFaithful sm initSM 5332 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 473 _ 5332 8019 (fun x => x)
      (by native_decide) sn473 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_multiref2_second_out' sm s 0 5332 8015 8019 (by decide))
      (faithful_nonempty_sm 474) (l12_boundary_sm_not_written 474 8019 (by decide))
      (faithful_nonempty_sm 473) (l12_boundary_sm_not_written 473 5332 (by decide))
  have p15753 : denoteGraphDistributedFaithful pm initPM 15753 =
      denoteGraphDistributedFaithful pm initPM 5332 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1012 _ 5332 15753 (fun x => x)
      (by native_decide) pn1012 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_multiref2_second_out' pm s 1 5332 15749 15753 (by decide))
      (faithful_nonempty_pm 1013) (l12_boundary_pm_not_written 1013 15753 (by decide))
      (faithful_nonempty_pm 1012) (l12_boundary_pm_not_written 1012 5332 (by decide))
  have hw := faithful_weight_eq initSM initPM hInit 5335 initGoal_5335
    (by native_decide) rfl rfl rfl rfl
    (fun n hn => (sweight n hn).2.2) (fun n hn => (pweight n hn).2.2)
  have hsw := faithful_weight_shape initSM hSM 5335 [4, 64, 1024]
    (by native_decide) (fun n hn => (sweight n hn).2.2)
  have rSM : denoteGraphDistributedFaithful sm initSM 5336 =
      fw_per_head_linear (denoteGraphDistributedFaithful sm initSM 8019)
        (denoteGraphDistributedFaithful sm initSM 5335) := by
    exact denoteGraphDistributedFaithful_reduce2 sm initSM 476 _ 8019 5335 5336
      fw_per_head_linear (by native_decide) sn476 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_per_head_mix_precision_linear_out sm s 0 8019 5335 5336 [])
      (faithful_nonempty_sm 477) (l12_boundary_sm_not_written 477 5336 (by decide))
      (faithful_nonempty_sm 476) (l12_boundary_sm_not_written 476 8019 (by decide)) (l12_boundary_sm_not_written 476 5335 (by decide))
  have rPM : denoteGraphDistributedFaithful pm initPM 5336 =
      fw_per_head_linear (denoteGraphDistributedFaithful pm initPM 15753)
        (denoteGraphDistributedFaithful pm initPM 5335) := by
    exact denoteGraphDistributedFaithful_reduce2 pm initPM 1018 _ 15753 5335 5336
      fw_per_head_linear (by native_decide) pn1018 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_per_head_mix_precision_linear_out pm s 1 15753 5335 5336 [])
      (faithful_nonempty_pm 1019) (l12_boundary_pm_not_written 1019 5336 (by decide))
      (faithful_nonempty_pm 1018) (l12_boundary_pm_not_written 1018 15753 (by decide)) (l12_boundary_pm_not_written 1018 5335 (by decide))
  have hval : denoteGraphDistributedFaithful sm initSM 5336 =
      denoteGraphDistributedFaithful pm initPM 5336 := by
    rw [rSM, rPM, s8019, p15753, hv32, hw]
  have hshape : (denoteGraphDistributedFaithful sm initSM 5336).shape = [4096, 4, 64] := by
    rw [rSM, s8019]
    exact fw_per_head_linear_shape_3d _ _ 4096 1024 4 64 hs32 hsw
  exact wrap_1tp_gen _ _ intermediateGoal_5336 5336 [4096, 4, 64]
    rfl rfl rfl rfl rfl rfl hval hshape

end
end TrainVerify.Denote.GeneratedPatterns
