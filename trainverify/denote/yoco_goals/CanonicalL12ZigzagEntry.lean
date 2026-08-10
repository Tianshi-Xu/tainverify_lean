/- Canonical Goal 1: exact faithful ordinary-cache to L12 zigzag entry. -/
import denote.yoco_goals.Goal1ExternalToCacheComposition
import denote.yoco_goals.ZigzagLayoutRel

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def cL12ESmMulti : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [5595], outs := [8368, 8372], params := [2] }
private def cL12EPmMulti0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [9722], outs := [15822, 15826], params := [2] }
private def cL12EPmMulti1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [9723], outs := [15830, 15834], params := [2] }
private def cL12ESmShuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [8372, 5602], outs := [5603], params := [1, 0] }
private def cL12EPmShuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [15826, 5602], outs := [9750], params := [2, 0] }
private def cL12EPmShuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [15834, 5602], outs := [9751], params := [2, 1] }

private theorem cL12E_apply_multiref_second (g : GraphDecl) (s : Store)
    (rank xTid t0 t1 : Nat) (hne : t0 ≠ t1) :
    applyNode g s
      { rank := rank, op := "OpName.FW_multiref", ins := [xTid],
        outs := [t0, t1], params := [2] } t1 = s xTid := by
  unfold applyNode
  rw [show ([xTid] : List Tid).map s = [s xTid] from rfl, evalOp_fw_multiref]
  change storeSet s ([t0, t1].zip (List.replicate 2 (s xTid))) t1 = _
  unfold storeSet
  simp [List.zip, List.zipWith, List.replicate, List.find?, hne]

private theorem cL12E_red_sm8372 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 8372 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 5595 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 initSM 470 cL12ESmMulti
    5595 8372 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL12ESmMulti
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL12E_apply_multiref_second sm_goal_1 s 0 5595 8368 8372 (by decide)

private theorem cL12E_red_pm15826 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15826 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9722 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1040 cL12EPmMulti0
    9722 15826 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL12EPmMulti0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL12E_apply_multiref_second pm_goal_1 s 0 9722 15822 15826 (by decide)

private theorem cL12E_red_pm15834 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 15834 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 9723 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 initPM 1041 cL12EPmMulti1
    9723 15834 (fun x => x) (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL12EPmMulti1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact cL12E_apply_multiref_second pm_goal_1 s 1 9723 15830 15834 (by decide)

private theorem cL12E_red_sm5603 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5603 =
      denoteGraphDistributedFaithful sm_goal_1 initSM 8372 := by
  rw [denoteGraphDistributedFaithful_node_core sm_goal_1 initSM 472 cL12ESmShuffle 5603
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)]
  unfold cL12ESmShuffle
  rw [applyNodeDistributedFaithful_shuffle_out]
  rw [← denoteGraphDistributedFaithful_prefix_read sm_goal_1 initSM 472 8372
    (by native_decide) (by native_decide)]
  apply applyNodeFaithfulShuffleValue_cpSize_one
  · native_decide
  · rfl
  · rfl

private theorem cL12E_red_pm9750 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9750 =
      fw_maybe_shuffle_collective
        [denoteGraphDistributedFaithful pm_goal_1 initPM 15826,
         denoteGraphDistributedFaithful pm_goal_1 initPM 15834]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_1 initPM 5602)) 2 0 := by
  refine denoteGraphDistributedFaithful_reduce3 pm_goal_1 initPM 1043 cL12EPmShuffle0
    15826 15834 5602 9750
    (fun a b cu => fw_maybe_shuffle_collective [a, b] (decodeCuSeqlens cu) 2 0)
    (by native_decide) (by native_decide) ?_ (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL12EPmShuffle0
  rw [applyNodeDistributedFaithful_shuffle_out]
  unfold applyNodeFaithfulShuffleValue
  rw [show pm_goal_1.replicaBuddies
    { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [15826, 5602],
      outs := [9750], params := [2, 0] } = [cL12EPmShuffle0, cL12EPmShuffle1] by
        native_decide]
  unfold cL12EPmShuffle0 cL12EPmShuffle1
  rfl

private theorem cL12E_red_pm9751 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_1 initPM 9751 =
      fw_maybe_shuffle_collective
        [denoteGraphDistributedFaithful pm_goal_1 initPM 15826,
         denoteGraphDistributedFaithful pm_goal_1 initPM 15834]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_1 initPM 5602)) 2 1 := by
  refine denoteGraphDistributedFaithful_reduce3 pm_goal_1 initPM 1045 cL12EPmShuffle1
    15826 15834 5602 9751
    (fun a b cu => fw_maybe_shuffle_collective [a, b] (decodeCuSeqlens cu) 2 1)
    (by native_decide) (by native_decide) ?_ (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL12EPmShuffle1
  rw [applyNodeDistributedFaithful_shuffle_out]
  unfold applyNodeFaithfulShuffleValue
  rw [show pm_goal_1.replicaBuddies
    { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [15834, 5602],
      outs := [9751], params := [2, 1] } = [cL12EPmShuffle0, cL12EPmShuffle1] by
        native_decide]
  unfold cL12EPmShuffle0 cL12EPmShuffle1
  rfl

private theorem cL12E_final_pm (initPM : Store) (tid : Tid)
    (h : tid ∈ [5602, 6252]) :
    denoteGraphDistributedFaithful pm_goal_1 initPM tid = initPM tid := by
  unfold denoteGraphDistributedFaithful
  refine foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
    initPM tid (by native_decide) ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> native_decide

private theorem cL12E_source0_shape (initSM initPM : Store)
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024]) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 15826).shape = [2048, 1024] := by
  rw [cL12E_red_pm15826 initPM]
  exact hCache.shard0_shape

private theorem cL12E_source1_shape (initSM initPM : Store)
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024]) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 15834).shape = [2048, 1024] := by
  rw [cL12E_red_pm15834 initPM]
  exact hCache.shard1_shape

private theorem cL12E_sources_shape (initSM initPM : Store)
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024]) :
    ∀ x ∈ [denoteGraphDistributedFaithful pm_goal_1 initPM 15826,
      denoteGraphDistributedFaithful pm_goal_1 initPM 15834],
      x.shape = [2048, 1024] := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact cL12E_source0_shape initSM initPM hCache
  · exact cL12E_source1_shape initSM initPM hCache

private theorem cL12E_sources_nonempty (initSM initPM : Store)
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024]) :
    ∀ x ∈ [denoteGraphDistributedFaithful pm_goal_1 initPM 15826,
      denoteGraphDistributedFaithful pm_goal_1 initPM 15834], x.shape ≠ [] := by
  intro x hx
  rw [cL12E_sources_shape initSM initPM hCache x hx]
  decide

private theorem cL12E_sources_same_shape (initSM initPM : Store)
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024]) :
    ∀ x ∈ [denoteGraphDistributedFaithful pm_goal_1 initPM 15826,
      denoteGraphDistributedFaithful pm_goal_1 initPM 15834],
      x.shape = (denoteGraphDistributedFaithful pm_goal_1 initPM 15826).shape := by
  intro x hx
  rw [cL12E_source0_shape initSM initPM hCache]
  exact cL12E_sources_shape initSM initPM hCache x hx

private theorem cL12E_sources_endpoint (initSM initPM : Store)
    (hPacked : PackedCuSeqlensWF (initPM 6252) 4096 2)
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024]) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM 15826).shape.getD 0 0 * 2 =
      listLast! (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)) := by
  rw [cL12E_source0_shape initSM initPM hCache,
    cL12E_final_pm initPM 6252 (by decide), hPacked.endpoint]
  decide

private theorem cL12E_sources_wf (initSM initPM : Store)
    (hPacked : PackedCuSeqlensWF (initPM 6252) 4096 2)
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024]) :
    ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_1 initPM 6252))
      [denoteGraphDistributedFaithful pm_goal_1 initPM 15826,
       denoteGraphDistributedFaithful pm_goal_1 initPM 15834] 2 := by
  refine ⟨hPacked.cp_pos, rfl, ?_, hPacked.has_endpoint,
    hPacked.monotone, hPacked.divisible, ?_, ?_, ?_⟩
  · rw [cL12E_final_pm initPM 6252 (by decide)]
    exact hPacked.starts_zero
  · exact cL12E_sources_nonempty initSM initPM hCache
  · simpa only [List.getD_cons_zero] using
      cL12E_sources_same_shape initSM initPM hCache
  · simpa only [List.getD_cons_zero] using
      cL12E_sources_endpoint initSM initPM hPacked hCache

private theorem cL12E_full_value (initSM initPM : Store)
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024]) :
    denoteGraphDistributedFaithful sm_goal_1 initSM 5603 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_1 initPM 15826,
         denoteGraphDistributedFaithful pm_goal_1 initPM 15834] := by
  rw [cL12E_red_sm5603 initSM, cL12E_red_sm8372 initSM,
    cL12E_red_pm15826 initPM, cL12E_red_pm15834 initPM]
  exact hCache.value

private theorem cL12E_full_shape (initSM initPM : Store)
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024]) :
    (denoteGraphDistributedFaithful sm_goal_1 initSM 5603).shape = [4096, 1024] := by
  rw [cL12E_red_sm5603 initSM, cL12E_red_sm8372 initSM]
  exact hCache.full_shape

/-- Exact Goal-1 L12 shuffle entry from the real L11/cache output.  Its only
non-shape premise is the external packed-cu/value-class contract; no relation
between computed intermediates is assumed. -/
theorem canonical_l12_zigzag_entry_from_cache
    (initSM initPM : Store)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hPacked : PackedCuSeqlensWF (initPM 6252) 4096 2)
    (hCache : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9723)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5603)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9750)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9751)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hcuInit : initPM 5602 = initPM 6252 :=
    hValues.2.eq_of_mem
      (c := pmInputValueClasses[1]'(by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hcu : denoteGraphDistributedFaithful pm_goal_1 initPM 5602 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252 := by
    rw [cL12E_final_pm initPM 5602 (by decide),
      cL12E_final_pm initPM 6252 (by decide), hcuInit]
  have hwf := cL12E_sources_wf initSM initPM hPacked hCache
  apply Zigzag2Rel.of_sources
    (denoteGraphDistributedFaithful pm_goal_1 initPM 15826)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 15834)
  · exact cL12E_full_value initSM initPM hCache
  · rw [cL12E_red_pm9750 initPM, hcu]
  · rw [cL12E_red_pm9751 initPM, hcu]
  · exact cL12E_full_shape initSM initPM hCache
  · exact cL12E_source0_shape initSM initPM hCache
  · exact cL12E_source1_shape initSM initPM hCache
  · exact hwf

/-- An ancestry-closed L12 entry: the ordinary cache relation is reconstructed
internally from the exact external/init contracts. -/
theorem goal1_external_to_l12_zigzag_entry
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_1InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM)
    (hContract : Goal1AncestryInputContract initSM initPM) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 5603)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9750)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9751)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hCache := goal1_external_to_cache_faithful_composition initSM initPM hSM hPM hInit
  exact canonical_l12_zigzag_entry_from_cache initSM initPM
    ⟨hContract.1, hContract.2.1⟩ hContract.2.2 hCache

#print axioms canonical_l12_zigzag_entry_from_cache
#print axioms goal1_external_to_l12_zigzag_entry

end
end TrainVerify.Denote.GeneratedPatterns
