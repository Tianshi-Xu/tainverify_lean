/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler
import denote.InputValueClasses
import denote.ZigzagKRelationWitness

open TrainVerify.Denote
namespace CPEntry
noncomputable section
def smGraph : GraphDecl where
  numRanks := 1
  nodes := [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [10, 90], outs := [20], params := [1, 0] }]
  replicaGroups := [{ logical := { cid := 0, mb := 0, irname := "FW_maybe_shuffle" }, members := [{ rank := 0, primaryOutTid := 20 }] }]
def smShapes : List (Tid × Shape) := [(10, [12, 2]), (90, [2]), (91, [2])]
def smInputValueClasses : List InputValueClass := [{ source := "cu", tids := [90, 91] }]
def pmGraph : GraphDecl where
  numRanks := 3
  nodes := [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }]
  replicaGroups := [{ logical := { cid := 0, mb := 0, irname := "FW_maybe_shuffle" }, members := [{ rank := 0, primaryOutTid := 200 }, { rank := 1, primaryOutTid := 201 }, { rank := 2, primaryOutTid := 202 }] }]
def pmShapes : List (Tid × Shape) := [(100, [4, 2]), (101, [4, 2]), (102, [4, 2]), (90, [2]), (91, [2])]
def pmInputValueClasses : List InputValueClass := [{ source := "cu", tids := [90, 91] }]
def initSM : Store := fun tid => if tid = 10 then TrainVerify.Denote.RelationCompiler.ZigzagKRelationWitness.full else TrainVerify.Denote.RelationCompiler.ZigzagKRelationWitness.cu
def initPM : Store := fun tid => if tid = 100 then TrainVerify.Denote.RelationCompiler.ZigzagKRelationWitness.source 0 else if tid = 101 then TrainVerify.Denote.RelationCompiler.ZigzagKRelationWitness.source 1 else if tid = 102 then TrainVerify.Denote.RelationCompiler.ZigzagKRelationWitness.source 2 else TrainVerify.Denote.RelationCompiler.ZigzagKRelationWitness.cu
theorem packed : ZigzagCollective.PackedCuSeqlensWF (TrainVerify.Denote.RelationCompiler.ZigzagKRelationWitness.cu) 12 3 := by
  have h := TrainVerify.Denote.RelationCompiler.ZigzagKRelationWitness.cu_wf
  refine ⟨by decide, TrainVerify.Denote.RelationCompiler.ZigzagKRelationWitness.decode_cu, h.cu_starts_zero, h.cu_has_endpoint, h.monotone, h.divisible, ?_⟩
  rw [TrainVerify.Denote.RelationCompiler.ZigzagKRelationWitness.decode_cu]
  rfl
end
end CPEntry


open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.CPEntryProof

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_000000 : RelationFact :=
  .sharded 10 [100, 101, 102] 0 [12, 2] [4, 2]

private def fact_000001 : RelationFact :=
  .zigzagK 20 [200, 201, 202] 90 [12, 2] [4, 2]

private def authority_cross_metadata_eq_90_90 : RelationFact :=
  .tensorEq .sm 90 .pm 90

private def authority_packed_cu_000000 : RelationFact :=
  .packedCu .pm 91 12 3

private def authority_pm_metadata_eq_000000_90 : RelationFact :=
  .tensorEq .pm 90 .pm 91

private def anchor_sm_shape_10 : RelationFact :=
  .tensorShape .sm 10 [12, 2]

private def state_000000 : RelationState where
  facts := [anchor_sm_shape_10, authority_cross_metadata_eq_90_90, authority_packed_cu_000000, authority_pm_metadata_eq_000000_90, fact_000000]
  nonempty := by decide

private def state_000001 : RelationState where
  facts := [anchor_sm_shape_10, fact_000001]
  nonempty := by decide

private def segment_000000 :
    ClosedDepSegmentCertificate CPEntry.smGraph CPEntry.pmGraph state_000000 state_000001 where
  smNodes := [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [10, 90], outs := [20], params := [1, 0] }]
  pmNodes := [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }]
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [10, 90], outs := [20], params := [1, 0] }]
    let pmNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }]
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful CPEntry.smGraph) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore
    have hframe : state_000000.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hSource : fact_000000.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 10) [pmStore 100, pmStore 101, pmStore 102] 0 [12, 2] [4, 2] at hSource
    have hPacked : authority_packed_cu_000000.Holds smStore pmStore := hstate _ (by native_decide)
    have hAlias : authority_pm_metadata_eq_000000_90.Holds smStore pmStore := hstate _ (by native_decide)
    change ZigzagCollective.PackedCuSeqlensWF (pmStore 91) 12 3 at hPacked
    change pmStore 90 = pmStore 91 at hAlias
    have hPackedActual : ZigzagCollective.PackedCuSeqlensWF (pmStore 90) 12 3 := by
      rw [hAlias]
      exact hPacked
    have hCu : ZigzagCollective.ZigzagCuWF (decodeCuSeqlens (pmStore 90)) [pmStore 100, pmStore 101, pmStore 102] 3 := by
      apply hPackedActual.toZigzagCuWF rfl
      · intro x hx
        rw [hSource.shard_shapes x hx]
        decide
      · intro x hx
        change x.shape = (pmStore 100).shape
        rw [hSource.shard_shapes x hx, hSource.shard_shapes (pmStore 100) (by simp)]
      · change (pmStore 100).shape.getD 0 0 * 3 = 12
        rw [hSource.shard_shapes (pmStore 100) (by simp)]
        rfl
    have core := ZigzagKRel.of_sharded hSource hCu
    have hSm : smFinal 20 = ZigzagCollective.fw_maybe_shuffle_collective [smStore 10] (decodeCuSeqlens (smStore 90)) 1 0 := by
      have hw : smFinal 20 = ZigzagCollective.fw_maybe_shuffle_collective [([].foldl (applyNodeDistributedFaithful CPEntry.smGraph) smStore) 10] (decodeCuSeqlens (([].foldl (applyNodeDistributedFaithful CPEntry.smGraph) smStore) 90)) 1 0 := by
        simpa [smFinal, smNodes] using
          (foldl_faithful_middle_writer CPEntry.smGraph smStore [] [] { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [10, 90], outs := [20], params := [1, 0] } 20
            (fun t => ZigzagCollective.fw_maybe_shuffle_collective [t 10] (decodeCuSeqlens (t 90)) 1 0) (by
              intro t
              rw [applyNodeDistributedFaithful_shuffle_out]
              unfold applyNodeFaithfulShuffleValue
              rw [show CPEntry.smGraph.replicaBuddies { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [10, 90], outs := [20], params := [1, 0] } = [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [10, 90], outs := [20], params := [1, 0] }] by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.smGraph [] smStore 10 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.smGraph [] smStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hPm0 : pmFinal 200 = ZigzagCollective.fw_maybe_shuffle_collective [pmStore 100, pmStore 101, pmStore 102] (decodeCuSeqlens (pmStore 90)) 3 0 := by
      have hw : pmFinal 200 = ZigzagCollective.fw_maybe_shuffle_collective [([].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 100, ([].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 101, ([].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 102] (decodeCuSeqlens (([].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 90)) 3 0 := by
        simpa [pmFinal, pmNodes] using
          (foldl_faithful_middle_writer CPEntry.pmGraph pmStore [] [{ rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }] { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] } 200
            (fun t => ZigzagCollective.fw_maybe_shuffle_collective [t 100, t 101, t 102] (decodeCuSeqlens (t 90)) 3 0) (by
              intro t
              rw [applyNodeDistributedFaithful_shuffle_out]
              unfold applyNodeFaithfulShuffleValue
              rw [show CPEntry.pmGraph.replicaBuddies { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] } = [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }] by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [] pmStore 100 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [] pmStore 101 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [] pmStore 102 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [] pmStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hPm1 : pmFinal 201 = ZigzagCollective.fw_maybe_shuffle_collective [pmStore 100, pmStore 101, pmStore 102] (decodeCuSeqlens (pmStore 90)) 3 1 := by
      have hw : pmFinal 201 = ZigzagCollective.fw_maybe_shuffle_collective [([{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 100, ([{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 101, ([{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 102] (decodeCuSeqlens (([{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 90)) 3 1 := by
        simpa [pmFinal, pmNodes] using
          (foldl_faithful_middle_writer CPEntry.pmGraph pmStore [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }] [{ rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }] { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] } 201
            (fun t => ZigzagCollective.fw_maybe_shuffle_collective [t 100, t 101, t 102] (decodeCuSeqlens (t 90)) 3 1) (by
              intro t
              rw [applyNodeDistributedFaithful_shuffle_out]
              unfold applyNodeFaithfulShuffleValue
              rw [show CPEntry.pmGraph.replicaBuddies { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] } = [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }] by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }] pmStore 100 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }] pmStore 101 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }] pmStore 102 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }] pmStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hPm2 : pmFinal 202 = ZigzagCollective.fw_maybe_shuffle_collective [pmStore 100, pmStore 101, pmStore 102] (decodeCuSeqlens (pmStore 90)) 3 2 := by
      have hw : pmFinal 202 = ZigzagCollective.fw_maybe_shuffle_collective [([{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 100, ([{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 101, ([{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 102] (decodeCuSeqlens (([{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 90)) 3 2 := by
        simpa [pmFinal, pmNodes] using
          (foldl_faithful_middle_writer CPEntry.pmGraph pmStore [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] }] [] { rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] } 202
            (fun t => ZigzagCollective.fw_maybe_shuffle_collective [t 100, t 101, t 102] (decodeCuSeqlens (t 90)) 3 2) (by
              intro t
              rw [applyNodeDistributedFaithful_shuffle_out]
              unfold applyNodeFaithfulShuffleValue
              rw [show CPEntry.pmGraph.replicaBuddies { rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] } = [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }] by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] }] pmStore 100 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] }] pmStore 101 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] }] pmStore 102 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] }] pmStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hSmValue : smFinal 20 = smStore 10 := by
      simpa [ZigzagCollective.fw_maybe_shuffle_collective] using hSm
    have hMetadataFinal : pmFinal 90 = pmStore 90 :=
      foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph pmNodes pmStore 90 (by native_decide) (by native_decide)
    have hOut : fact_000001.Holds smFinal pmFinal := by
      change ZigzagKRel (smFinal 20) [pmFinal 200, pmFinal 201, pmFinal 202] (pmFinal 90) [12, 2] [4, 2]
      rw [hSmValue, hPm0, hPm1, hPm2, hMetadataFinal]
      exact core
    intro fact hfact
    have covered : fact ∈ [fact_000001] ++ state_000000.facts := by
      exact (show state_000001.facts ⊆ [fact_000001] ++ state_000000.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | hold
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hOut
    · exact hframe fact hold

open CPEntry
theorem inhabitedInput : state_000000.Holds CPEntry.initSM CPEntry.initPM := by
  intro fact hfact
  change fact ∈ [anchor_sm_shape_10, authority_cross_metadata_eq_90_90, authority_packed_cu_000000, authority_pm_metadata_eq_000000_90, fact_000000] at hfact
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfact
  rcases hfact with rfl | rfl | rfl | rfl | rfl
  · exact TrainVerify.Denote.RelationCompiler.ZigzagKRelationWitness.sharded_input.full_shape
  · rfl
  · exact CPEntry.packed
  · rfl
  · exact TrainVerify.Denote.RelationCompiler.ZigzagKRelationWitness.sharded_input
theorem inhabitedOutput : fact_000001.Holds
    (smGraph.nodes.foldl (applyNodeDistributedFaithful smGraph) initSM)
    (pmGraph.nodes.foldl (applyNodeDistributedFaithful pmGraph) initPM) := by
  have h := segment_000000.sound CPEntry.initSM CPEntry.initPM inhabitedInput
  exact h fact_000001 (by native_decide)
#print axioms inhabitedOutput
end
end TrainVerify.Denote.CPEntryProof
