/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler
import denote.InputValueClasses
import denote.ZigzagKRelationWitness
import denote.ZigzagKExit

open TrainVerify.Denote
namespace CPEntry
noncomputable section
def smGraph : GraphDecl where
  numRanks := 1
  nodes := [{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [10, 90], outs := [20], params := [1, 0] }, { rank := 0, op := "OpName.BW_maybe_shuffle", ins := [20, 90], outs := [30], params := [1, 0] }]
  replicaGroups := [{ logical := { cid := 0, mb := 0, irname := "BW_maybe_unshuffle" }, members := [{ rank := 0, primaryOutTid := 20 }] }, { logical := { cid := 1, mb := 0, irname := "BW_maybe_shuffle" }, members := [{ rank := 0, primaryOutTid := 30 }] }]
def smShapes : List (Tid × Shape) := [(10, [12, 2]), (90, [2]), (91, [2])]
def smInputValueClasses : List InputValueClass := [{ source := "cu", tids := [90, 91] }]
def pmGraph : GraphDecl where
  numRanks := 3
  nodes := [{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.BW_maybe_unshuffle", ins := [101, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.BW_maybe_unshuffle", ins := [102, 90], outs := [202], params := [3, 2] }, { rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] }, { rank := 0, op := "OpName.BW_maybe_shuffle", ins := [200, 90], outs := [300], params := [3, 0] }, { rank := 1, op := "OpName.BW_maybe_shuffle", ins := [201, 90], outs := [301], params := [3, 1] }]
  replicaGroups := [{ logical := { cid := 0, mb := 0, irname := "BW_maybe_unshuffle" }, members := [{ rank := 0, primaryOutTid := 200 }, { rank := 1, primaryOutTid := 201 }, { rank := 2, primaryOutTid := 202 }] }, { logical := { cid := 1, mb := 0, irname := "BW_maybe_shuffle" }, members := [{ rank := 0, primaryOutTid := 300 }, { rank := 1, primaryOutTid := 301 }, { rank := 2, primaryOutTid := 302 }] }]
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

namespace CPEntry
noncomputable section
def smGraphInitEnv : ShapeEnv := shapeEnvOfList smShapes
def pmGraphInitEnv : ShapeEnv := shapeEnvOfList pmShapes
def initGoal_10 : LineageGoal := { ts := 10, tsShape := [12, 2], tps := [{ rank := 0, tid := 100 }, { rank := 1, tid := 101 }, { rank := 2, tid := 102 }], tpShapes := [[4, 2], [4, 2], [4, 2]], gatherDim := 0 }
def initGoal_90 : LineageGoal := { ts := 90, tsShape := [2], tps := [{ rank := 0, tid := 90 }], tpShapes := [[2]], gatherDim := 0 }
def initGoal_91 : LineageGoal := { ts := 91, tsShape := [2], tps := [{ rank := 0, tid := 91 }], tpShapes := [[2]], gatherDim := 0 }
def initGoals : List LineageGoal := [initGoal_10, initGoal_90, initGoal_91]
def exitGoal : LineageGoal := { ts := 30, tsShape := [12, 2], tps := [{ rank := 0, tid := 300 }, { rank := 1, tid := 301 }, { rank := 2, tid := 302 }], tpShapes := [[4, 2], [4, 2], [4, 2]], gatherDim := 0 }
def externalContract (initSM initPM : Store) : Prop :=
  InputValueClassesHold smInputValueClasses initSM ∧
  InputValueClassesHold pmInputValueClasses initPM ∧
  ZigzagCollective.PackedCuSeqlensWF (initPM 91) 12 3
def exitStatement : Prop :=
  CoarseLineageHoldsWithInitDistributedFaithfulWithContract
    smGraph pmGraph exitGoal smGraphInitEnv pmGraphInitEnv initGoals externalContract
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
  .sharded 30 [300, 301, 302] 0 [12, 2] [4, 2]

private def fact_000002 : RelationFact :=
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
  facts := [anchor_sm_shape_10, authority_cross_metadata_eq_90_90, authority_packed_cu_000000, authority_pm_metadata_eq_000000_90, fact_000002]
  nonempty := by decide

private def state_000002 : RelationState where
  facts := [anchor_sm_shape_10, fact_000001, fact_000002]
  nonempty := by decide

private def segment_000000 :
    ClosedDepSegmentCertificate CPEntry.smGraph CPEntry.pmGraph state_000000 state_000001 where
  smNodes := [{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [10, 90], outs := [20], params := [1, 0] }]
  pmNodes := [{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.BW_maybe_unshuffle", ins := [101, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.BW_maybe_unshuffle", ins := [102, 90], outs := [202], params := [3, 2] }]
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [10, 90], outs := [20], params := [1, 0] }]
    let pmNodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.BW_maybe_unshuffle", ins := [101, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.BW_maybe_unshuffle", ins := [102, 90], outs := [202], params := [3, 2] }]
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
          (foldl_faithful_middle_writer CPEntry.smGraph smStore [] [] { rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [10, 90], outs := [20], params := [1, 0] } 20
            (fun t => ZigzagCollective.fw_maybe_shuffle_collective [t 10] (decodeCuSeqlens (t 90)) 1 0) (by
              intro t
              rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
              rw [applyNodeDistributed_bw_maybe_unshuffle_out]
              unfold applyNodeBWMaybeUnshuffleValue
              rw [ZigzagCollective.bw_maybe_unshuffle_collective_eq_fw_shuffle]
              rw [show CPEntry.smGraph.replicaBuddies { rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [10, 90], outs := [20], params := [1, 0] } = [{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [10, 90], outs := [20], params := [1, 0] }] by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.smGraph [] smStore 10 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.smGraph [] smStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hPm0 : pmFinal 200 = ZigzagCollective.fw_maybe_shuffle_collective [pmStore 100, pmStore 101, pmStore 102] (decodeCuSeqlens (pmStore 90)) 3 0 := by
      have hw : pmFinal 200 = ZigzagCollective.fw_maybe_shuffle_collective [([].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 100, ([].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 101, ([].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 102] (decodeCuSeqlens (([].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 90)) 3 0 := by
        simpa [pmFinal, pmNodes] using
          (foldl_faithful_middle_writer CPEntry.pmGraph pmStore [] [{ rank := 1, op := "OpName.BW_maybe_unshuffle", ins := [101, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.BW_maybe_unshuffle", ins := [102, 90], outs := [202], params := [3, 2] }] { rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] } 200
            (fun t => ZigzagCollective.fw_maybe_shuffle_collective [t 100, t 101, t 102] (decodeCuSeqlens (t 90)) 3 0) (by
              intro t
              rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
              rw [applyNodeDistributed_bw_maybe_unshuffle_out]
              unfold applyNodeBWMaybeUnshuffleValue
              rw [ZigzagCollective.bw_maybe_unshuffle_collective_eq_fw_shuffle]
              rw [show CPEntry.pmGraph.replicaBuddies { rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] } = [{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.BW_maybe_unshuffle", ins := [101, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.BW_maybe_unshuffle", ins := [102, 90], outs := [202], params := [3, 2] }] by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [] pmStore 100 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [] pmStore 101 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [] pmStore 102 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [] pmStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hPm1 : pmFinal 201 = ZigzagCollective.fw_maybe_shuffle_collective [pmStore 100, pmStore 101, pmStore 102] (decodeCuSeqlens (pmStore 90)) 3 1 := by
      have hw : pmFinal 201 = ZigzagCollective.fw_maybe_shuffle_collective [([{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 100, ([{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 101, ([{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 102] (decodeCuSeqlens (([{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 90)) 3 1 := by
        simpa [pmFinal, pmNodes] using
          (foldl_faithful_middle_writer CPEntry.pmGraph pmStore [{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] }] [{ rank := 2, op := "OpName.BW_maybe_unshuffle", ins := [102, 90], outs := [202], params := [3, 2] }] { rank := 1, op := "OpName.BW_maybe_unshuffle", ins := [101, 90], outs := [201], params := [3, 1] } 201
            (fun t => ZigzagCollective.fw_maybe_shuffle_collective [t 100, t 101, t 102] (decodeCuSeqlens (t 90)) 3 1) (by
              intro t
              rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
              rw [applyNodeDistributed_bw_maybe_unshuffle_out]
              unfold applyNodeBWMaybeUnshuffleValue
              rw [ZigzagCollective.bw_maybe_unshuffle_collective_eq_fw_shuffle]
              rw [show CPEntry.pmGraph.replicaBuddies { rank := 1, op := "OpName.BW_maybe_unshuffle", ins := [101, 90], outs := [201], params := [3, 1] } = [{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.BW_maybe_unshuffle", ins := [101, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.BW_maybe_unshuffle", ins := [102, 90], outs := [202], params := [3, 2] }] by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] }] pmStore 100 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] }] pmStore 101 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] }] pmStore 102 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] }] pmStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hPm2 : pmFinal 202 = ZigzagCollective.fw_maybe_shuffle_collective [pmStore 100, pmStore 101, pmStore 102] (decodeCuSeqlens (pmStore 90)) 3 2 := by
      have hw : pmFinal 202 = ZigzagCollective.fw_maybe_shuffle_collective [([{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.BW_maybe_unshuffle", ins := [101, 90], outs := [201], params := [3, 1] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 100, ([{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.BW_maybe_unshuffle", ins := [101, 90], outs := [201], params := [3, 1] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 101, ([{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.BW_maybe_unshuffle", ins := [101, 90], outs := [201], params := [3, 1] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 102] (decodeCuSeqlens (([{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.BW_maybe_unshuffle", ins := [101, 90], outs := [201], params := [3, 1] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 90)) 3 2 := by
        simpa [pmFinal, pmNodes] using
          (foldl_faithful_middle_writer CPEntry.pmGraph pmStore [{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.BW_maybe_unshuffle", ins := [101, 90], outs := [201], params := [3, 1] }] [] { rank := 2, op := "OpName.BW_maybe_unshuffle", ins := [102, 90], outs := [202], params := [3, 2] } 202
            (fun t => ZigzagCollective.fw_maybe_shuffle_collective [t 100, t 101, t 102] (decodeCuSeqlens (t 90)) 3 2) (by
              intro t
              rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
              rw [applyNodeDistributed_bw_maybe_unshuffle_out]
              unfold applyNodeBWMaybeUnshuffleValue
              rw [ZigzagCollective.bw_maybe_unshuffle_collective_eq_fw_shuffle]
              rw [show CPEntry.pmGraph.replicaBuddies { rank := 2, op := "OpName.BW_maybe_unshuffle", ins := [102, 90], outs := [202], params := [3, 2] } = [{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.BW_maybe_unshuffle", ins := [101, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.BW_maybe_unshuffle", ins := [102, 90], outs := [202], params := [3, 2] }] by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.BW_maybe_unshuffle", ins := [101, 90], outs := [201], params := [3, 1] }] pmStore 100 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.BW_maybe_unshuffle", ins := [101, 90], outs := [201], params := [3, 1] }] pmStore 101 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.BW_maybe_unshuffle", ins := [101, 90], outs := [201], params := [3, 1] }] pmStore 102 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 0, op := "OpName.BW_maybe_unshuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.BW_maybe_unshuffle", ins := [101, 90], outs := [201], params := [3, 1] }] pmStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hSmValue : smFinal 20 = smStore 10 := by
      simpa [ZigzagCollective.fw_maybe_shuffle_collective] using hSm
    have hMetadataFinal : pmFinal 90 = pmStore 90 :=
      foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph pmNodes pmStore 90 (by native_decide) (by native_decide)
    have hOut : fact_000002.Holds smFinal pmFinal := by
      change ZigzagKRel (smFinal 20) [pmFinal 200, pmFinal 201, pmFinal 202] (pmFinal 90) [12, 2] [4, 2]
      rw [hSmValue, hPm0, hPm1, hPm2, hMetadataFinal]
      exact core
    intro fact hfact
    have covered : fact ∈ [fact_000002] ++ state_000000.facts := by
      exact (show state_000001.facts ⊆ [fact_000002] ++ state_000000.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | hold
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hOut
    · exact hframe fact hold

private def segment_000001 :
    ClosedDepSegmentCertificate CPEntry.smGraph CPEntry.pmGraph state_000001 state_000002 where
  smNodes := [{ rank := 0, op := "OpName.BW_maybe_shuffle", ins := [20, 90], outs := [30], params := [1, 0] }]
  pmNodes := [{ rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] }, { rank := 0, op := "OpName.BW_maybe_shuffle", ins := [200, 90], outs := [300], params := [3, 0] }, { rank := 1, op := "OpName.BW_maybe_shuffle", ins := [201, 90], outs := [301], params := [3, 1] }]
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := [{ rank := 0, op := "OpName.BW_maybe_shuffle", ins := [20, 90], outs := [30], params := [1, 0] }]
    let pmNodes : List NodeDecl := [{ rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] }, { rank := 0, op := "OpName.BW_maybe_shuffle", ins := [200, 90], outs := [300], params := [3, 0] }, { rank := 1, op := "OpName.BW_maybe_shuffle", ins := [201, 90], outs := [301], params := [3, 1] }]
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful CPEntry.smGraph) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore
    have hframe : state_000001.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hSource : fact_000002.Holds smStore pmStore := hstate _ (by native_decide)
    change ZigzagKRel (smStore 20) [pmStore 200, pmStore 201, pmStore 202] (pmStore 90) [12, 2] [4, 2] at hSource
    have hPacked : authority_packed_cu_000000.Holds smStore pmStore := hstate _ (by native_decide)
    have hAlias : authority_pm_metadata_eq_000000_90.Holds smStore pmStore := hstate _ (by native_decide)
    change ZigzagCollective.PackedCuSeqlensWF (pmStore 91) 12 3 at hPacked
    change pmStore 90 = pmStore 91 at hAlias
    have hPackedActual : ZigzagCollective.PackedCuSeqlensWF (pmStore 90) 12 3 := by
      rw [hAlias]
      exact hPacked
    have hDecode : decodeCuSeqlens (pmStore 90) = [0, 3 * 4] := hPackedActual.decoded_single
    have core := ZigzagKRel.to_sharded_unshuffle_single (d := 2) hSource (by decide) hDecode
    have hSm : smFinal 30 = ZigzagCollective.fw_maybe_unshuffle_collective [smStore 20] (decodeCuSeqlens (smStore 90)) 1 0 := by
      have hw : smFinal 30 = ZigzagCollective.fw_maybe_unshuffle_collective [([].foldl (applyNodeDistributedFaithful CPEntry.smGraph) smStore) 20] (decodeCuSeqlens (([].foldl (applyNodeDistributedFaithful CPEntry.smGraph) smStore) 90)) 1 0 := by
        simpa [smFinal, smNodes] using
          (foldl_faithful_middle_writer CPEntry.smGraph smStore [] [] { rank := 0, op := "OpName.BW_maybe_shuffle", ins := [20, 90], outs := [30], params := [1, 0] } 30
            (fun t => ZigzagCollective.fw_maybe_unshuffle_collective [t 20] (decodeCuSeqlens (t 90)) 1 0) (by
              intro t
              rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
              rw [applyNodeDistributed_bw_maybe_shuffle_out]
              unfold applyNodeBWMaybeShuffleValue
              rw [ZigzagCollective.bw_maybe_shuffle_collective_eq_fw_unshuffle]
              rw [show CPEntry.smGraph.replicaBuddies { rank := 0, op := "OpName.BW_maybe_shuffle", ins := [20, 90], outs := [30], params := [1, 0] } = [{ rank := 0, op := "OpName.BW_maybe_shuffle", ins := [20, 90], outs := [30], params := [1, 0] }] by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.smGraph [] smStore 20 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.smGraph [] smStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hPm0 : pmFinal 300 = ZigzagCollective.fw_maybe_unshuffle_collective [pmStore 200, pmStore 201, pmStore 202] (decodeCuSeqlens (pmStore 90)) 3 0 := by
      have hw : pmFinal 300 = ZigzagCollective.fw_maybe_unshuffle_collective [([{ rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 200, ([{ rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 201, ([{ rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 202] (decodeCuSeqlens (([{ rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 90)) 3 0 := by
        simpa [pmFinal, pmNodes] using
          (foldl_faithful_middle_writer CPEntry.pmGraph pmStore [{ rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] }] [{ rank := 1, op := "OpName.BW_maybe_shuffle", ins := [201, 90], outs := [301], params := [3, 1] }] { rank := 0, op := "OpName.BW_maybe_shuffle", ins := [200, 90], outs := [300], params := [3, 0] } 300
            (fun t => ZigzagCollective.fw_maybe_unshuffle_collective [t 200, t 201, t 202] (decodeCuSeqlens (t 90)) 3 0) (by
              intro t
              rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
              rw [applyNodeDistributed_bw_maybe_shuffle_out]
              unfold applyNodeBWMaybeShuffleValue
              rw [ZigzagCollective.bw_maybe_shuffle_collective_eq_fw_unshuffle]
              rw [show CPEntry.pmGraph.replicaBuddies { rank := 0, op := "OpName.BW_maybe_shuffle", ins := [200, 90], outs := [300], params := [3, 0] } = [{ rank := 0, op := "OpName.BW_maybe_shuffle", ins := [200, 90], outs := [300], params := [3, 0] }, { rank := 1, op := "OpName.BW_maybe_shuffle", ins := [201, 90], outs := [301], params := [3, 1] }, { rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] }] by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] }] pmStore 200 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] }] pmStore 201 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] }] pmStore 202 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] }] pmStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hPm1 : pmFinal 301 = ZigzagCollective.fw_maybe_unshuffle_collective [pmStore 200, pmStore 201, pmStore 202] (decodeCuSeqlens (pmStore 90)) 3 1 := by
      have hw : pmFinal 301 = ZigzagCollective.fw_maybe_unshuffle_collective [([{ rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] }, { rank := 0, op := "OpName.BW_maybe_shuffle", ins := [200, 90], outs := [300], params := [3, 0] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 200, ([{ rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] }, { rank := 0, op := "OpName.BW_maybe_shuffle", ins := [200, 90], outs := [300], params := [3, 0] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 201, ([{ rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] }, { rank := 0, op := "OpName.BW_maybe_shuffle", ins := [200, 90], outs := [300], params := [3, 0] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 202] (decodeCuSeqlens (([{ rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] }, { rank := 0, op := "OpName.BW_maybe_shuffle", ins := [200, 90], outs := [300], params := [3, 0] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 90)) 3 1 := by
        simpa [pmFinal, pmNodes] using
          (foldl_faithful_middle_writer CPEntry.pmGraph pmStore [{ rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] }, { rank := 0, op := "OpName.BW_maybe_shuffle", ins := [200, 90], outs := [300], params := [3, 0] }] [] { rank := 1, op := "OpName.BW_maybe_shuffle", ins := [201, 90], outs := [301], params := [3, 1] } 301
            (fun t => ZigzagCollective.fw_maybe_unshuffle_collective [t 200, t 201, t 202] (decodeCuSeqlens (t 90)) 3 1) (by
              intro t
              rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
              rw [applyNodeDistributed_bw_maybe_shuffle_out]
              unfold applyNodeBWMaybeShuffleValue
              rw [ZigzagCollective.bw_maybe_shuffle_collective_eq_fw_unshuffle]
              rw [show CPEntry.pmGraph.replicaBuddies { rank := 1, op := "OpName.BW_maybe_shuffle", ins := [201, 90], outs := [301], params := [3, 1] } = [{ rank := 0, op := "OpName.BW_maybe_shuffle", ins := [200, 90], outs := [300], params := [3, 0] }, { rank := 1, op := "OpName.BW_maybe_shuffle", ins := [201, 90], outs := [301], params := [3, 1] }, { rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] }] by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] }, { rank := 0, op := "OpName.BW_maybe_shuffle", ins := [200, 90], outs := [300], params := [3, 0] }] pmStore 200 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] }, { rank := 0, op := "OpName.BW_maybe_shuffle", ins := [200, 90], outs := [300], params := [3, 0] }] pmStore 201 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] }, { rank := 0, op := "OpName.BW_maybe_shuffle", ins := [200, 90], outs := [300], params := [3, 0] }] pmStore 202 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] }, { rank := 0, op := "OpName.BW_maybe_shuffle", ins := [200, 90], outs := [300], params := [3, 0] }] pmStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hPm2 : pmFinal 302 = ZigzagCollective.fw_maybe_unshuffle_collective [pmStore 200, pmStore 201, pmStore 202] (decodeCuSeqlens (pmStore 90)) 3 2 := by
      have hw : pmFinal 302 = ZigzagCollective.fw_maybe_unshuffle_collective [([].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 200, ([].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 201, ([].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 202] (decodeCuSeqlens (([].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 90)) 3 2 := by
        simpa [pmFinal, pmNodes] using
          (foldl_faithful_middle_writer CPEntry.pmGraph pmStore [] [{ rank := 0, op := "OpName.BW_maybe_shuffle", ins := [200, 90], outs := [300], params := [3, 0] }, { rank := 1, op := "OpName.BW_maybe_shuffle", ins := [201, 90], outs := [301], params := [3, 1] }] { rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] } 302
            (fun t => ZigzagCollective.fw_maybe_unshuffle_collective [t 200, t 201, t 202] (decodeCuSeqlens (t 90)) 3 2) (by
              intro t
              rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
              rw [applyNodeDistributed_bw_maybe_shuffle_out]
              unfold applyNodeBWMaybeShuffleValue
              rw [ZigzagCollective.bw_maybe_shuffle_collective_eq_fw_unshuffle]
              rw [show CPEntry.pmGraph.replicaBuddies { rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] } = [{ rank := 0, op := "OpName.BW_maybe_shuffle", ins := [200, 90], outs := [300], params := [3, 0] }, { rank := 1, op := "OpName.BW_maybe_shuffle", ins := [201, 90], outs := [301], params := [3, 1] }, { rank := 2, op := "OpName.BW_maybe_shuffle", ins := [202, 90], outs := [302], params := [3, 2] }] by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [] pmStore 200 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [] pmStore 201 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [] pmStore 202 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [] pmStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hSmValue : smFinal 30 = smStore 20 := by
      simpa [ZigzagCollective.fw_maybe_unshuffle_collective] using hSm
    have hOut : fact_000001.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 30) [pmFinal 300, pmFinal 301, pmFinal 302] 0 [12, 2] [4, 2]
      rw [hSmValue, hPm0, hPm1, hPm2]
      exact core
    intro fact hfact
    have covered : fact ∈ [fact_000001] ++ state_000001.facts := by
      exact (show state_000002.facts ⊆ [fact_000001] ++ state_000001.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | hold
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hOut
    · exact hframe fact hold

private def composed : ClosedDepSegmentCertificate CPEntry.smGraph CPEntry.pmGraph state_000000 state_000002 where
  smNodes := CPEntry.smGraph.nodes
  pmNodes := CPEntry.pmGraph.nodes
  sound := by
    intro sm pm h
    rw [show CPEntry.smGraph.nodes = segment_000000.smNodes ++ segment_000001.smNodes by native_decide]
    rw [show CPEntry.pmGraph.nodes = segment_000000.pmNodes ++ segment_000001.pmNodes by native_decide]
    rw [List.foldl_append, List.foldl_append]
    exact segment_000001.sound _ _ (segment_000000.sound sm pm h)

private theorem CPEntryProof_anchor_sm_shape_10_from_external_inputs
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM CPEntry.smGraphInitEnv)
    (hPM : StoreShapesHold initPM CPEntry.pmGraphInitEnv)
    (hInit : InitGoalsHold CPEntry.pmGraph.numRanks CPEntry.initGoals initSM initPM)
    (hSMValues : InputValueClassesHold CPEntry.smInputValueClasses initSM)
    (hPMValues : InputValueClassesHold CPEntry.pmInputValueClasses initPM)
    (hPacked_0 : ZigzagCollective.PackedCuSeqlensWF (initPM 91) 12 3)
    : anchor_sm_shape_10.Holds initSM initPM := by
  unfold anchor_sm_shape_10 RelationFact.Holds StoreSide.read
  exact hSM 10 [12, 2] (by native_decide)
private theorem CPEntryProof_authority_cross_metadata_eq_90_90_from_external_inputs
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM CPEntry.smGraphInitEnv)
    (hPM : StoreShapesHold initPM CPEntry.pmGraphInitEnv)
    (hInit : InitGoalsHold CPEntry.pmGraph.numRanks CPEntry.initGoals initSM initPM)
    (hSMValues : InputValueClassesHold CPEntry.smInputValueClasses initSM)
    (hPMValues : InputValueClassesHold CPEntry.pmInputValueClasses initPM)
    (hPacked_0 : ZigzagCollective.PackedCuSeqlensWF (initPM 91) 12 3)
    : authority_cross_metadata_eq_90_90.Holds initSM initPM := by
  unfold authority_cross_metadata_eq_90_90 RelationFact.Holds StoreSide.read
  have hi := hInit CPEntry.initGoal_90 (by native_decide)
  exact InitGoalHolds.singleton_value_eq CPEntry.pmGraph.numRanks CPEntry.initGoal_90 initSM initPM
    { rank := 0, tid := 90 } hi rfl
private theorem CPEntryProof_authority_packed_cu_000000_from_external_inputs
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM CPEntry.smGraphInitEnv)
    (hPM : StoreShapesHold initPM CPEntry.pmGraphInitEnv)
    (hInit : InitGoalsHold CPEntry.pmGraph.numRanks CPEntry.initGoals initSM initPM)
    (hSMValues : InputValueClassesHold CPEntry.smInputValueClasses initSM)
    (hPMValues : InputValueClassesHold CPEntry.pmInputValueClasses initPM)
    (hPacked_0 : ZigzagCollective.PackedCuSeqlensWF (initPM 91) 12 3)
    : authority_packed_cu_000000.Holds initSM initPM := by
  unfold authority_packed_cu_000000 RelationFact.Holds StoreSide.read
  exact hPacked_0
private theorem CPEntryProof_authority_pm_metadata_eq_000000_90_from_external_inputs
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM CPEntry.smGraphInitEnv)
    (hPM : StoreShapesHold initPM CPEntry.pmGraphInitEnv)
    (hInit : InitGoalsHold CPEntry.pmGraph.numRanks CPEntry.initGoals initSM initPM)
    (hSMValues : InputValueClassesHold CPEntry.smInputValueClasses initSM)
    (hPMValues : InputValueClassesHold CPEntry.pmInputValueClasses initPM)
    (hPacked_0 : ZigzagCollective.PackedCuSeqlensWF (initPM 91) 12 3)
    : authority_pm_metadata_eq_000000_90.Holds initSM initPM := by
  unfold authority_pm_metadata_eq_000000_90 RelationFact.Holds StoreSide.read
  exact InputValueClassesHold.eq_of_mem hPMValues
    (c := CPEntry.pmInputValueClasses[0]'(by native_decide))
    (by native_decide) (by native_decide) (by native_decide)
private theorem CPEntryProof_fact_000000_from_external_inputs
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM CPEntry.smGraphInitEnv)
    (hPM : StoreShapesHold initPM CPEntry.pmGraphInitEnv)
    (hInit : InitGoalsHold CPEntry.pmGraph.numRanks CPEntry.initGoals initSM initPM)
    (hSMValues : InputValueClassesHold CPEntry.smInputValueClasses initSM)
    (hPMValues : InputValueClassesHold CPEntry.pmInputValueClasses initPM)
    (hPacked_0 : ZigzagCollective.PackedCuSeqlensWF (initPM 91) 12 3)
    : fact_000000.Holds initSM initPM := by
  unfold fact_000000 RelationFact.Holds StoreSide.read
  -- ordered PM TIDs: [100, 101, 102]
  have hi := hInit CPEntry.initGoal_10 (by native_decide)
  have htps : CPEntry.initGoal_10.tps = [{ rank := 0, tid := 100 }, { rank := 1, tid := 101 }, { rank := 2, tid := 102 }] := by native_decide
  have hfull := hSM 10 [12, 2] (by native_decide)
  have hp0 := hPM 100 [4, 2] (by native_decide)
  have hp1 := hPM 101 [4, 2] (by native_decide)
  have hp2 := hPM 102 [4, 2] (by native_decide)
  have hrel := ShardedRel.of_init_goal CPEntry.pmGraph.numRanks CPEntry.initGoal_10 initSM initPM 0 [12, 2] [4, 2]
    hi (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)
    (by
      rw [htps]
      simp only [List.map_cons, List.map_nil, List.head?_cons,
        Option.map_some, Option.getD_some]
      rw [hp0]
      native_decide)
    hfull
    (by
      intro shard hshard
      rw [htps] at hshard
      simp only [List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hshard
      rcases hshard with rfl | hshard
      · exact hp0
      rcases hshard with rfl | hshard
      · exact hp1
      subst shard
      exact hp2)
    (by native_decide) (by native_decide)
  simpa [CPEntry.initGoal_10] using hrel
private theorem CPEntryProof_initial_chunk_000
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM CPEntry.smGraphInitEnv)
    (hPM : StoreShapesHold initPM CPEntry.pmGraphInitEnv)
    (hInit : InitGoalsHold CPEntry.pmGraph.numRanks CPEntry.initGoals initSM initPM)
    (hSMValues : InputValueClassesHold CPEntry.smInputValueClasses initSM)
    (hPMValues : InputValueClassesHold CPEntry.pmInputValueClasses initPM)
    (hPacked_0 : ZigzagCollective.PackedCuSeqlensWF (initPM 91) 12 3)
    (fact : RelationFact) (hfact : fact ∈ [anchor_sm_shape_10, authority_cross_metadata_eq_90_90, authority_packed_cu_000000, authority_pm_metadata_eq_000000_90, fact_000000])
    : fact.Holds initSM initPM := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfact
  rcases hfact with rfl | hfact
  · exact CPEntryProof_anchor_sm_shape_10_from_external_inputs initSM initPM hSM hPM hInit hSMValues hPMValues hPacked_0
  rcases hfact with rfl | hfact
  · exact CPEntryProof_authority_cross_metadata_eq_90_90_from_external_inputs initSM initPM hSM hPM hInit hSMValues hPMValues hPacked_0
  rcases hfact with rfl | hfact
  · exact CPEntryProof_authority_packed_cu_000000_from_external_inputs initSM initPM hSM hPM hInit hSMValues hPMValues hPacked_0
  rcases hfact with rfl | hfact
  · exact CPEntryProof_authority_pm_metadata_eq_000000_90_from_external_inputs initSM initPM hSM hPM hInit hSMValues hPMValues hPacked_0
  subst fact
  exact CPEntryProof_fact_000000_from_external_inputs initSM initPM hSM hPM hInit hSMValues hPMValues hPacked_0
private theorem CPEntryProof_initial_state
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM CPEntry.smGraphInitEnv)
    (hPM : StoreShapesHold initPM CPEntry.pmGraphInitEnv)
    (hInit : InitGoalsHold CPEntry.pmGraph.numRanks CPEntry.initGoals initSM initPM)
    (hSMValues : InputValueClassesHold CPEntry.smInputValueClasses initSM)
    (hPMValues : InputValueClassesHold CPEntry.pmInputValueClasses initPM)
    (hPacked_0 : ZigzagCollective.PackedCuSeqlensWF (initPM 91) 12 3)
    : state_000000.Holds initSM initPM := by
  intro fact hfact
  have covered : fact ∈ [anchor_sm_shape_10, authority_cross_metadata_eq_90_90, authority_packed_cu_000000, authority_pm_metadata_eq_000000_90, fact_000000] := by
    exact (show state_000000.facts ⊆ [anchor_sm_shape_10, authority_cross_metadata_eq_90_90, authority_packed_cu_000000, authority_pm_metadata_eq_000000_90, fact_000000] by native_decide) hfact
  exact CPEntryProof_initial_chunk_000 initSM initPM hSM hPM hInit hSMValues hPMValues hPacked_0 fact covered

@[irreducible] private def CPEntryProof_target_statement (initSM initPM : Store) : Prop :=
  fact_000001.Holds (denoteGraphDistributedFaithful CPEntry.smGraph initSM) (denoteGraphDistributedFaithful CPEntry.pmGraph initPM)
private theorem CPEntryProof_target_from_external_inputs
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM CPEntry.smGraphInitEnv)
    (hPM : StoreShapesHold initPM CPEntry.pmGraphInitEnv)
    (hInit : InitGoalsHold CPEntry.pmGraph.numRanks CPEntry.initGoals initSM initPM)
    (hSMValues : InputValueClassesHold CPEntry.smInputValueClasses initSM)
    (hPMValues : InputValueClassesHold CPEntry.pmInputValueClasses initPM)
    (hPacked_0 : ZigzagCollective.PackedCuSeqlensWF (initPM 91) 12 3)
    : CPEntryProof_target_statement initSM initPM := by
  unfold CPEntryProof_target_statement
  have hpre := CPEntryProof_initial_state initSM initPM hSM hPM hInit hSMValues hPMValues hPacked_0
  have h := composed.sound initSM initPM hpre
  exact h fact_000001 (by native_decide)

private theorem CPEntryProof_sharded_target_publication (smStore pmStore : Store)
    (htarget : fact_000001.Holds smStore pmStore) :
    let ts := smStore CPEntry.exitGoal.ts
    let tps := CPEntry.exitGoal.tps.map (fun p => pmStore p.tid)
    ts.shape = CPEntry.exitGoal.tsShape ∧
      (tps.map (fun t => t.shape)) = CPEntry.exitGoal.tpShapes ∧
      ts = reconstructForGoal CPEntry.exitGoal CPEntry.pmGraph.numRanks tps := by
  refine ⟨htarget.full_shape, ?_, ?_⟩
  · change [(pmStore 300).shape, (pmStore 301).shape, (pmStore 302).shape] = [[4, 2], [4, 2], [4, 2]]
    rw [htarget.shard_shapes (pmStore 300) (by simp), htarget.shard_shapes (pmStore 301) (by simp), htarget.shard_shapes (pmStore 302) (by simp)]
  · rw [reconstructForGoal_of_not_replicated CPEntry.exitGoal CPEntry.pmGraph.numRanks _ rfl]
    simp only [CPEntry.exitGoal, List.map]
    rw [reconstructWithDim_cons_cons_nonscalar 0 CPEntry.pmGraph.numRanks 0 (pmStore 300) (pmStore 301) [pmStore 302] (by
      rw [htarget.shard_shapes (pmStore 300) (by simp)]
      native_decide)]
    have hRankCount : CPEntry.pmGraph.numRanks = [pmStore 300, pmStore 301, pmStore 302].length := by rfl
    rw [hRankCount]
    exact htarget.full_value

@[irreducible] private def CPEntryProof_public_body_statement (initSM initPM : Store) : Prop :=
  let smStore := denoteGraphDistributedFaithful CPEntry.smGraph initSM
  let pmStore := denoteGraphDistributedFaithful CPEntry.pmGraph initPM
  let ts := smStore CPEntry.exitGoal.ts
  let tps := CPEntry.exitGoal.tps.map (fun p => pmStore p.tid)
  ts.shape = CPEntry.exitGoal.tsShape ∧
    (tps.map (fun t => t.shape)) = CPEntry.exitGoal.tpShapes ∧
    ts = reconstructForGoal CPEntry.exitGoal CPEntry.pmGraph.numRanks tps
private theorem CPEntryProof_public_body_proof
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM CPEntry.smGraphInitEnv)
    (hPM : StoreShapesHold initPM CPEntry.pmGraphInitEnv)
    (hInit : InitGoalsHold CPEntry.pmGraph.numRanks CPEntry.initGoals initSM initPM)
    (hSMValues : InputValueClassesHold CPEntry.smInputValueClasses initSM)
    (hPMValues : InputValueClassesHold CPEntry.pmInputValueClasses initPM)
    (hPacked_0 : ZigzagCollective.PackedCuSeqlensWF (initPM 91) 12 3)
    : CPEntryProof_public_body_statement initSM initPM := by
  unfold CPEntryProof_public_body_statement
  have htarget := CPEntryProof_target_from_external_inputs initSM initPM hSM hPM hInit hSMValues hPMValues hPacked_0
  unfold CPEntryProof_target_statement fact_000001 RelationFact.Holds at htarget
  exact CPEntryProof_sharded_target_publication (denoteGraphDistributedFaithful CPEntry.smGraph initSM) (denoteGraphDistributedFaithful CPEntry.pmGraph initPM) htarget


@[irreducible] private def CPEntryProof_public_statement : Prop := CPEntry.exitStatement
private theorem CPEntryProof_public_proof : CPEntryProof_public_statement := by
  unfold CPEntryProof_public_statement
  unfold CPEntry.exitStatement
  unfold CoarseLineageHoldsWithInitDistributedFaithfulWithContract
  intro initSM initPM hSM hPM hInit hContract
  unfold CPEntry.externalContract at hContract
  rcases hContract with ⟨hSMValues, hPMValues, hPacked_0⟩
  simpa only [CPEntryProof_public_body_statement, InitGoalHolds] using CPEntryProof_public_body_proof initSM initPM hSM hPM hInit hSMValues hPMValues hPacked_0

theorem prove_goal_0_closed : CPEntry.exitStatement := by
  simpa only [CPEntryProof_public_statement] using CPEntryProof_public_proof

#print axioms prove_goal_0_closed

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
  have h := composed.sound CPEntry.initSM CPEntry.initPM inhabitedInput
  exact h fact_000001 (by native_decide)
#print axioms inhabitedOutput


open ZigzagKRelationWitness in
theorem publicInputs :
    StoreShapesHold CPEntry.initSM CPEntry.smGraphInitEnv ∧
    StoreShapesHold CPEntry.initPM CPEntry.pmGraphInitEnv ∧
    InitGoalsHold 3 CPEntry.initGoals CPEntry.initSM CPEntry.initPM ∧
    CPEntry.externalContract CPEntry.initSM CPEntry.initPM := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro tid sh h
    simp [CPEntry.smGraphInitEnv, CPEntry.smShapes, shapeEnvOfList, List.find?] at h
    by_cases h10 : 10 = tid <;> by_cases h90 : 90 = tid <;> by_cases h91 : 91 = tid <;>
      simp_all [CPEntry.initSM, sharded_input.full_shape, cu, Tensor.mkShape, eq_comm]
  · intro tid sh h
    simp [CPEntry.pmGraphInitEnv, CPEntry.pmShapes, shapeEnvOfList, List.find?] at h
    by_cases h100 : 100 = tid <;> by_cases h101 : 101 = tid <;> by_cases h102 : 102 = tid <;>
      by_cases h90 : 90 = tid <;> by_cases h91 : 91 = tid <;>
      simp_all [CPEntry.initPM, source, cu, Tensor.mkShape, eq_comm]
  · intro g hg
    simp only [CPEntry.initGoals, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · refine ⟨sharded_input.full_shape, rfl, ?_⟩
      rw [reconstructForGoal_of_not_replicated _ _ _ rfl]
      change full = reconstructWithDim 0 3 0 [source 0, source 1, source 2]
      rw [reconstructWithDim_cons_cons_nonscalar 0 3 0 (source 0) (source 1) [source 2] (by decide)]
      rfl
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
  · refine ⟨?_, ?_, CPEntry.packed⟩
    · intro c hc tid ht
      simp only [CPEntry.smInputValueClasses, List.mem_singleton] at hc
      subst c
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> rfl
    · intro c hc tid ht
      simp only [CPEntry.pmInputValueClasses, List.mem_singleton] at hc
      subst c
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl <;> rfl

theorem inhabitedPublicOutput : InitGoalHolds 3 CPEntry.exitGoal
    (denoteGraphDistributedFaithful CPEntry.smGraph CPEntry.initSM)
    (denoteGraphDistributedFaithful CPEntry.pmGraph CPEntry.initPM) :=
  prove_goal_0_closed CPEntry.initSM CPEntry.initPM publicInputs.1
    publicInputs.2.1 publicInputs.2.2.1 publicInputs.2.2.2
#print axioms publicInputs
#print axioms inhabitedPublicOutput
end
end TrainVerify.Denote.CPEntryProof
