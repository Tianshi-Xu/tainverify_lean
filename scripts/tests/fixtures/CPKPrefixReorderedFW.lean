/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler
import denote.InputValueClasses
import denote.ZigzagKRelationWitness

open TrainVerify.Denote
namespace CPEntry
noncomputable section
def smGraph : GraphDecl where
  numRanks := 1
  nodes := [{ rank := 0, op := "OpName.FW_contiguous", ins := [10], outs := [30] }, { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [30, 90], outs := [20], params := [1, 0] }]
  replicaGroups := [{ logical := { cid := 0, mb := 0, irname := "FW_maybe_shuffle" }, members := [{ rank := 0, primaryOutTid := 20 }] }]
def smShapes : List (Tid × Shape) := [(10, [12, 2]), (90, [2]), (91, [2])]
def smInputValueClasses : List InputValueClass := [{ source := "cu", tids := [90, 91] }]
def pmGraph : GraphDecl where
  numRanks := 3
  nodes := [{ rank := 2, op := "OpName.FW_contiguous", ins := [102], outs := [112] }, { rank := 0, op := "OpName.FW_contiguous", ins := [100], outs := [110] }, { rank := 1, op := "OpName.FW_contiguous", ins := [101], outs := [111] }, { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [111, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.FW_maybe_shuffle", ins := [112, 90], outs := [202], params := [3, 2] }]
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
  .sharded 30 [110, 111, 112] 0 [12, 2] [4, 2]

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
  facts := [anchor_sm_shape_10, authority_cross_metadata_eq_90_90, authority_packed_cu_000000, authority_pm_metadata_eq_000000_90, fact_000001]
  nonempty := by decide

private def state_000002 : RelationState where
  facts := [anchor_sm_shape_10, fact_000001, fact_000002]
  nonempty := by decide

private def segment_000000_sm_node : NodeDecl := { rank := 0, op := "OpName.FW_contiguous", ins := [10], outs := [30] }
private def segment_000000_pm_node_0 : NodeDecl := { rank := 0, op := "OpName.FW_contiguous", ins := [100], outs := [110] }
private def segment_000000_pm_node_1 : NodeDecl := { rank := 1, op := "OpName.FW_contiguous", ins := [101], outs := [111] }
private def segment_000000_pm_node_2 : NodeDecl := { rank := 2, op := "OpName.FW_contiguous", ins := [102], outs := [112] }
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_contiguous", ins := [10], outs := [30] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 2, op := "OpName.FW_contiguous", ins := [102], outs := [112] }, { rank := 0, op := "OpName.FW_contiguous", ins := [100], outs := [110] }, { rank := 1, op := "OpName.FW_contiguous", ins := [101], outs := [111] }]

private def segment_000000 :
    ClosedDepSegmentCertificate CPEntry.smGraph CPEntry.pmGraph state_000000 state_000001 where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := segment_000000_sm_nodes
    let pmNodes : List NodeDecl := segment_000000_pm_nodes
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful CPEntry.smGraph) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore
    have hframe : state_000000.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hin : fact_000000.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 10) [pmStore 100, pmStore 101, pmStore 102] 0 [12, 2] [4, 2] at hin
    have hSmWriter : smFinal 30 = fw_contiguous (smStore 10) := by
      change (smNodes.foldl (applyNodeDistributedFaithful CPEntry.smGraph) smStore) 30 = _
      rw [show smNodes = smNodes.take 0 ++ [segment_000000_sm_node] ++ smNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer CPEntry.smGraph smStore (smNodes.take 0) (smNodes.drop 1)
        segment_000000_sm_node 30 (fun t => fw_contiguous (t 10)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn, segment_000000_sm_node]
          exact applyNode_fw_contiguous_out CPEntry.smGraph t 0 10 30
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.smGraph (smNodes.take 0) smStore 10 (by native_decide) (by native_decide)]
    have hPmWriter0 : pmFinal 110 = fw_contiguous (pmStore 100) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 110 = _
      rw [show pmNodes = pmNodes.take 1 ++ [segment_000000_pm_node_0] ++ pmNodes.drop 2 by native_decide]
      rw [foldl_faithful_middle_writer CPEntry.pmGraph pmStore (pmNodes.take 1) (pmNodes.drop 2)
        segment_000000_pm_node_0 110 (fun t => fw_contiguous (t 100)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn, segment_000000_pm_node_0]
          exact applyNode_fw_contiguous_out CPEntry.pmGraph t 0 100 110
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph (pmNodes.take 1) pmStore 100 (by native_decide) (by native_decide)]
    have hPmWriter1 : pmFinal 111 = fw_contiguous (pmStore 101) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 111 = _
      rw [show pmNodes = pmNodes.take 2 ++ [segment_000000_pm_node_1] ++ pmNodes.drop 3 by native_decide]
      rw [foldl_faithful_middle_writer CPEntry.pmGraph pmStore (pmNodes.take 2) (pmNodes.drop 3)
        segment_000000_pm_node_1 111 (fun t => fw_contiguous (t 101)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn, segment_000000_pm_node_1]
          exact applyNode_fw_contiguous_out CPEntry.pmGraph t 1 101 111
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph (pmNodes.take 2) pmStore 101 (by native_decide) (by native_decide)]
    have hPmWriter2 : pmFinal 112 = fw_contiguous (pmStore 102) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 112 = _
      rw [show pmNodes = pmNodes.take 0 ++ [segment_000000_pm_node_2] ++ pmNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer CPEntry.pmGraph pmStore (pmNodes.take 0) (pmNodes.drop 1)
        segment_000000_pm_node_2 112 (fun t => fw_contiguous (t 102)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn, segment_000000_pm_node_2]
          exact applyNode_fw_contiguous_out CPEntry.pmGraph t 2 102 112
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph (pmNodes.take 0) pmStore 102 (by native_decide) (by native_decide)]
    have htransport := ShardedRel.fw_contiguous hin
    have hout : fact_000001.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 30) [pmFinal 110, pmFinal 111, pmFinal 112] 0 [12, 2] [4, 2]
      rw [hSmWriter, hPmWriter0, hPmWriter1, hPmWriter2]
      simpa only [List.map] using htransport
    intro fact hfact
    have covered : fact ∈ [fact_000001] ++ state_000000.facts := by
      exact (show state_000001.facts ⊆ [fact_000001] ++ state_000000.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hout
    · exact hframe fact old

private def segment_000001 :
    ClosedDepSegmentCertificate CPEntry.smGraph CPEntry.pmGraph state_000001 state_000002 where
  smNodes := [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [30, 90], outs := [20], params := [1, 0] }]
  pmNodes := [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [111, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.FW_maybe_shuffle", ins := [112, 90], outs := [202], params := [3, 2] }]
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [30, 90], outs := [20], params := [1, 0] }]
    let pmNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [111, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.FW_maybe_shuffle", ins := [112, 90], outs := [202], params := [3, 2] }]
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful CPEntry.smGraph) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore
    have hframe : state_000001.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hSource : fact_000001.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 30) [pmStore 110, pmStore 111, pmStore 112] 0 [12, 2] [4, 2] at hSource
    have hPacked : authority_packed_cu_000000.Holds smStore pmStore := hstate _ (by native_decide)
    have hAlias : authority_pm_metadata_eq_000000_90.Holds smStore pmStore := hstate _ (by native_decide)
    change ZigzagCollective.PackedCuSeqlensWF (pmStore 91) 12 3 at hPacked
    change pmStore 90 = pmStore 91 at hAlias
    have hPackedActual : ZigzagCollective.PackedCuSeqlensWF (pmStore 90) 12 3 := by
      rw [hAlias]
      exact hPacked
    have hCu : ZigzagCollective.ZigzagCuWF (decodeCuSeqlens (pmStore 90)) [pmStore 110, pmStore 111, pmStore 112] 3 := by
      apply hPackedActual.toZigzagCuWF rfl
      · intro x hx
        rw [hSource.shard_shapes x hx]
        decide
      · intro x hx
        change x.shape = (pmStore 110).shape
        rw [hSource.shard_shapes x hx, hSource.shard_shapes (pmStore 110) (by simp)]
      · change (pmStore 110).shape.getD 0 0 * 3 = 12
        rw [hSource.shard_shapes (pmStore 110) (by simp)]
        rfl
    have core := ZigzagKRel.of_sharded hSource hCu
    have hSm : smFinal 20 = ZigzagCollective.fw_maybe_shuffle_collective [smStore 30] (decodeCuSeqlens (smStore 90)) 1 0 := by
      have hw : smFinal 20 = ZigzagCollective.fw_maybe_shuffle_collective [([].foldl (applyNodeDistributedFaithful CPEntry.smGraph) smStore) 30] (decodeCuSeqlens (([].foldl (applyNodeDistributedFaithful CPEntry.smGraph) smStore) 90)) 1 0 := by
        simpa [smFinal, smNodes] using
          (foldl_faithful_middle_writer CPEntry.smGraph smStore [] [] { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [30, 90], outs := [20], params := [1, 0] } 20
            (fun t => ZigzagCollective.fw_maybe_shuffle_collective [t 30] (decodeCuSeqlens (t 90)) 1 0) (by
              intro t
              rw [applyNodeDistributedFaithful_shuffle_out]
              unfold applyNodeFaithfulShuffleValue
              rw [show CPEntry.smGraph.replicaBuddies { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [30, 90], outs := [20], params := [1, 0] } = [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [30, 90], outs := [20], params := [1, 0] }] by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.smGraph [] smStore 30 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.smGraph [] smStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hPm0 : pmFinal 200 = ZigzagCollective.fw_maybe_shuffle_collective [pmStore 110, pmStore 111, pmStore 112] (decodeCuSeqlens (pmStore 90)) 3 0 := by
      have hw : pmFinal 200 = ZigzagCollective.fw_maybe_shuffle_collective [([].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 110, ([].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 111, ([].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 112] (decodeCuSeqlens (([].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 90)) 3 0 := by
        simpa [pmFinal, pmNodes] using
          (foldl_faithful_middle_writer CPEntry.pmGraph pmStore [] [{ rank := 1, op := "OpName.FW_maybe_shuffle", ins := [111, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.FW_maybe_shuffle", ins := [112, 90], outs := [202], params := [3, 2] }] { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] } 200
            (fun t => ZigzagCollective.fw_maybe_shuffle_collective [t 110, t 111, t 112] (decodeCuSeqlens (t 90)) 3 0) (by
              intro t
              rw [applyNodeDistributedFaithful_shuffle_out]
              unfold applyNodeFaithfulShuffleValue
              rw [show CPEntry.pmGraph.replicaBuddies { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] } = [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [111, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.FW_maybe_shuffle", ins := [112, 90], outs := [202], params := [3, 2] }] by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [] pmStore 110 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [] pmStore 111 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [] pmStore 112 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [] pmStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hPm1 : pmFinal 201 = ZigzagCollective.fw_maybe_shuffle_collective [pmStore 110, pmStore 111, pmStore 112] (decodeCuSeqlens (pmStore 90)) 3 1 := by
      have hw : pmFinal 201 = ZigzagCollective.fw_maybe_shuffle_collective [([{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 110, ([{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 111, ([{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 112] (decodeCuSeqlens (([{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 90)) 3 1 := by
        simpa [pmFinal, pmNodes] using
          (foldl_faithful_middle_writer CPEntry.pmGraph pmStore [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] }] [{ rank := 2, op := "OpName.FW_maybe_shuffle", ins := [112, 90], outs := [202], params := [3, 2] }] { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [111, 90], outs := [201], params := [3, 1] } 201
            (fun t => ZigzagCollective.fw_maybe_shuffle_collective [t 110, t 111, t 112] (decodeCuSeqlens (t 90)) 3 1) (by
              intro t
              rw [applyNodeDistributedFaithful_shuffle_out]
              unfold applyNodeFaithfulShuffleValue
              rw [show CPEntry.pmGraph.replicaBuddies { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [111, 90], outs := [201], params := [3, 1] } = [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [111, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.FW_maybe_shuffle", ins := [112, 90], outs := [202], params := [3, 2] }] by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] }] pmStore 110 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] }] pmStore 111 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] }] pmStore 112 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] }] pmStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hPm2 : pmFinal 202 = ZigzagCollective.fw_maybe_shuffle_collective [pmStore 110, pmStore 111, pmStore 112] (decodeCuSeqlens (pmStore 90)) 3 2 := by
      have hw : pmFinal 202 = ZigzagCollective.fw_maybe_shuffle_collective [([{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [111, 90], outs := [201], params := [3, 1] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 110, ([{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [111, 90], outs := [201], params := [3, 1] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 111, ([{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [111, 90], outs := [201], params := [3, 1] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 112] (decodeCuSeqlens (([{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [111, 90], outs := [201], params := [3, 1] }].foldl (applyNodeDistributedFaithful CPEntry.pmGraph) pmStore) 90)) 3 2 := by
        simpa [pmFinal, pmNodes] using
          (foldl_faithful_middle_writer CPEntry.pmGraph pmStore [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [111, 90], outs := [201], params := [3, 1] }] [] { rank := 2, op := "OpName.FW_maybe_shuffle", ins := [112, 90], outs := [202], params := [3, 2] } 202
            (fun t => ZigzagCollective.fw_maybe_shuffle_collective [t 110, t 111, t 112] (decodeCuSeqlens (t 90)) 3 2) (by
              intro t
              rw [applyNodeDistributedFaithful_shuffle_out]
              unfold applyNodeFaithfulShuffleValue
              rw [show CPEntry.pmGraph.replicaBuddies { rank := 2, op := "OpName.FW_maybe_shuffle", ins := [112, 90], outs := [202], params := [3, 2] } = [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [111, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.FW_maybe_shuffle", ins := [112, 90], outs := [202], params := [3, 2] }] by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [111, 90], outs := [201], params := [3, 1] }] pmStore 110 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [111, 90], outs := [201], params := [3, 1] }] pmStore 111 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [111, 90], outs := [201], params := [3, 1] }] pmStore 112 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [110, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [111, 90], outs := [201], params := [3, 1] }] pmStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hSmValue : smFinal 20 = smStore 30 := by
      simpa [ZigzagCollective.fw_maybe_shuffle_collective] using hSm
    have hMetadataFinal : pmFinal 90 = pmStore 90 :=
      foldl_applyNodeDistributedFaithful_at_not_written CPEntry.pmGraph pmNodes pmStore 90 (by native_decide) (by native_decide)
    have hOut : fact_000002.Holds smFinal pmFinal := by
      change ZigzagKRel (smFinal 20) [pmFinal 200, pmFinal 201, pmFinal 202] (pmFinal 90) [12, 2] [4, 2]
      rw [hSmValue, hPm0, hPm1, hPm2, hMetadataFinal]
      exact core
    intro fact hfact
    have covered : fact ∈ [fact_000002] ++ state_000001.facts := by
      exact (show state_000002.facts ⊆ [fact_000002] ++ state_000001.facts by native_decide) hfact
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
theorem inhabitedOutput : fact_000002.Holds
    (smGraph.nodes.foldl (applyNodeDistributedFaithful smGraph) initSM)
    (pmGraph.nodes.foldl (applyNodeDistributedFaithful pmGraph) initPM) := by
  have h := composed.sound CPEntry.initSM CPEntry.initPM inhabitedInput
  exact h fact_000002 (by native_decide)
#print axioms inhabitedOutput
end
end TrainVerify.Denote.CPEntryProof
