/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler
import denote.InputValueClasses
import denote.GraphGears
import denote.ZigzagKAttentionWitness
import denote.ZigzagKAttention
import denote.ZigzagKAttentionRefinement
import denote.ZigzagKExit
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace CPKAttention
noncomputable section
def smGraph : GraphDecl where
  numRanks := 1
  nodes := [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [10, 90], outs := [20], params := [1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [20, 11, 12, 90, 90], outs := [30], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [30, 90], outs := [40], params := [1, 0] }]
  replicaGroups := [{ logical := { cid := 0, mb := 0, irname := "FW_maybe_shuffle" }, members := [{ rank := 0, primaryOutTid := 20 }] }, { logical := { cid := 1, mb := 0, irname := "FW_attn_zigzag" }, members := [{ rank := 0, primaryOutTid := 30 }] }, { logical := { cid := 2, mb := 0, irname := "FW_maybe_unshuffle" }, members := [{ rank := 0, primaryOutTid := 40 }] }]
def smShapes : List (Tid × Shape) := [(10, [12, 2, 2]), (90, [2]), (91, [2]), (11, [12, 1, 2]), (12, [12, 1, 3])]
def smGraphInitEnv : ShapeEnv := shapeEnvOfList smShapes
def smInputValueClasses : List InputValueClass := [{ source := "cu", tids := [90, 91] }]
def pmGraph : GraphDecl where
  numRanks := 3
  nodes := [{ rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }, { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }, { rank := 1, op := "OpName.FW_attn_zigzag", ins := [201, 111, 121, 90, 90], outs := [301], params := [2, 1, 2, 3, 1, 0] }, { rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] }, { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [300, 90], outs := [400], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [301, 90], outs := [401], params := [3, 1] }]
  replicaGroups := [{ logical := { cid := 0, mb := 0, irname := "FW_maybe_shuffle" }, members := [{ rank := 0, primaryOutTid := 200 }, { rank := 1, primaryOutTid := 201 }, { rank := 2, primaryOutTid := 202 }] }, { logical := { cid := 1, mb := 0, irname := "FW_attn_zigzag" }, members := [{ rank := 0, primaryOutTid := 300 }, { rank := 1, primaryOutTid := 301 }, { rank := 2, primaryOutTid := 302 }] }, { logical := { cid := 2, mb := 0, irname := "FW_maybe_unshuffle" }, members := [{ rank := 0, primaryOutTid := 400 }, { rank := 1, primaryOutTid := 401 }, { rank := 2, primaryOutTid := 402 }] }]
def pmShapes : List (Tid × Shape) := [(100, [4, 2, 2]), (101, [4, 2, 2]), (102, [4, 2, 2]), (90, [2]), (91, [2]), (110, [4, 1, 2]), (111, [4, 1, 2]), (112, [4, 1, 2]), (120, [4, 1, 3]), (121, [4, 1, 3]), (122, [4, 1, 3])]
def pmGraphInitEnv : ShapeEnv := shapeEnvOfList pmShapes
def pmInputValueClasses : List InputValueClass := [{ source := "cu", tids := [90, 91] }]
abbrev q := ZigzagKAttentionWitness.q
abbrev k := ZigzagKAttentionWitness.k
def v : Tensor := Tensor.mkShape [12, 1, 3] (fun i => (3 * i.val + 2 : Nat))
abbrev cu := ZigzagKAttentionWitness.cu
abbrev sources := ZigzagKAttentionWitness.sources
theorem q_sharded : ShardedRel q (sources q) 0 [12, 2, 2] [4, 2, 2] := ZigzagKAttentionWitness.q_sharded
theorem k_sharded : ShardedRel k (sources k) 0 [12, 1, 2] [4, 1, 2] := ZigzagKAttentionWitness.k_sharded
theorem v_sharded : ShardedRel v (sources v) 0 [12, 1, 3] [4, 1, 3] :=
  ShardedRel.attention_chunks v 3 2 1 3 (by decide) rfl
def initSM : Store := fun tid => if tid = 10 then q else if tid = 11 then k else if tid = 12 then v else cu
def initPM : Store := fun tid =>
  if tid = 100 then (sources q).getD 0 (zeroTensor []) else
  if tid = 101 then (sources q).getD 1 (zeroTensor []) else
  if tid = 102 then (sources q).getD 2 (zeroTensor []) else
  if tid = 110 then (sources k).getD 0 (zeroTensor []) else
  if tid = 111 then (sources k).getD 1 (zeroTensor []) else
  if tid = 112 then (sources k).getD 2 (zeroTensor []) else
  if tid = 120 then (sources v).getD 0 (zeroTensor []) else
  if tid = 121 then (sources v).getD 1 (zeroTensor []) else
  if tid = 122 then (sources v).getD 2 (zeroTensor []) else cu
theorem packed : ZigzagCollective.PackedCuSeqlensWF cu 12 3 := by
  have h := ZigzagKAttentionWitness.q_metadata
  refine ⟨by decide, ZigzagAttentionSourceWitness.decode_cu, h.cu_starts_zero, h.cu_has_endpoint, h.monotone, h.divisible, ?_⟩
  rw [ZigzagAttentionSourceWitness.decode_cu]
  rfl
def initGoal_10 : LineageGoal := { ts := 10, tsShape := [12, 2, 2], tps := [{ rank := 0, tid := 100 }, { rank := 1, tid := 101 }, { rank := 2, tid := 102 }], tpShapes := [[4, 2, 2], [4, 2, 2], [4, 2, 2]], gatherDim := 0 }
def initGoal_90 : LineageGoal := { ts := 90, tsShape := [2], tps := [{ rank := 0, tid := 90 }], tpShapes := [[2]], gatherDim := 0 }
def initGoal_91 : LineageGoal := { ts := 91, tsShape := [2], tps := [{ rank := 0, tid := 91 }], tpShapes := [[2]], gatherDim := 0 }
def initGoal_11 : LineageGoal := { ts := 11, tsShape := [12, 1, 2], tps := [{ rank := 0, tid := 110 }, { rank := 1, tid := 111 }, { rank := 2, tid := 112 }], tpShapes := [[4, 1, 2], [4, 1, 2], [4, 1, 2]], gatherDim := 0 }
def initGoal_12 : LineageGoal := { ts := 12, tsShape := [12, 1, 3], tps := [{ rank := 0, tid := 120 }, { rank := 1, tid := 121 }, { rank := 2, tid := 122 }], tpShapes := [[4, 1, 3], [4, 1, 3], [4, 1, 3]], gatherDim := 0 }
def initGoals : List LineageGoal := [initGoal_10, initGoal_90, initGoal_91, initGoal_11, initGoal_12]
def exitGoal : LineageGoal := { ts := 40, tsShape := [12, 2, 3], tps := [{ rank := 0, tid := 400 }, { rank := 1, tid := 401 }, { rank := 2, tid := 402 }], tpShapes := [[4, 2, 3], [4, 2, 3], [4, 2, 3]], gatherDim := 0 }
def externalContract (sm pm : Store) : Prop :=
  InputValueClassesHold smInputValueClasses sm ∧
  InputValueClassesHold pmInputValueClasses pm ∧
  ZigzagCollective.PackedCuSeqlensWF (pm 91) 12 3
def exitStatement : Prop :=
  CoarseLineageHoldsWithInitDistributedFaithfulWithContract
    smGraph pmGraph exitGoal smGraphInitEnv pmGraphInitEnv initGoals externalContract
theorem publicInputs :
    StoreShapesHold initSM smGraphInitEnv ∧ StoreShapesHold initPM pmGraphInitEnv ∧
    InitGoalsHold 3 initGoals initSM initPM ∧ externalContract initSM initPM := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro tid sh h
    have hm := shapeEnvOfList_mem_of_eq_some h
    simp only [smShapes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals rfl
  · intro tid sh h
    have hm := shapeEnvOfList_mem_of_eq_some h
    simp only [pmShapes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals rfl
  · intro g hg
    simp only [initGoals, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    · refine ⟨rfl, rfl, ?_⟩
      rw [reconstructForGoal_of_not_replicated _ _ _ rfl]
      change q = reconstructWithDim 0 3 0 [(chunkPrimDimN 0 3 0 q), (chunkPrimDimN 0 3 1 q), (chunkPrimDimN 0 3 2 q)]
      rw [reconstructWithDim_cons_cons_nonscalar 0 3 0 (chunkPrimDimN 0 3 0 q) (chunkPrimDimN 0 3 1 q) [(chunkPrimDimN 0 3 2 q)] (by decide)]
      exact q_sharded.full_value
    · exact ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl⟩
    · refine ⟨rfl, rfl, ?_⟩
      rw [reconstructForGoal_of_not_replicated _ _ _ rfl]
      change k = reconstructWithDim 0 3 0 [(chunkPrimDimN 0 3 0 k), (chunkPrimDimN 0 3 1 k), (chunkPrimDimN 0 3 2 k)]
      rw [reconstructWithDim_cons_cons_nonscalar 0 3 0 (chunkPrimDimN 0 3 0 k) (chunkPrimDimN 0 3 1 k) [(chunkPrimDimN 0 3 2 k)] (by decide)]
      exact k_sharded.full_value
    · refine ⟨rfl, rfl, ?_⟩
      rw [reconstructForGoal_of_not_replicated _ _ _ rfl]
      change v = reconstructWithDim 0 3 0 [(chunkPrimDimN 0 3 0 v), (chunkPrimDimN 0 3 1 v), (chunkPrimDimN 0 3 2 v)]
      rw [reconstructWithDim_cons_cons_nonscalar 0 3 0 (chunkPrimDimN 0 3 0 v) (chunkPrimDimN 0 3 1 v) [(chunkPrimDimN 0 3 2 v)] (by decide)]
      exact v_sharded.full_value
  · refine ⟨?_, ?_, packed⟩
    · intro cls hcls tid htid
      simp only [smInputValueClasses, List.mem_singleton] at hcls
      subst cls
      simp only [List.mem_cons, List.not_mem_nil, or_false] at htid
      rcases htid with rfl | rfl <;> rfl
    · intro cls hcls tid htid
      simp only [pmInputValueClasses, List.mem_singleton] at hcls
      subst cls
      simp only [List.mem_cons, List.not_mem_nil, or_false] at htid
      rcases htid with rfl | rfl <;> rfl
end
end CPKAttention


open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.CPKAttentionProof

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_000000 : RelationFact :=
  .sharded 10 [100, 101, 102] 0 [12, 2, 2] [4, 2, 2]

private def fact_000001 : RelationFact :=
  .sharded 11 [110, 111, 112] 0 [12, 1, 2] [4, 1, 2]

private def fact_000002 : RelationFact :=
  .sharded 12 [120, 121, 122] 0 [12, 1, 3] [4, 1, 3]

private def fact_000003 : RelationFact :=
  .sharded 40 [400, 401, 402] 0 [12, 2, 3] [4, 2, 3]

private def fact_000004 : RelationFact :=
  .zigzagK 20 [200, 201, 202] 90 [12, 2, 2] [4, 2, 2]

private def fact_000005 : RelationFact :=
  .zigzagK 30 [300, 301, 302] 90 [12, 2, 3] [4, 2, 3]

private def authority_cross_metadata_eq_90_90 : RelationFact :=
  .tensorEq .sm 90 .pm 90

private def authority_packed_cu_000000 : RelationFact :=
  .packedCu .pm 91 12 3

private def authority_pm_metadata_eq_000000_90 : RelationFact :=
  .tensorEq .pm 90 .pm 91

private def anchor_sm_shape_10 : RelationFact :=
  .tensorShape .sm 10 [12, 2, 2]

private def state_000000 : RelationState where
  facts := [anchor_sm_shape_10, authority_cross_metadata_eq_90_90, authority_packed_cu_000000, authority_pm_metadata_eq_000000_90, fact_000000, fact_000001, fact_000002]
  nonempty := by decide

private def state_000001 : RelationState where
  facts := [anchor_sm_shape_10, authority_cross_metadata_eq_90_90, authority_packed_cu_000000, authority_pm_metadata_eq_000000_90, fact_000001, fact_000002, fact_000004]
  nonempty := by decide

private def state_000002 : RelationState where
  facts := [anchor_sm_shape_10, authority_cross_metadata_eq_90_90, authority_packed_cu_000000, authority_pm_metadata_eq_000000_90, fact_000004, fact_000005]
  nonempty := by decide

private def state_000003 : RelationState where
  facts := [anchor_sm_shape_10, fact_000003, fact_000004, fact_000005]
  nonempty := by decide

private def segment_000000 :
    ClosedDepSegmentCertificate CPKAttention.smGraph CPKAttention.pmGraph state_000000 state_000001 where
  smNodes := [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [10, 90], outs := [20], params := [1, 0] }]
  pmNodes := [{ rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }, { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] }]
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [10, 90], outs := [20], params := [1, 0] }]
    let pmNodes : List NodeDecl := [{ rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }, { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] }]
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful CPKAttention.smGraph) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore
    have hframe : state_000000.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hSource : fact_000000.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 10) [pmStore 100, pmStore 101, pmStore 102] 0 [12, 2, 2] [4, 2, 2] at hSource
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
      have hw : smFinal 20 = ZigzagCollective.fw_maybe_shuffle_collective [([].foldl (applyNodeDistributedFaithful CPKAttention.smGraph) smStore) 10] (decodeCuSeqlens (([].foldl (applyNodeDistributedFaithful CPKAttention.smGraph) smStore) 90)) 1 0 := by
        simpa [smFinal, smNodes] using
          (foldl_faithful_middle_writer CPKAttention.smGraph smStore [] [] { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [10, 90], outs := [20], params := [1, 0] } 20
            (fun t => ZigzagCollective.fw_maybe_shuffle_collective [t 10] (decodeCuSeqlens (t 90)) 1 0) (by
              intro t
              rw [applyNodeDistributedFaithful_shuffle_out]
              unfold applyNodeFaithfulShuffleValue
              rw [show CPKAttention.smGraph.replicaBuddies { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [10, 90], outs := [20], params := [1, 0] } = [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [10, 90], outs := [20], params := [1, 0] }] by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.smGraph [] smStore 10 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.smGraph [] smStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hPm0 : pmFinal 200 = ZigzagCollective.fw_maybe_shuffle_collective [pmStore 100, pmStore 101, pmStore 102] (decodeCuSeqlens (pmStore 90)) 3 0 := by
      have hw : pmFinal 200 = ZigzagCollective.fw_maybe_shuffle_collective [([{ rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 100, ([{ rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 101, ([{ rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 102] (decodeCuSeqlens (([{ rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 90)) 3 0 := by
        simpa [pmFinal, pmNodes] using
          (foldl_faithful_middle_writer CPKAttention.pmGraph pmStore [{ rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }] [{ rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] }] { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] } 200
            (fun t => ZigzagCollective.fw_maybe_shuffle_collective [t 100, t 101, t 102] (decodeCuSeqlens (t 90)) 3 0) (by
              intro t
              rw [applyNodeDistributedFaithful_shuffle_out]
              unfold applyNodeFaithfulShuffleValue
              rw [show CPKAttention.pmGraph.replicaBuddies { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] } = [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }] by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }] pmStore 100 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }] pmStore 101 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }] pmStore 102 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }] pmStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hPm1 : pmFinal 201 = ZigzagCollective.fw_maybe_shuffle_collective [pmStore 100, pmStore 101, pmStore 102] (decodeCuSeqlens (pmStore 90)) 3 1 := by
      have hw : pmFinal 201 = ZigzagCollective.fw_maybe_shuffle_collective [([{ rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }, { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 100, ([{ rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }, { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 101, ([{ rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }, { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 102] (decodeCuSeqlens (([{ rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }, { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 90)) 3 1 := by
        simpa [pmFinal, pmNodes] using
          (foldl_faithful_middle_writer CPKAttention.pmGraph pmStore [{ rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }, { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }] [] { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] } 201
            (fun t => ZigzagCollective.fw_maybe_shuffle_collective [t 100, t 101, t 102] (decodeCuSeqlens (t 90)) 3 1) (by
              intro t
              rw [applyNodeDistributedFaithful_shuffle_out]
              unfold applyNodeFaithfulShuffleValue
              rw [show CPKAttention.pmGraph.replicaBuddies { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] } = [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }] by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }, { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }] pmStore 100 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }, { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }] pmStore 101 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }, { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }] pmStore 102 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }, { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }] pmStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hPm2 : pmFinal 202 = ZigzagCollective.fw_maybe_shuffle_collective [pmStore 100, pmStore 101, pmStore 102] (decodeCuSeqlens (pmStore 90)) 3 2 := by
      have hw : pmFinal 202 = ZigzagCollective.fw_maybe_shuffle_collective [([].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 100, ([].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 101, ([].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 102] (decodeCuSeqlens (([].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 90)) 3 2 := by
        simpa [pmFinal, pmNodes] using
          (foldl_faithful_middle_writer CPKAttention.pmGraph pmStore [] [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] }] { rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] } 202
            (fun t => ZigzagCollective.fw_maybe_shuffle_collective [t 100, t 101, t 102] (decodeCuSeqlens (t 90)) 3 2) (by
              intro t
              rw [applyNodeDistributedFaithful_shuffle_out]
              unfold applyNodeFaithfulShuffleValue
              rw [show CPKAttention.pmGraph.replicaBuddies { rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] } = [{ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [100, 90], outs := [200], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [101, 90], outs := [201], params := [3, 1] }, { rank := 2, op := "OpName.FW_maybe_shuffle", ins := [102, 90], outs := [202], params := [3, 2] }] by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [] pmStore 100 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [] pmStore 101 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [] pmStore 102 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [] pmStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hSmValue : smFinal 20 = smStore 10 := by
      simpa [ZigzagCollective.fw_maybe_shuffle_collective] using hSm
    have hMetadataFinal : pmFinal 90 = pmStore 90 :=
      foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph pmNodes pmStore 90 (by native_decide) (by native_decide)
    have hOut : fact_000004.Holds smFinal pmFinal := by
      change ZigzagKRel (smFinal 20) [pmFinal 200, pmFinal 201, pmFinal 202] (pmFinal 90) [12, 2, 2] [4, 2, 2]
      rw [hSmValue, hPm0, hPm1, hPm2, hMetadataFinal]
      exact core
    intro fact hfact
    have covered : fact ∈ [fact_000004] ++ state_000000.facts := by
      exact (show state_000001.facts ⊆ [fact_000004] ++ state_000000.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | hold
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hOut
    · exact hframe fact hold

private def segment_000001 :
    ClosedDepSegmentCertificate CPKAttention.smGraph CPKAttention.pmGraph state_000001 state_000002 where
  smNodes := [{ rank := 0, op := "OpName.FW_attn_zigzag", ins := [20, 11, 12, 90, 90], outs := [30], params := [2, 1, 2, 3, 1, 0] }]
  pmNodes := [{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }, { rank := 1, op := "OpName.FW_attn_zigzag", ins := [201, 111, 121, 90, 90], outs := [301], params := [2, 1, 2, 3, 1, 0] }]
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_attn_zigzag", ins := [20, 11, 12, 90, 90], outs := [30], params := [2, 1, 2, 3, 1, 0] }]
    let pmNodes : List NodeDecl := [{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }, { rank := 1, op := "OpName.FW_attn_zigzag", ins := [201, 111, 121, 90, 90], outs := [301], params := [2, 1, 2, 3, 1, 0] }]
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful CPKAttention.smGraph) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore
    have hframe : state_000001.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hQ : fact_000004.Holds smStore pmStore := hstate _ (by native_decide)
    change ZigzagKRel (smStore 20) [pmStore 200, pmStore 201, pmStore 202] (pmStore 90) [12, 2, 2] [4, 2, 2] at hQ
    have hK : fact_000001.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 11) [pmStore 110, pmStore 111, pmStore 112] 0 [12, 1, 2] [4, 1, 2] at hK
    have hV : fact_000002.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 12) [pmStore 120, pmStore 121, pmStore 122] 0 [12, 1, 3] [4, 1, 3] at hV
    have hPacked := hstate authority_packed_cu_000000 (by native_decide)
    have hAlias := hstate authority_pm_metadata_eq_000000_90 (by native_decide)
    have hCross := hstate authority_cross_metadata_eq_90_90 (by native_decide)
    change ZigzagCollective.PackedCuSeqlensWF (pmStore 91) 12 3 at hPacked
    change pmStore 90 = pmStore 91 at hAlias
    change smStore 90 = pmStore 90 at hCross
    have hDecode : decodeCuSeqlens (pmStore 90) = [0, 3 * (2 * 2)] := by
      rw [hAlias]
      exact hPacked.decoded_single
    have core := ZigzagKRel.attn_zigzag_sharded_kv_single (smStore 20) (smStore 11) (smStore 12) (pmStore 90) (pmStore 90) [pmStore 200, pmStore 201, pmStore 202] [pmStore 110, pmStore 111, pmStore 112] [pmStore 120, pmStore 121, pmStore 122] 3 2 2 1 2 3
      hQ hK hV rfl rfl rfl hDecode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hSm : smFinal 30 = fw_attn_varlen (smStore 20) (smStore 11) (smStore 12) (smStore 90) (smStore 90) 2 1 2 3 true 0 := by
      have hw : smFinal 30 = fw_attn_varlen (([].foldl (applyNodeDistributedFaithful CPKAttention.smGraph) smStore) 20) (([].foldl (applyNodeDistributedFaithful CPKAttention.smGraph) smStore) 11) (([].foldl (applyNodeDistributedFaithful CPKAttention.smGraph) smStore) 12) (([].foldl (applyNodeDistributedFaithful CPKAttention.smGraph) smStore) 90) (([].foldl (applyNodeDistributedFaithful CPKAttention.smGraph) smStore) 90) 2 1 2 3 true 0 := by
        simpa [smFinal, smNodes] using
          (foldl_faithful_middle_writer CPKAttention.smGraph smStore [] [] { rank := 0, op := "OpName.FW_attn_zigzag", ins := [20, 11, 12, 90, 90], outs := [30], params := [2, 1, 2, 3, 1, 0] } 30
            (fun t => fw_attn_varlen (t 20) (t 11) (t 12) (t 90) (t 90) 2 1 2 3 true 0) (by
              intro t
              rw [applyNodeDistributedFaithful_zigzag_attn_out]
              dsimp only [applyNodeFaithfulZigzagAttnValue]
              rw [show zigzagAttnUsesReplicatedKV CPKAttention.smGraph { rank := 0, op := "OpName.FW_attn_zigzag", ins := [20, 11, 12, 90, 90], outs := [30], params := [2, 1, 2, 3, 1, 0] } = true by native_decide]
              rw [show CPKAttention.smGraph.replicaBuddies { rank := 0, op := "OpName.FW_attn_zigzag", ins := [20, 11, 12, 90, 90], outs := [30], params := [2, 1, 2, 3, 1, 0] } = [{ rank := 0, op := "OpName.FW_attn_zigzag", ins := [20, 11, 12, 90, 90], outs := [30], params := [2, 1, 2, 3, 1, 0] }] by native_decide]
              rw [show CPKAttention.smGraph.numRanks = 1 by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.smGraph [] smStore 20 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.smGraph [] smStore 11 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.smGraph [] smStore 12 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.smGraph [] smStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hPm0 : pmFinal 300 = ZigzagCollective.fw_attn_zigzag_collective_sharded_kv [pmStore 200, pmStore 201, pmStore 202] [pmStore 110, pmStore 111, pmStore 112] [pmStore 120, pmStore 121, pmStore 122] (pmStore 90) (pmStore 90) 2 1 2 3 true 0 3 0 := by
      have hw : pmFinal 300 = ZigzagCollective.fw_attn_zigzag_collective_sharded_kv [([{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 200, ([{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 201, ([{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 202] [([{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 110, ([{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 111, ([{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 112] [([{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 120, ([{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 121, ([{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 122] (([{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 90) (([{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 90) 2 1 2 3 true 0 3 0 := by
        simpa [pmFinal, pmNodes] using
          (foldl_faithful_middle_writer CPKAttention.pmGraph pmStore [{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }] [{ rank := 1, op := "OpName.FW_attn_zigzag", ins := [201, 111, 121, 90, 90], outs := [301], params := [2, 1, 2, 3, 1, 0] }] { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] } 300
            (fun t => ZigzagCollective.fw_attn_zigzag_collective_sharded_kv [t 200, t 201, t 202] [t 110, t 111, t 112] [t 120, t 121, t 122] (t 90) (t 90) 2 1 2 3 true 0 3 0) (by
              intro t
              rw [applyNodeDistributedFaithful_zigzag_attn_out]
              dsimp only [applyNodeFaithfulZigzagAttnValue]
              rw [show zigzagAttnUsesReplicatedKV CPKAttention.pmGraph { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] } = false by native_decide]
              rw [show CPKAttention.pmGraph.replicaBuddies { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] } = [{ rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }, { rank := 1, op := "OpName.FW_attn_zigzag", ins := [201, 111, 121, 90, 90], outs := [301], params := [2, 1, 2, 3, 1, 0] }, { rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }] by native_decide]
              rw [show CPKAttention.pmGraph.numRanks = 3 by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }] pmStore 200 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }] pmStore 110 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }] pmStore 120 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }] pmStore 90 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }] pmStore 201 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }] pmStore 111 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }] pmStore 121 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }] pmStore 202 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }] pmStore 112 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }] pmStore 122 (by native_decide) (by native_decide)] at hw
      exact hw
    have hRef0 := ZigzagKRel.sourceOutput_eq_collective (smStore 20) (smStore 11) (smStore 12) (pmStore 90) [pmStore 200, pmStore 201, pmStore 202] [pmStore 110, pmStore 111, pmStore 112] [pmStore 120, pmStore 121, pmStore 122] 3 0 2 2 1 2 3
      hQ hK hV rfl rfl rfl hDecode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hPmSource0 := hPm0.trans hRef0.symm
    have hPm1 : pmFinal 301 = ZigzagCollective.fw_attn_zigzag_collective_sharded_kv [pmStore 200, pmStore 201, pmStore 202] [pmStore 110, pmStore 111, pmStore 112] [pmStore 120, pmStore 121, pmStore 122] (pmStore 90) (pmStore 90) 2 1 2 3 true 0 3 1 := by
      have hw : pmFinal 301 = ZigzagCollective.fw_attn_zigzag_collective_sharded_kv [([{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 200, ([{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 201, ([{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 202] [([{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 110, ([{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 111, ([{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 112] [([{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 120, ([{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 121, ([{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 122] (([{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 90) (([{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 90) 2 1 2 3 true 0 3 1 := by
        simpa [pmFinal, pmNodes] using
          (foldl_faithful_middle_writer CPKAttention.pmGraph pmStore [{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }] [] { rank := 1, op := "OpName.FW_attn_zigzag", ins := [201, 111, 121, 90, 90], outs := [301], params := [2, 1, 2, 3, 1, 0] } 301
            (fun t => ZigzagCollective.fw_attn_zigzag_collective_sharded_kv [t 200, t 201, t 202] [t 110, t 111, t 112] [t 120, t 121, t 122] (t 90) (t 90) 2 1 2 3 true 0 3 1) (by
              intro t
              rw [applyNodeDistributedFaithful_zigzag_attn_out]
              dsimp only [applyNodeFaithfulZigzagAttnValue]
              rw [show zigzagAttnUsesReplicatedKV CPKAttention.pmGraph { rank := 1, op := "OpName.FW_attn_zigzag", ins := [201, 111, 121, 90, 90], outs := [301], params := [2, 1, 2, 3, 1, 0] } = false by native_decide]
              rw [show CPKAttention.pmGraph.replicaBuddies { rank := 1, op := "OpName.FW_attn_zigzag", ins := [201, 111, 121, 90, 90], outs := [301], params := [2, 1, 2, 3, 1, 0] } = [{ rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }, { rank := 1, op := "OpName.FW_attn_zigzag", ins := [201, 111, 121, 90, 90], outs := [301], params := [2, 1, 2, 3, 1, 0] }, { rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }] by native_decide]
              rw [show CPKAttention.pmGraph.numRanks = 3 by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }] pmStore 200 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }] pmStore 110 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }] pmStore 120 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }] pmStore 90 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }] pmStore 201 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }] pmStore 111 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }] pmStore 121 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }] pmStore 202 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }] pmStore 112 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }] pmStore 122 (by native_decide) (by native_decide)] at hw
      exact hw
    have hRef1 := ZigzagKRel.sourceOutput_eq_collective (smStore 20) (smStore 11) (smStore 12) (pmStore 90) [pmStore 200, pmStore 201, pmStore 202] [pmStore 110, pmStore 111, pmStore 112] [pmStore 120, pmStore 121, pmStore 122] 3 1 2 2 1 2 3
      hQ hK hV rfl rfl rfl hDecode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hPmSource1 := hPm1.trans hRef1.symm
    have hPm2 : pmFinal 302 = ZigzagCollective.fw_attn_zigzag_collective_sharded_kv [pmStore 200, pmStore 201, pmStore 202] [pmStore 110, pmStore 111, pmStore 112] [pmStore 120, pmStore 121, pmStore 122] (pmStore 90) (pmStore 90) 2 1 2 3 true 0 3 2 := by
      have hw : pmFinal 302 = ZigzagCollective.fw_attn_zigzag_collective_sharded_kv [([].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 200, ([].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 201, ([].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 202] [([].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 110, ([].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 111, ([].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 112] [([].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 120, ([].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 121, ([].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 122] (([].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 90) (([].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 90) 2 1 2 3 true 0 3 2 := by
        simpa [pmFinal, pmNodes] using
          (foldl_faithful_middle_writer CPKAttention.pmGraph pmStore [] [{ rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }, { rank := 1, op := "OpName.FW_attn_zigzag", ins := [201, 111, 121, 90, 90], outs := [301], params := [2, 1, 2, 3, 1, 0] }] { rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] } 302
            (fun t => ZigzagCollective.fw_attn_zigzag_collective_sharded_kv [t 200, t 201, t 202] [t 110, t 111, t 112] [t 120, t 121, t 122] (t 90) (t 90) 2 1 2 3 true 0 3 2) (by
              intro t
              rw [applyNodeDistributedFaithful_zigzag_attn_out]
              dsimp only [applyNodeFaithfulZigzagAttnValue]
              rw [show zigzagAttnUsesReplicatedKV CPKAttention.pmGraph { rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] } = false by native_decide]
              rw [show CPKAttention.pmGraph.replicaBuddies { rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] } = [{ rank := 0, op := "OpName.FW_attn_zigzag", ins := [200, 110, 120, 90, 90], outs := [300], params := [2, 1, 2, 3, 1, 0] }, { rank := 1, op := "OpName.FW_attn_zigzag", ins := [201, 111, 121, 90, 90], outs := [301], params := [2, 1, 2, 3, 1, 0] }, { rank := 2, op := "OpName.FW_attn_zigzag", ins := [202, 112, 122, 90, 90], outs := [302], params := [2, 1, 2, 3, 1, 0] }] by native_decide]
              rw [show CPKAttention.pmGraph.numRanks = 3 by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [] pmStore 200 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [] pmStore 110 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [] pmStore 120 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [] pmStore 90 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [] pmStore 201 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [] pmStore 111 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [] pmStore 121 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [] pmStore 202 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [] pmStore 112 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [] pmStore 122 (by native_decide) (by native_decide)] at hw
      exact hw
    have hRef2 := ZigzagKRel.sourceOutput_eq_collective (smStore 20) (smStore 11) (smStore 12) (pmStore 90) [pmStore 200, pmStore 201, pmStore 202] [pmStore 110, pmStore 111, pmStore 112] [pmStore 120, pmStore 121, pmStore 122] 3 2 2 2 1 2 3
      hQ hK hV rfl rfl rfl hDecode (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hPmSource2 := hPm2.trans hRef2.symm
    have hMetadataFinal : pmFinal 90 = pmStore 90 :=
      foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph pmNodes pmStore 90 (by native_decide) (by native_decide)
    have hOut : fact_000005.Holds smFinal pmFinal := by
      change ZigzagKRel (smFinal 30) [pmFinal 300, pmFinal 301, pmFinal 302] (pmFinal 90) [12, 2, 3] [4, 2, 3]
      rw [hSm, hCross, hPmSource0, hRef0, hPmSource1, hRef1, hPmSource2, hRef2, hMetadataFinal]
      exact core
    intro fact hfact
    have covered : fact ∈ [fact_000005] ++ state_000001.facts := by
      exact (show state_000002.facts ⊆ [fact_000005] ++ state_000001.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | hold
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hOut
    · exact hframe fact hold

private def segment_000002 :
    ClosedDepSegmentCertificate CPKAttention.smGraph CPKAttention.pmGraph state_000002 state_000003 where
  smNodes := [{ rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [30, 90], outs := [40], params := [1, 0] }]
  pmNodes := [{ rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] }, { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [300, 90], outs := [400], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [301, 90], outs := [401], params := [3, 1] }]
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [30, 90], outs := [40], params := [1, 0] }]
    let pmNodes : List NodeDecl := [{ rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] }, { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [300, 90], outs := [400], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [301, 90], outs := [401], params := [3, 1] }]
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful CPKAttention.smGraph) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore
    have hframe : state_000002.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hSource : fact_000005.Holds smStore pmStore := hstate _ (by native_decide)
    change ZigzagKRel (smStore 30) [pmStore 300, pmStore 301, pmStore 302] (pmStore 90) [12, 2, 3] [4, 2, 3] at hSource
    have hPacked : authority_packed_cu_000000.Holds smStore pmStore := hstate _ (by native_decide)
    have hAlias : authority_pm_metadata_eq_000000_90.Holds smStore pmStore := hstate _ (by native_decide)
    change ZigzagCollective.PackedCuSeqlensWF (pmStore 91) 12 3 at hPacked
    change pmStore 90 = pmStore 91 at hAlias
    have hPackedActual : ZigzagCollective.PackedCuSeqlensWF (pmStore 90) 12 3 := by
      rw [hAlias]
      exact hPacked
    have hDecode : decodeCuSeqlens (pmStore 90) = [0, 3 * 4] := hPackedActual.decoded_single
    have core := ZigzagKRel.to_sharded_unshuffle_single (d := 2) hSource (by decide) hDecode
    have hSm : smFinal 40 = ZigzagCollective.fw_maybe_unshuffle_collective [smStore 30] (decodeCuSeqlens (smStore 90)) 1 0 := by
      have hw : smFinal 40 = ZigzagCollective.fw_maybe_unshuffle_collective [([].foldl (applyNodeDistributedFaithful CPKAttention.smGraph) smStore) 30] (decodeCuSeqlens (([].foldl (applyNodeDistributedFaithful CPKAttention.smGraph) smStore) 90)) 1 0 := by
        simpa [smFinal, smNodes] using
          (foldl_faithful_middle_writer CPKAttention.smGraph smStore [] [] { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [30, 90], outs := [40], params := [1, 0] } 40
            (fun t => ZigzagCollective.fw_maybe_unshuffle_collective [t 30] (decodeCuSeqlens (t 90)) 1 0) (by
              intro t
              rw [applyNodeDistributedFaithful_unshuffle_out]
              unfold applyNodeFaithfulUnshuffleValue
              rw [show CPKAttention.smGraph.replicaBuddies { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [30, 90], outs := [40], params := [1, 0] } = [{ rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [30, 90], outs := [40], params := [1, 0] }] by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.smGraph [] smStore 30 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.smGraph [] smStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hPm0 : pmFinal 400 = ZigzagCollective.fw_maybe_unshuffle_collective [pmStore 300, pmStore 301, pmStore 302] (decodeCuSeqlens (pmStore 90)) 3 0 := by
      have hw : pmFinal 400 = ZigzagCollective.fw_maybe_unshuffle_collective [([{ rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 300, ([{ rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 301, ([{ rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 302] (decodeCuSeqlens (([{ rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 90)) 3 0 := by
        simpa [pmFinal, pmNodes] using
          (foldl_faithful_middle_writer CPKAttention.pmGraph pmStore [{ rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] }] [{ rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [301, 90], outs := [401], params := [3, 1] }] { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [300, 90], outs := [400], params := [3, 0] } 400
            (fun t => ZigzagCollective.fw_maybe_unshuffle_collective [t 300, t 301, t 302] (decodeCuSeqlens (t 90)) 3 0) (by
              intro t
              rw [applyNodeDistributedFaithful_unshuffle_out]
              unfold applyNodeFaithfulUnshuffleValue
              rw [show CPKAttention.pmGraph.replicaBuddies { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [300, 90], outs := [400], params := [3, 0] } = [{ rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [300, 90], outs := [400], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [301, 90], outs := [401], params := [3, 1] }, { rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] }] by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] }] pmStore 300 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] }] pmStore 301 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] }] pmStore 302 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] }] pmStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hPm1 : pmFinal 401 = ZigzagCollective.fw_maybe_unshuffle_collective [pmStore 300, pmStore 301, pmStore 302] (decodeCuSeqlens (pmStore 90)) 3 1 := by
      have hw : pmFinal 401 = ZigzagCollective.fw_maybe_unshuffle_collective [([{ rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] }, { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [300, 90], outs := [400], params := [3, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 300, ([{ rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] }, { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [300, 90], outs := [400], params := [3, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 301, ([{ rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] }, { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [300, 90], outs := [400], params := [3, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 302] (decodeCuSeqlens (([{ rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] }, { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [300, 90], outs := [400], params := [3, 0] }].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 90)) 3 1 := by
        simpa [pmFinal, pmNodes] using
          (foldl_faithful_middle_writer CPKAttention.pmGraph pmStore [{ rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] }, { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [300, 90], outs := [400], params := [3, 0] }] [] { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [301, 90], outs := [401], params := [3, 1] } 401
            (fun t => ZigzagCollective.fw_maybe_unshuffle_collective [t 300, t 301, t 302] (decodeCuSeqlens (t 90)) 3 1) (by
              intro t
              rw [applyNodeDistributedFaithful_unshuffle_out]
              unfold applyNodeFaithfulUnshuffleValue
              rw [show CPKAttention.pmGraph.replicaBuddies { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [301, 90], outs := [401], params := [3, 1] } = [{ rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [300, 90], outs := [400], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [301, 90], outs := [401], params := [3, 1] }, { rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] }] by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] }, { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [300, 90], outs := [400], params := [3, 0] }] pmStore 300 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] }, { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [300, 90], outs := [400], params := [3, 0] }] pmStore 301 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] }, { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [300, 90], outs := [400], params := [3, 0] }] pmStore 302 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [{ rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] }, { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [300, 90], outs := [400], params := [3, 0] }] pmStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hPm2 : pmFinal 402 = ZigzagCollective.fw_maybe_unshuffle_collective [pmStore 300, pmStore 301, pmStore 302] (decodeCuSeqlens (pmStore 90)) 3 2 := by
      have hw : pmFinal 402 = ZigzagCollective.fw_maybe_unshuffle_collective [([].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 300, ([].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 301, ([].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 302] (decodeCuSeqlens (([].foldl (applyNodeDistributedFaithful CPKAttention.pmGraph) pmStore) 90)) 3 2 := by
        simpa [pmFinal, pmNodes] using
          (foldl_faithful_middle_writer CPKAttention.pmGraph pmStore [] [{ rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [300, 90], outs := [400], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [301, 90], outs := [401], params := [3, 1] }] { rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] } 402
            (fun t => ZigzagCollective.fw_maybe_unshuffle_collective [t 300, t 301, t 302] (decodeCuSeqlens (t 90)) 3 2) (by
              intro t
              rw [applyNodeDistributedFaithful_unshuffle_out]
              unfold applyNodeFaithfulUnshuffleValue
              rw [show CPKAttention.pmGraph.replicaBuddies { rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] } = [{ rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [300, 90], outs := [400], params := [3, 0] }, { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [301, 90], outs := [401], params := [3, 1] }, { rank := 2, op := "OpName.FW_maybe_unshuffle", ins := [302, 90], outs := [402], params := [3, 2] }] by native_decide]
              rfl) (by native_decide) (by native_decide))
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [] pmStore 300 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [] pmStore 301 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [] pmStore 302 (by native_decide) (by native_decide)] at hw
      rw [foldl_applyNodeDistributedFaithful_at_not_written CPKAttention.pmGraph [] pmStore 90 (by native_decide) (by native_decide)] at hw
      exact hw
    have hSmValue : smFinal 40 = smStore 30 := by
      simpa [ZigzagCollective.fw_maybe_unshuffle_collective] using hSm
    have hOut : fact_000003.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 40) [pmFinal 400, pmFinal 401, pmFinal 402] 0 [12, 2, 3] [4, 2, 3]
      rw [hSmValue, hPm0, hPm1, hPm2]
      exact core
    intro fact hfact
    have covered : fact ∈ [fact_000003] ++ state_000002.facts := by
      exact (show state_000003.facts ⊆ [fact_000003] ++ state_000002.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | hold
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hOut
    · exact hframe fact hold

private def composed : ClosedDepSegmentCertificate CPKAttention.smGraph CPKAttention.pmGraph state_000000 state_000003 where
  smNodes := CPKAttention.smGraph.nodes
  pmNodes := CPKAttention.pmGraph.nodes
  sound := by
    intro sm pm h
    rw [show CPKAttention.smGraph.nodes = (segment_000000.smNodes ++ segment_000001.smNodes) ++ segment_000002.smNodes by native_decide]
    rw [show CPKAttention.pmGraph.nodes = (segment_000000.pmNodes ++ segment_000001.pmNodes) ++ segment_000002.pmNodes by native_decide]
    simp only [List.foldl_append]
    exact segment_000002.sound _ _ (segment_000001.sound _ _ (segment_000000.sound sm pm h))
private theorem CPKAttentionProof_anchor_sm_shape_10_from_external_inputs
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM CPKAttention.smGraphInitEnv)
    (hPM : StoreShapesHold initPM CPKAttention.pmGraphInitEnv)
    (hInit : InitGoalsHold CPKAttention.pmGraph.numRanks CPKAttention.initGoals initSM initPM)
    (hSMValues : InputValueClassesHold CPKAttention.smInputValueClasses initSM)
    (hPMValues : InputValueClassesHold CPKAttention.pmInputValueClasses initPM)
    (hPacked_0 : ZigzagCollective.PackedCuSeqlensWF (initPM 91) 12 3)
    : anchor_sm_shape_10.Holds initSM initPM := by
  unfold anchor_sm_shape_10 RelationFact.Holds StoreSide.read
  exact hSM 10 [12, 2, 2] (by native_decide)
private theorem CPKAttentionProof_authority_cross_metadata_eq_90_90_from_external_inputs
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM CPKAttention.smGraphInitEnv)
    (hPM : StoreShapesHold initPM CPKAttention.pmGraphInitEnv)
    (hInit : InitGoalsHold CPKAttention.pmGraph.numRanks CPKAttention.initGoals initSM initPM)
    (hSMValues : InputValueClassesHold CPKAttention.smInputValueClasses initSM)
    (hPMValues : InputValueClassesHold CPKAttention.pmInputValueClasses initPM)
    (hPacked_0 : ZigzagCollective.PackedCuSeqlensWF (initPM 91) 12 3)
    : authority_cross_metadata_eq_90_90.Holds initSM initPM := by
  unfold authority_cross_metadata_eq_90_90 RelationFact.Holds StoreSide.read
  have hi := hInit CPKAttention.initGoal_90 (by native_decide)
  exact InitGoalHolds.singleton_value_eq CPKAttention.pmGraph.numRanks CPKAttention.initGoal_90 initSM initPM
    { rank := 0, tid := 90 } hi rfl
private theorem CPKAttentionProof_authority_packed_cu_000000_from_external_inputs
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM CPKAttention.smGraphInitEnv)
    (hPM : StoreShapesHold initPM CPKAttention.pmGraphInitEnv)
    (hInit : InitGoalsHold CPKAttention.pmGraph.numRanks CPKAttention.initGoals initSM initPM)
    (hSMValues : InputValueClassesHold CPKAttention.smInputValueClasses initSM)
    (hPMValues : InputValueClassesHold CPKAttention.pmInputValueClasses initPM)
    (hPacked_0 : ZigzagCollective.PackedCuSeqlensWF (initPM 91) 12 3)
    : authority_packed_cu_000000.Holds initSM initPM := by
  unfold authority_packed_cu_000000 RelationFact.Holds StoreSide.read
  exact hPacked_0
private theorem CPKAttentionProof_authority_pm_metadata_eq_000000_90_from_external_inputs
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM CPKAttention.smGraphInitEnv)
    (hPM : StoreShapesHold initPM CPKAttention.pmGraphInitEnv)
    (hInit : InitGoalsHold CPKAttention.pmGraph.numRanks CPKAttention.initGoals initSM initPM)
    (hSMValues : InputValueClassesHold CPKAttention.smInputValueClasses initSM)
    (hPMValues : InputValueClassesHold CPKAttention.pmInputValueClasses initPM)
    (hPacked_0 : ZigzagCollective.PackedCuSeqlensWF (initPM 91) 12 3)
    : authority_pm_metadata_eq_000000_90.Holds initSM initPM := by
  unfold authority_pm_metadata_eq_000000_90 RelationFact.Holds StoreSide.read
  exact InputValueClassesHold.eq_of_mem hPMValues
    (c := CPKAttention.pmInputValueClasses[0]'(by native_decide))
    (by native_decide) (by native_decide) (by native_decide)
private theorem CPKAttentionProof_fact_000000_from_external_inputs
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM CPKAttention.smGraphInitEnv)
    (hPM : StoreShapesHold initPM CPKAttention.pmGraphInitEnv)
    (hInit : InitGoalsHold CPKAttention.pmGraph.numRanks CPKAttention.initGoals initSM initPM)
    (hSMValues : InputValueClassesHold CPKAttention.smInputValueClasses initSM)
    (hPMValues : InputValueClassesHold CPKAttention.pmInputValueClasses initPM)
    (hPacked_0 : ZigzagCollective.PackedCuSeqlensWF (initPM 91) 12 3)
    : fact_000000.Holds initSM initPM := by
  unfold fact_000000 RelationFact.Holds StoreSide.read
  -- ordered PM TIDs: [100, 101, 102]
  have hi := hInit CPKAttention.initGoal_10 (by native_decide)
  have htps : CPKAttention.initGoal_10.tps = [{ rank := 0, tid := 100 }, { rank := 1, tid := 101 }, { rank := 2, tid := 102 }] := by native_decide
  have hfull := hSM 10 [12, 2, 2] (by native_decide)
  have hp0 := hPM 100 [4, 2, 2] (by native_decide)
  have hp1 := hPM 101 [4, 2, 2] (by native_decide)
  have hp2 := hPM 102 [4, 2, 2] (by native_decide)
  have hrel := ShardedRel.of_init_goal CPKAttention.pmGraph.numRanks CPKAttention.initGoal_10 initSM initPM 0 [12, 2, 2] [4, 2, 2]
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
  simpa [CPKAttention.initGoal_10] using hrel
private theorem CPKAttentionProof_fact_000001_from_external_inputs
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM CPKAttention.smGraphInitEnv)
    (hPM : StoreShapesHold initPM CPKAttention.pmGraphInitEnv)
    (hInit : InitGoalsHold CPKAttention.pmGraph.numRanks CPKAttention.initGoals initSM initPM)
    (hSMValues : InputValueClassesHold CPKAttention.smInputValueClasses initSM)
    (hPMValues : InputValueClassesHold CPKAttention.pmInputValueClasses initPM)
    (hPacked_0 : ZigzagCollective.PackedCuSeqlensWF (initPM 91) 12 3)
    : fact_000001.Holds initSM initPM := by
  unfold fact_000001 RelationFact.Holds StoreSide.read
  -- ordered PM TIDs: [110, 111, 112]
  have hi := hInit CPKAttention.initGoal_11 (by native_decide)
  have htps : CPKAttention.initGoal_11.tps = [{ rank := 0, tid := 110 }, { rank := 1, tid := 111 }, { rank := 2, tid := 112 }] := by native_decide
  have hfull := hSM 11 [12, 1, 2] (by native_decide)
  have hp0 := hPM 110 [4, 1, 2] (by native_decide)
  have hp1 := hPM 111 [4, 1, 2] (by native_decide)
  have hp2 := hPM 112 [4, 1, 2] (by native_decide)
  have hrel := ShardedRel.of_init_goal CPKAttention.pmGraph.numRanks CPKAttention.initGoal_11 initSM initPM 0 [12, 1, 2] [4, 1, 2]
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
  simpa [CPKAttention.initGoal_11] using hrel
private theorem CPKAttentionProof_fact_000002_from_external_inputs
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM CPKAttention.smGraphInitEnv)
    (hPM : StoreShapesHold initPM CPKAttention.pmGraphInitEnv)
    (hInit : InitGoalsHold CPKAttention.pmGraph.numRanks CPKAttention.initGoals initSM initPM)
    (hSMValues : InputValueClassesHold CPKAttention.smInputValueClasses initSM)
    (hPMValues : InputValueClassesHold CPKAttention.pmInputValueClasses initPM)
    (hPacked_0 : ZigzagCollective.PackedCuSeqlensWF (initPM 91) 12 3)
    : fact_000002.Holds initSM initPM := by
  unfold fact_000002 RelationFact.Holds StoreSide.read
  -- ordered PM TIDs: [120, 121, 122]
  have hi := hInit CPKAttention.initGoal_12 (by native_decide)
  have htps : CPKAttention.initGoal_12.tps = [{ rank := 0, tid := 120 }, { rank := 1, tid := 121 }, { rank := 2, tid := 122 }] := by native_decide
  have hfull := hSM 12 [12, 1, 3] (by native_decide)
  have hp0 := hPM 120 [4, 1, 3] (by native_decide)
  have hp1 := hPM 121 [4, 1, 3] (by native_decide)
  have hp2 := hPM 122 [4, 1, 3] (by native_decide)
  have hrel := ShardedRel.of_init_goal CPKAttention.pmGraph.numRanks CPKAttention.initGoal_12 initSM initPM 0 [12, 1, 3] [4, 1, 3]
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
  simpa [CPKAttention.initGoal_12] using hrel
private theorem CPKAttentionProof_initial_chunk_000
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM CPKAttention.smGraphInitEnv)
    (hPM : StoreShapesHold initPM CPKAttention.pmGraphInitEnv)
    (hInit : InitGoalsHold CPKAttention.pmGraph.numRanks CPKAttention.initGoals initSM initPM)
    (hSMValues : InputValueClassesHold CPKAttention.smInputValueClasses initSM)
    (hPMValues : InputValueClassesHold CPKAttention.pmInputValueClasses initPM)
    (hPacked_0 : ZigzagCollective.PackedCuSeqlensWF (initPM 91) 12 3)
    (fact : RelationFact) (hfact : fact ∈ [anchor_sm_shape_10, authority_cross_metadata_eq_90_90, authority_packed_cu_000000, authority_pm_metadata_eq_000000_90, fact_000000, fact_000001, fact_000002])
    : fact.Holds initSM initPM := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfact
  rcases hfact with rfl | hfact
  · exact CPKAttentionProof_anchor_sm_shape_10_from_external_inputs initSM initPM hSM hPM hInit hSMValues hPMValues hPacked_0
  rcases hfact with rfl | hfact
  · exact CPKAttentionProof_authority_cross_metadata_eq_90_90_from_external_inputs initSM initPM hSM hPM hInit hSMValues hPMValues hPacked_0
  rcases hfact with rfl | hfact
  · exact CPKAttentionProof_authority_packed_cu_000000_from_external_inputs initSM initPM hSM hPM hInit hSMValues hPMValues hPacked_0
  rcases hfact with rfl | hfact
  · exact CPKAttentionProof_authority_pm_metadata_eq_000000_90_from_external_inputs initSM initPM hSM hPM hInit hSMValues hPMValues hPacked_0
  rcases hfact with rfl | hfact
  · exact CPKAttentionProof_fact_000000_from_external_inputs initSM initPM hSM hPM hInit hSMValues hPMValues hPacked_0
  rcases hfact with rfl | hfact
  · exact CPKAttentionProof_fact_000001_from_external_inputs initSM initPM hSM hPM hInit hSMValues hPMValues hPacked_0
  subst fact
  exact CPKAttentionProof_fact_000002_from_external_inputs initSM initPM hSM hPM hInit hSMValues hPMValues hPacked_0
private theorem CPKAttentionProof_initial_state
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM CPKAttention.smGraphInitEnv)
    (hPM : StoreShapesHold initPM CPKAttention.pmGraphInitEnv)
    (hInit : InitGoalsHold CPKAttention.pmGraph.numRanks CPKAttention.initGoals initSM initPM)
    (hSMValues : InputValueClassesHold CPKAttention.smInputValueClasses initSM)
    (hPMValues : InputValueClassesHold CPKAttention.pmInputValueClasses initPM)
    (hPacked_0 : ZigzagCollective.PackedCuSeqlensWF (initPM 91) 12 3)
    : state_000000.Holds initSM initPM := by
  intro fact hfact
  have covered : fact ∈ [anchor_sm_shape_10, authority_cross_metadata_eq_90_90, authority_packed_cu_000000, authority_pm_metadata_eq_000000_90, fact_000000, fact_000001, fact_000002] := by
    exact (show state_000000.facts ⊆ [anchor_sm_shape_10, authority_cross_metadata_eq_90_90, authority_packed_cu_000000, authority_pm_metadata_eq_000000_90, fact_000000, fact_000001, fact_000002] by native_decide) hfact
  exact CPKAttentionProof_initial_chunk_000 initSM initPM hSM hPM hInit hSMValues hPMValues hPacked_0 fact covered

@[irreducible] private def CPKAttentionProof_target_statement (initSM initPM : Store) : Prop :=
  fact_000003.Holds (denoteGraphDistributedFaithful CPKAttention.smGraph initSM) (denoteGraphDistributedFaithful CPKAttention.pmGraph initPM)
private theorem CPKAttentionProof_target_from_external_inputs
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM CPKAttention.smGraphInitEnv)
    (hPM : StoreShapesHold initPM CPKAttention.pmGraphInitEnv)
    (hInit : InitGoalsHold CPKAttention.pmGraph.numRanks CPKAttention.initGoals initSM initPM)
    (hSMValues : InputValueClassesHold CPKAttention.smInputValueClasses initSM)
    (hPMValues : InputValueClassesHold CPKAttention.pmInputValueClasses initPM)
    (hPacked_0 : ZigzagCollective.PackedCuSeqlensWF (initPM 91) 12 3)
    : CPKAttentionProof_target_statement initSM initPM := by
  unfold CPKAttentionProof_target_statement
  have hpre := CPKAttentionProof_initial_state initSM initPM hSM hPM hInit hSMValues hPMValues hPacked_0
  have h := composed.sound initSM initPM hpre
  exact h fact_000003 (by native_decide)

private theorem CPKAttentionProof_sharded_target_publication (smStore pmStore : Store)
    (htarget : fact_000003.Holds smStore pmStore) :
    let ts := smStore CPKAttention.exitGoal.ts
    let tps := CPKAttention.exitGoal.tps.map (fun p => pmStore p.tid)
    ts.shape = CPKAttention.exitGoal.tsShape ∧
      (tps.map (fun t => t.shape)) = CPKAttention.exitGoal.tpShapes ∧
      ts = reconstructForGoal CPKAttention.exitGoal CPKAttention.pmGraph.numRanks tps := by
  refine ⟨htarget.full_shape, ?_, ?_⟩
  · change [(pmStore 400).shape, (pmStore 401).shape, (pmStore 402).shape] = [[4, 2, 3], [4, 2, 3], [4, 2, 3]]
    rw [htarget.shard_shapes (pmStore 400) (by simp), htarget.shard_shapes (pmStore 401) (by simp), htarget.shard_shapes (pmStore 402) (by simp)]
  · rw [reconstructForGoal_of_not_replicated CPKAttention.exitGoal CPKAttention.pmGraph.numRanks _ rfl]
    simp only [CPKAttention.exitGoal, List.map]
    rw [reconstructWithDim_cons_cons_nonscalar 0 CPKAttention.pmGraph.numRanks 0 (pmStore 400) (pmStore 401) [pmStore 402] (by
      rw [htarget.shard_shapes (pmStore 400) (by simp)]
      native_decide)]
    have hRankCount : CPKAttention.pmGraph.numRanks = [pmStore 400, pmStore 401, pmStore 402].length := by rfl
    rw [hRankCount]
    exact htarget.full_value

@[irreducible] private def CPKAttentionProof_public_body_statement (initSM initPM : Store) : Prop :=
  let smStore := denoteGraphDistributedFaithful CPKAttention.smGraph initSM
  let pmStore := denoteGraphDistributedFaithful CPKAttention.pmGraph initPM
  let ts := smStore CPKAttention.exitGoal.ts
  let tps := CPKAttention.exitGoal.tps.map (fun p => pmStore p.tid)
  ts.shape = CPKAttention.exitGoal.tsShape ∧
    (tps.map (fun t => t.shape)) = CPKAttention.exitGoal.tpShapes ∧
    ts = reconstructForGoal CPKAttention.exitGoal CPKAttention.pmGraph.numRanks tps
private theorem CPKAttentionProof_public_body_proof
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM CPKAttention.smGraphInitEnv)
    (hPM : StoreShapesHold initPM CPKAttention.pmGraphInitEnv)
    (hInit : InitGoalsHold CPKAttention.pmGraph.numRanks CPKAttention.initGoals initSM initPM)
    (hSMValues : InputValueClassesHold CPKAttention.smInputValueClasses initSM)
    (hPMValues : InputValueClassesHold CPKAttention.pmInputValueClasses initPM)
    (hPacked_0 : ZigzagCollective.PackedCuSeqlensWF (initPM 91) 12 3)
    : CPKAttentionProof_public_body_statement initSM initPM := by
  unfold CPKAttentionProof_public_body_statement
  have htarget := CPKAttentionProof_target_from_external_inputs initSM initPM hSM hPM hInit hSMValues hPMValues hPacked_0
  unfold CPKAttentionProof_target_statement fact_000003 RelationFact.Holds at htarget
  exact CPKAttentionProof_sharded_target_publication (denoteGraphDistributedFaithful CPKAttention.smGraph initSM) (denoteGraphDistributedFaithful CPKAttention.pmGraph initPM) htarget


@[irreducible] private def CPKAttentionProof_public_statement : Prop := CPKAttention.exitStatement
private theorem CPKAttentionProof_public_proof : CPKAttentionProof_public_statement := by
  unfold CPKAttentionProof_public_statement
  unfold CPKAttention.exitStatement
  unfold CoarseLineageHoldsWithInitDistributedFaithfulWithContract
  intro initSM initPM hSM hPM hInit hContract
  unfold CPKAttention.externalContract at hContract
  rcases hContract with ⟨hSMValues, hPMValues, hPacked_0⟩
  simpa only [CPKAttentionProof_public_body_statement, InitGoalHolds] using CPKAttentionProof_public_body_proof initSM initPM hSM hPM hInit hSMValues hPMValues hPacked_0

theorem prove_goal_0_closed : CPKAttention.exitStatement := by
  simpa only [CPKAttentionProof_public_statement] using CPKAttentionProof_public_proof

#print axioms prove_goal_0_closed
#print axioms CPKAttention.publicInputs

theorem inhabitedPublicOutput : InitGoalHolds 3 CPKAttention.exitGoal
    (denoteGraphDistributedFaithful CPKAttention.smGraph CPKAttention.initSM)
    (denoteGraphDistributedFaithful CPKAttention.pmGraph CPKAttention.initPM) :=
  prove_goal_0_closed CPKAttention.initSM CPKAttention.initPM CPKAttention.publicInputs.1
    CPKAttention.publicInputs.2.1 CPKAttention.publicInputs.2.2.1 CPKAttention.publicInputs.2.2.2
#print axioms inhabitedPublicOutput

end
end TrainVerify.Denote.CPKAttentionProof
