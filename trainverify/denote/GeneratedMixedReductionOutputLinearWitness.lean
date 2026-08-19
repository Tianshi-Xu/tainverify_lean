import denote.RelationCompiler
import denote.KRankLinearReduction
import denote.KRankLinearGather

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticReductionOutput
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := { numRanks := 1, nodes := [] }
def gPM : GraphDecl := { numRanks := 3, nodes := [] }
def fact_activation_0 : RelationFact := .sharded 100 [200,201,202] 2 [1,6,12] [1,6,4]
def fact_reduction_weight_0 : RelationFact := .sharded 300 [400,401,402] 1 [9,12] [9,4]
def fact_activation_1 : RelationFact := .sharded 101 [210,211,212] 2 [1,6,12] [1,6,4]
def fact_reduction_weight_1 : RelationFact := .sharded 301 [410,411,412] 1 [9,12] [9,4]
def fact_joined : RelationFact := .joined 700 701 [1,6,12]
def fact_output_weight : RelationFact := .sharded 702 [710,711,712] 0 [15,12] [5,12]
def fact_reduction_output_0 : RelationFact := .reduction 500 [600,601,602] [1,6,9]
def fact_reduction_output_1 : RelationFact := .reduction 501 [610,611,612] [1,6,9]
def fact_final : RelationFact := .sharded 703 [720,721,722] 2 [1,6,15] [1,6,5]
def state_pre : RelationState where
  facts := [fact_activation_0,fact_reduction_weight_0,fact_activation_1,fact_reduction_weight_1,fact_joined,fact_output_weight]
  nonempty := by decide
def state_post : RelationState where
  facts := [fact_reduction_output_0,fact_reduction_output_1,fact_final]
  nonempty := by decide

set_option maxHeartbeats 500000 in
private def segment_atomic_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [100, 300], outs := [500] }, { rank := 0, op := "OpName.FW_linear", ins := [101, 301], outs := [501] }, { rank := 0, op := "OpName.FW_linear", ins := [700, 702], outs := [703] }]
private def segment_atomic_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [200, 400], outs := [600] }, { rank := 0, op := "OpName.FW_linear", ins := [210, 410], outs := [610] }, { rank := 0, op := "OpName.FW_linear", ins := [701, 710], outs := [720] }, { rank := 1, op := "OpName.FW_linear", ins := [701, 711], outs := [721] }, { rank := 2, op := "OpName.FW_linear", ins := [701, 712], outs := [722] }, { rank := 1, op := "OpName.FW_linear", ins := [201, 401], outs := [601] }, { rank := 1, op := "OpName.FW_linear", ins := [211, 411], outs := [611] }, { rank := 2, op := "OpName.FW_linear", ins := [202, 402], outs := [602] }, { rank := 2, op := "OpName.FW_linear", ins := [212, 412], outs := [612] }]

set_option maxHeartbeats 500000 in
private def segment_atomic : ClosedDepSegmentCertificate SyntheticReductionOutput.gSM SyntheticReductionOutput.gPM state_pre state_post where
  smNodes := segment_atomic_sm_nodes
  pmNodes := segment_atomic_pm_nodes
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := segment_atomic_sm_nodes
    let pmNodes : List NodeDecl := segment_atomic_pm_nodes
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gSM) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hActivation0 : fact_activation_0.Holds smStore pmStore := hstate fact_activation_0 (by native_decide)
    change ShardedRel (smStore 100) ([200, 201, 202].map pmStore) 2 [1, 6, 12] [1, 6, 4] at hActivation0
    have hReductionWeight0 : fact_reduction_weight_0.Holds smStore pmStore := hstate fact_reduction_weight_0 (by native_decide)
    change ShardedRel (smStore 300) ([400, 401, 402].map pmStore) 1 [9, 12] [9, 4] at hReductionWeight0
    let pmActivationTids0 : List Tid := [200, 201, 202]
    let pmWeightTids0 : List Tid := [400, 401, 402]
    let pmOutputTids0 : List Tid := [600, 601, 602]
    let rankCount0 := pmActivationTids0.length
    have hReductionSm0 : smFinal 500 = fw_linear (smStore 100) (smStore 300) := by
      calc
        smFinal 500 = fw_linear ((smNodes.take 0).foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gSM) smStore 100) ((smNodes.take 0).foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gSM) smStore 300) := by
          change (smNodes.foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gSM) smStore) 500 = _
          rw [show smNodes = smNodes.take 0 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [100, 300], outs := [500] }] ++ smNodes.drop 1 by native_decide]
          apply foldl_faithful_middle_writer SyntheticReductionOutput.gSM smStore (smNodes.take 0) (smNodes.drop 1) { rank := 0, op := "OpName.FW_linear", ins := [100, 300], outs := [500] } 500 (fun t => fw_linear (t 100) (t 300))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_linear_out SyntheticReductionOutput.gSM t 0 100 300 500
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_linear (smStore 100) (smStore 300) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionOutput.gSM (smNodes.take 0) smStore 100 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionOutput.gSM (smNodes.take 0) smStore 300 (by native_decide) (by native_decide)]
    have hReductionPm0_0 : pmFinal 600 = fw_linear (pmStore 200) (pmStore 400) := by
      calc
        pmFinal 600 = fw_linear ((pmNodes.take 0).foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore 200) ((pmNodes.take 0).foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore 400) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore) 600 = _
          rw [show pmNodes = pmNodes.take 0 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [200, 400], outs := [600] }] ++ pmNodes.drop 1 by native_decide]
          apply foldl_faithful_middle_writer SyntheticReductionOutput.gPM pmStore (pmNodes.take 0) (pmNodes.drop 1) { rank := 0, op := "OpName.FW_linear", ins := [200, 400], outs := [600] } 600 (fun t => fw_linear (t 200) (t 400))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_linear_out SyntheticReductionOutput.gPM t 0 200 400 600
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_linear (pmStore 200) (pmStore 400) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionOutput.gPM (pmNodes.take 0) pmStore 200 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionOutput.gPM (pmNodes.take 0) pmStore 400 (by native_decide) (by native_decide)]
    have hReductionChunk0_0 : chunkPrim 3 0 (smStore 100) = pmStore 200 := by
      rw [hActivation0.full_value]
      have hcancel := TrainVerify.Denote.chunkPrim_allGatherPrimDimN_cancel_3d 3 0 1 6 4 (pmActivationTids0.map pmStore)
        (by simp [rankCount0, pmActivationTids0]) hActivation0.shard_shapes
        (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      simpa [rankCount0, pmActivationTids0] using hcancel
    have hReductionShape0_0 : (pmFinal 600).shape = [1, 6, 9] := by
      rw [hReductionPm0_0]
      have ha := hActivation0.shard_shapes (pmStore 200) (by simp [pmActivationTids0])
      have hw := hReductionWeight0.shard_shapes (pmStore 400) (by simp [pmWeightTids0])
      simp [fw_linear, ha, hw]
      rfl
    have hReductionPm0_1 : pmFinal 601 = fw_linear (pmStore 201) (pmStore 401) := by
      calc
        pmFinal 601 = fw_linear ((pmNodes.take 5).foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore 201) ((pmNodes.take 5).foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore 401) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore) 601 = _
          rw [show pmNodes = pmNodes.take 5 ++ [{ rank := 1, op := "OpName.FW_linear", ins := [201, 401], outs := [601] }] ++ pmNodes.drop 6 by native_decide]
          apply foldl_faithful_middle_writer SyntheticReductionOutput.gPM pmStore (pmNodes.take 5) (pmNodes.drop 6) { rank := 1, op := "OpName.FW_linear", ins := [201, 401], outs := [601] } 601 (fun t => fw_linear (t 201) (t 401))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_linear_out SyntheticReductionOutput.gPM t 1 201 401 601
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_linear (pmStore 201) (pmStore 401) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionOutput.gPM (pmNodes.take 5) pmStore 201 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionOutput.gPM (pmNodes.take 5) pmStore 401 (by native_decide) (by native_decide)]
    have hReductionChunk0_1 : chunkPrim 3 1 (smStore 100) = pmStore 201 := by
      rw [hActivation0.full_value]
      have hcancel := TrainVerify.Denote.chunkPrim_allGatherPrimDimN_cancel_3d 3 1 1 6 4 (pmActivationTids0.map pmStore)
        (by simp [rankCount0, pmActivationTids0]) hActivation0.shard_shapes
        (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      simpa [rankCount0, pmActivationTids0] using hcancel
    have hReductionShape0_1 : (pmFinal 601).shape = [1, 6, 9] := by
      rw [hReductionPm0_1]
      have ha := hActivation0.shard_shapes (pmStore 201) (by simp [pmActivationTids0])
      have hw := hReductionWeight0.shard_shapes (pmStore 401) (by simp [pmWeightTids0])
      simp [fw_linear, ha, hw]
      rfl
    have hReductionPm0_2 : pmFinal 602 = fw_linear (pmStore 202) (pmStore 402) := by
      calc
        pmFinal 602 = fw_linear ((pmNodes.take 7).foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore 202) ((pmNodes.take 7).foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore 402) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore) 602 = _
          rw [show pmNodes = pmNodes.take 7 ++ [{ rank := 2, op := "OpName.FW_linear", ins := [202, 402], outs := [602] }] ++ pmNodes.drop 8 by native_decide]
          apply foldl_faithful_middle_writer SyntheticReductionOutput.gPM pmStore (pmNodes.take 7) (pmNodes.drop 8) { rank := 2, op := "OpName.FW_linear", ins := [202, 402], outs := [602] } 602 (fun t => fw_linear (t 202) (t 402))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_linear_out SyntheticReductionOutput.gPM t 2 202 402 602
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_linear (pmStore 202) (pmStore 402) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionOutput.gPM (pmNodes.take 7) pmStore 202 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionOutput.gPM (pmNodes.take 7) pmStore 402 (by native_decide) (by native_decide)]
    have hReductionChunk0_2 : chunkPrim 3 2 (smStore 100) = pmStore 202 := by
      rw [hActivation0.full_value]
      have hcancel := TrainVerify.Denote.chunkPrim_allGatherPrimDimN_cancel_3d 3 2 1 6 4 (pmActivationTids0.map pmStore)
        (by simp [rankCount0, pmActivationTids0]) hActivation0.shard_shapes
        (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      simpa [rankCount0, pmActivationTids0] using hcancel
    have hReductionShape0_2 : (pmFinal 602).shape = [1, 6, 9] := by
      rw [hReductionPm0_2]
      have ha := hActivation0.shard_shapes (pmStore 202) (by simp [pmActivationTids0])
      have hw := hReductionWeight0.shard_shapes (pmStore 402) (by simp [pmWeightTids0])
      simp [fw_linear, ha, hw]
      rfl
    have hReductionWeightGather0 : smStore 300 = allGatherPrim rankCount0 0 (pmWeightTids0.map pmStore) := by
      change smStore 300 = allGatherPrim 3 0 ([400, 401, 402].map pmStore)
      rw [hReductionWeight0.full_value]
      have hhead : ((pmWeightTids0.map pmStore).head?.map (fun t => t.shape)).getD [] = [9, 4] := by
        simpa [pmWeightTids0] using hReductionWeight0.shard_shapes (pmStore 400) (by simp [pmWeightTids0])
      simpa [rankCount0, pmActivationTids0, pmWeightTids0] using
        (allGatherPrimDimN_1_eq_allGatherPrim_2d 3 ([400, 401, 402].map pmStore) 9 4 hhead (by native_decide) (by native_decide))
    have hReductionFullShape0 : (smFinal 500).shape = [1, 6, 9] := by
      rw [hReductionSm0]
      simp [fw_linear, hActivation0.full_shape, hReductionWeight0.full_shape]
      rfl
    have hReductionValue0 : smFinal 500 = allReducePrim (pmOutputTids0.map pmFinal).length 0 (pmOutputTids0.map pmFinal) := by
      rw [hReductionSm0, hReductionWeightGather0]
      have hComm := TrainVerify.Denote.fw_linear_allGather_eq_allReduce_fw_linear_chunk_3d 3 1 6 12 9 4 (smStore 100) (pmWeightTids0.map pmStore)
        hActivation0.full_shape (by native_decide) (by simp [rankCount0, pmActivationTids0, pmWeightTids0]) hReductionWeight0.shard_shapes
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      have hContribs : List.ofFn (fun r : Fin 3 => fw_linear (chunkPrim 3 r.val (smStore 100)) ((pmWeightTids0.map pmStore).get ⟨r.val, by simpa [pmWeightTids0] using r.isLt⟩)) = [fw_linear (chunkPrim 3 0 (smStore 100)) (pmStore 400), fw_linear (chunkPrim 3 1 (smStore 100)) (pmStore 401), fw_linear (chunkPrim 3 2 (smStore 100)) (pmStore 402)] := by rfl
      rw [hContribs] at hComm
      simp [rankCount0, pmActivationTids0, pmWeightTids0, pmOutputTids0] at hComm ⊢
      rw [hReductionChunk0_0, hReductionChunk0_1, hReductionChunk0_2] at hComm
      rw [hComm]
      rw [← hReductionPm0_0, ← hReductionPm0_1, ← hReductionPm0_2]
    have hReductionOut0 : fact_reduction_output_0.Holds smFinal pmFinal := by
      change ReductionRel (smFinal 500) (pmOutputTids0.map pmFinal) [1, 6, 9]
      refine { full_value := hReductionValue0, full_shape := hReductionFullShape0, contributions_nonempty := by simp [pmOutputTids0], contribution_shapes := ?_, reduced_shape := ?_ }
      · intro contribution hmem
        simp only [pmOutputTids0, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact hReductionShape0_0
        · exact hReductionShape0_1
        · exact hReductionShape0_2
      · rw [← hReductionValue0]
        exact hReductionFullShape0
    have hActivation1 : fact_activation_1.Holds smStore pmStore := hstate fact_activation_1 (by native_decide)
    change ShardedRel (smStore 101) ([210, 211, 212].map pmStore) 2 [1, 6, 12] [1, 6, 4] at hActivation1
    have hReductionWeight1 : fact_reduction_weight_1.Holds smStore pmStore := hstate fact_reduction_weight_1 (by native_decide)
    change ShardedRel (smStore 301) ([410, 411, 412].map pmStore) 1 [9, 12] [9, 4] at hReductionWeight1
    let pmActivationTids1 : List Tid := [210, 211, 212]
    let pmWeightTids1 : List Tid := [410, 411, 412]
    let pmOutputTids1 : List Tid := [610, 611, 612]
    let rankCount1 := pmActivationTids1.length
    have hReductionSm1 : smFinal 501 = fw_linear (smStore 101) (smStore 301) := by
      calc
        smFinal 501 = fw_linear ((smNodes.take 1).foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gSM) smStore 101) ((smNodes.take 1).foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gSM) smStore 301) := by
          change (smNodes.foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gSM) smStore) 501 = _
          rw [show smNodes = smNodes.take 1 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [101, 301], outs := [501] }] ++ smNodes.drop 2 by native_decide]
          apply foldl_faithful_middle_writer SyntheticReductionOutput.gSM smStore (smNodes.take 1) (smNodes.drop 2) { rank := 0, op := "OpName.FW_linear", ins := [101, 301], outs := [501] } 501 (fun t => fw_linear (t 101) (t 301))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_linear_out SyntheticReductionOutput.gSM t 0 101 301 501
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_linear (smStore 101) (smStore 301) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionOutput.gSM (smNodes.take 1) smStore 101 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionOutput.gSM (smNodes.take 1) smStore 301 (by native_decide) (by native_decide)]
    have hReductionPm1_0 : pmFinal 610 = fw_linear (pmStore 210) (pmStore 410) := by
      calc
        pmFinal 610 = fw_linear ((pmNodes.take 1).foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore 210) ((pmNodes.take 1).foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore 410) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore) 610 = _
          rw [show pmNodes = pmNodes.take 1 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [210, 410], outs := [610] }] ++ pmNodes.drop 2 by native_decide]
          apply foldl_faithful_middle_writer SyntheticReductionOutput.gPM pmStore (pmNodes.take 1) (pmNodes.drop 2) { rank := 0, op := "OpName.FW_linear", ins := [210, 410], outs := [610] } 610 (fun t => fw_linear (t 210) (t 410))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_linear_out SyntheticReductionOutput.gPM t 0 210 410 610
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_linear (pmStore 210) (pmStore 410) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionOutput.gPM (pmNodes.take 1) pmStore 210 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionOutput.gPM (pmNodes.take 1) pmStore 410 (by native_decide) (by native_decide)]
    have hReductionChunk1_0 : chunkPrim 3 0 (smStore 101) = pmStore 210 := by
      rw [hActivation1.full_value]
      have hcancel := TrainVerify.Denote.chunkPrim_allGatherPrimDimN_cancel_3d 3 0 1 6 4 (pmActivationTids1.map pmStore)
        (by simp [rankCount1, pmActivationTids1]) hActivation1.shard_shapes
        (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      simpa [rankCount1, pmActivationTids1] using hcancel
    have hReductionShape1_0 : (pmFinal 610).shape = [1, 6, 9] := by
      rw [hReductionPm1_0]
      have ha := hActivation1.shard_shapes (pmStore 210) (by simp [pmActivationTids1])
      have hw := hReductionWeight1.shard_shapes (pmStore 410) (by simp [pmWeightTids1])
      simp [fw_linear, ha, hw]
      rfl
    have hReductionPm1_1 : pmFinal 611 = fw_linear (pmStore 211) (pmStore 411) := by
      calc
        pmFinal 611 = fw_linear ((pmNodes.take 6).foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore 211) ((pmNodes.take 6).foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore 411) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore) 611 = _
          rw [show pmNodes = pmNodes.take 6 ++ [{ rank := 1, op := "OpName.FW_linear", ins := [211, 411], outs := [611] }] ++ pmNodes.drop 7 by native_decide]
          apply foldl_faithful_middle_writer SyntheticReductionOutput.gPM pmStore (pmNodes.take 6) (pmNodes.drop 7) { rank := 1, op := "OpName.FW_linear", ins := [211, 411], outs := [611] } 611 (fun t => fw_linear (t 211) (t 411))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_linear_out SyntheticReductionOutput.gPM t 1 211 411 611
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_linear (pmStore 211) (pmStore 411) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionOutput.gPM (pmNodes.take 6) pmStore 211 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionOutput.gPM (pmNodes.take 6) pmStore 411 (by native_decide) (by native_decide)]
    have hReductionChunk1_1 : chunkPrim 3 1 (smStore 101) = pmStore 211 := by
      rw [hActivation1.full_value]
      have hcancel := TrainVerify.Denote.chunkPrim_allGatherPrimDimN_cancel_3d 3 1 1 6 4 (pmActivationTids1.map pmStore)
        (by simp [rankCount1, pmActivationTids1]) hActivation1.shard_shapes
        (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      simpa [rankCount1, pmActivationTids1] using hcancel
    have hReductionShape1_1 : (pmFinal 611).shape = [1, 6, 9] := by
      rw [hReductionPm1_1]
      have ha := hActivation1.shard_shapes (pmStore 211) (by simp [pmActivationTids1])
      have hw := hReductionWeight1.shard_shapes (pmStore 411) (by simp [pmWeightTids1])
      simp [fw_linear, ha, hw]
      rfl
    have hReductionPm1_2 : pmFinal 612 = fw_linear (pmStore 212) (pmStore 412) := by
      calc
        pmFinal 612 = fw_linear ((pmNodes.take 8).foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore 212) ((pmNodes.take 8).foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore 412) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore) 612 = _
          rw [show pmNodes = pmNodes.take 8 ++ [{ rank := 2, op := "OpName.FW_linear", ins := [212, 412], outs := [612] }] ++ pmNodes.drop 9 by native_decide]
          apply foldl_faithful_middle_writer SyntheticReductionOutput.gPM pmStore (pmNodes.take 8) (pmNodes.drop 9) { rank := 2, op := "OpName.FW_linear", ins := [212, 412], outs := [612] } 612 (fun t => fw_linear (t 212) (t 412))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_linear_out SyntheticReductionOutput.gPM t 2 212 412 612
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_linear (pmStore 212) (pmStore 412) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionOutput.gPM (pmNodes.take 8) pmStore 212 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionOutput.gPM (pmNodes.take 8) pmStore 412 (by native_decide) (by native_decide)]
    have hReductionChunk1_2 : chunkPrim 3 2 (smStore 101) = pmStore 212 := by
      rw [hActivation1.full_value]
      have hcancel := TrainVerify.Denote.chunkPrim_allGatherPrimDimN_cancel_3d 3 2 1 6 4 (pmActivationTids1.map pmStore)
        (by simp [rankCount1, pmActivationTids1]) hActivation1.shard_shapes
        (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      simpa [rankCount1, pmActivationTids1] using hcancel
    have hReductionShape1_2 : (pmFinal 612).shape = [1, 6, 9] := by
      rw [hReductionPm1_2]
      have ha := hActivation1.shard_shapes (pmStore 212) (by simp [pmActivationTids1])
      have hw := hReductionWeight1.shard_shapes (pmStore 412) (by simp [pmWeightTids1])
      simp [fw_linear, ha, hw]
      rfl
    have hReductionWeightGather1 : smStore 301 = allGatherPrim rankCount1 0 (pmWeightTids1.map pmStore) := by
      change smStore 301 = allGatherPrim 3 0 ([410, 411, 412].map pmStore)
      rw [hReductionWeight1.full_value]
      have hhead : ((pmWeightTids1.map pmStore).head?.map (fun t => t.shape)).getD [] = [9, 4] := by
        simpa [pmWeightTids1] using hReductionWeight1.shard_shapes (pmStore 410) (by simp [pmWeightTids1])
      simpa [rankCount1, pmActivationTids1, pmWeightTids1] using
        (allGatherPrimDimN_1_eq_allGatherPrim_2d 3 ([410, 411, 412].map pmStore) 9 4 hhead (by native_decide) (by native_decide))
    have hReductionFullShape1 : (smFinal 501).shape = [1, 6, 9] := by
      rw [hReductionSm1]
      simp [fw_linear, hActivation1.full_shape, hReductionWeight1.full_shape]
      rfl
    have hReductionValue1 : smFinal 501 = allReducePrim (pmOutputTids1.map pmFinal).length 0 (pmOutputTids1.map pmFinal) := by
      rw [hReductionSm1, hReductionWeightGather1]
      have hComm := TrainVerify.Denote.fw_linear_allGather_eq_allReduce_fw_linear_chunk_3d 3 1 6 12 9 4 (smStore 101) (pmWeightTids1.map pmStore)
        hActivation1.full_shape (by native_decide) (by simp [rankCount1, pmActivationTids1, pmWeightTids1]) hReductionWeight1.shard_shapes
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      have hContribs : List.ofFn (fun r : Fin 3 => fw_linear (chunkPrim 3 r.val (smStore 101)) ((pmWeightTids1.map pmStore).get ⟨r.val, by simpa [pmWeightTids1] using r.isLt⟩)) = [fw_linear (chunkPrim 3 0 (smStore 101)) (pmStore 410), fw_linear (chunkPrim 3 1 (smStore 101)) (pmStore 411), fw_linear (chunkPrim 3 2 (smStore 101)) (pmStore 412)] := by rfl
      rw [hContribs] at hComm
      simp [rankCount1, pmActivationTids1, pmWeightTids1, pmOutputTids1] at hComm ⊢
      rw [hReductionChunk1_0, hReductionChunk1_1, hReductionChunk1_2] at hComm
      rw [hComm]
      rw [← hReductionPm1_0, ← hReductionPm1_1, ← hReductionPm1_2]
    have hReductionOut1 : fact_reduction_output_1.Holds smFinal pmFinal := by
      change ReductionRel (smFinal 501) (pmOutputTids1.map pmFinal) [1, 6, 9]
      refine { full_value := hReductionValue1, full_shape := hReductionFullShape1, contributions_nonempty := by simp [pmOutputTids1], contribution_shapes := ?_, reduced_shape := ?_ }
      · intro contribution hmem
        simp only [pmOutputTids1, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact hReductionShape1_0
        · exact hReductionShape1_1
        · exact hReductionShape1_2
      · rw [← hReductionValue1]
        exact hReductionFullShape1
    have hJoined : fact_joined.Holds smStore pmStore := hstate fact_joined (by native_decide)
    change smStore 700 = pmStore 701 ∧ (smStore 700).shape = [1, 6, 12] ∧ (pmStore 701).shape = [1, 6, 12] at hJoined
    have hOutputWeight : fact_output_weight.Holds smStore pmStore := hstate fact_output_weight (by native_decide)
    change ShardedRel (smStore 702) ([710, 711, 712].map pmStore) 0 [15, 12] [5, 12] at hOutputWeight
    have hOutputSm : smFinal 703 = fw_linear (smStore 700) (smStore 702) := by
      calc
        smFinal 703 = fw_linear ((smNodes.take 2).foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gSM) smStore 700) ((smNodes.take 2).foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gSM) smStore 702) := by
          change (smNodes.foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gSM) smStore) 703 = _
          rw [show smNodes = smNodes.take 2 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [700, 702], outs := [703] }] ++ smNodes.drop 3 by native_decide]
          apply foldl_faithful_middle_writer SyntheticReductionOutput.gSM smStore (smNodes.take 2) (smNodes.drop 3) { rank := 0, op := "OpName.FW_linear", ins := [700, 702], outs := [703] } 703 (fun t => fw_linear (t 700) (t 702))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_linear_out SyntheticReductionOutput.gSM t 0 700 702 703
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_linear (smStore 700) (smStore 702) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionOutput.gSM (smNodes.take 2) smStore 700 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionOutput.gSM (smNodes.take 2) smStore 702 (by native_decide) (by native_decide)]
    have hOutputPm0 : pmFinal 720 = fw_linear (pmStore 701) (pmStore 710) := by
      calc
        pmFinal 720 = fw_linear ((pmNodes.take 2).foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore 701) ((pmNodes.take 2).foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore 710) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore) 720 = _
          rw [show pmNodes = pmNodes.take 2 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [701, 710], outs := [720] }] ++ pmNodes.drop 3 by native_decide]
          apply foldl_faithful_middle_writer SyntheticReductionOutput.gPM pmStore (pmNodes.take 2) (pmNodes.drop 3) { rank := 0, op := "OpName.FW_linear", ins := [701, 710], outs := [720] } 720 (fun t => fw_linear (t 701) (t 710))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_linear_out SyntheticReductionOutput.gPM t 0 701 710 720
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_linear (pmStore 701) (pmStore 710) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionOutput.gPM (pmNodes.take 2) pmStore 701 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionOutput.gPM (pmNodes.take 2) pmStore 710 (by native_decide) (by native_decide)]
    have hOutputShape0 : (pmFinal 720).shape = [1, 6, 5] := by
      rw [hOutputPm0]
      exact fw_linear_3d_shape 1 6 12 5 _ _ hJoined.2.2 (hOutputWeight.shard_shapes _ (by simp))
    have hOutputPm1 : pmFinal 721 = fw_linear (pmStore 701) (pmStore 711) := by
      calc
        pmFinal 721 = fw_linear ((pmNodes.take 3).foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore 701) ((pmNodes.take 3).foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore 711) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore) 721 = _
          rw [show pmNodes = pmNodes.take 3 ++ [{ rank := 1, op := "OpName.FW_linear", ins := [701, 711], outs := [721] }] ++ pmNodes.drop 4 by native_decide]
          apply foldl_faithful_middle_writer SyntheticReductionOutput.gPM pmStore (pmNodes.take 3) (pmNodes.drop 4) { rank := 1, op := "OpName.FW_linear", ins := [701, 711], outs := [721] } 721 (fun t => fw_linear (t 701) (t 711))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_linear_out SyntheticReductionOutput.gPM t 1 701 711 721
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_linear (pmStore 701) (pmStore 711) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionOutput.gPM (pmNodes.take 3) pmStore 701 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionOutput.gPM (pmNodes.take 3) pmStore 711 (by native_decide) (by native_decide)]
    have hOutputShape1 : (pmFinal 721).shape = [1, 6, 5] := by
      rw [hOutputPm1]
      exact fw_linear_3d_shape 1 6 12 5 _ _ hJoined.2.2 (hOutputWeight.shard_shapes _ (by simp))
    have hOutputPm2 : pmFinal 722 = fw_linear (pmStore 701) (pmStore 712) := by
      calc
        pmFinal 722 = fw_linear ((pmNodes.take 4).foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore 701) ((pmNodes.take 4).foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore 712) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticReductionOutput.gPM) pmStore) 722 = _
          rw [show pmNodes = pmNodes.take 4 ++ [{ rank := 2, op := "OpName.FW_linear", ins := [701, 712], outs := [722] }] ++ pmNodes.drop 5 by native_decide]
          apply foldl_faithful_middle_writer SyntheticReductionOutput.gPM pmStore (pmNodes.take 4) (pmNodes.drop 5) { rank := 2, op := "OpName.FW_linear", ins := [701, 712], outs := [722] } 722 (fun t => fw_linear (t 701) (t 712))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_linear_out SyntheticReductionOutput.gPM t 2 701 712 722
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_linear (pmStore 701) (pmStore 712) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionOutput.gPM (pmNodes.take 4) pmStore 701 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionOutput.gPM (pmNodes.take 4) pmStore 712 (by native_decide) (by native_decide)]
    have hOutputShape2 : (pmFinal 722).shape = [1, 6, 5] := by
      rw [hOutputPm2]
      exact fw_linear_3d_shape 1 6 12 5 _ _ hJoined.2.2 (hOutputWeight.shard_shapes _ (by simp))
    have hOutputComm := (TrainVerify.Denote.fw_linear_3d_weight_allGatherPrimDimN_dim0_comm (K := ([710, 711, 712].map pmStore).length) (b := 1) (s := 6) (i := 12) (o := 5) (x := pmStore 701) (ws := [710, 711, 712].map pmStore) (by simp) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by simp) hJoined.2.2 (fun w hw => hOutputWeight.shard_shapes w hw))
    have hOutputValue : smFinal 703 = allGatherPrimDimN 2 ([720, 721, 722].map pmFinal).length 0 ([720, 721, 722].map pmFinal) := by
      rw [hOutputSm, hJoined.1, hOutputWeight.full_value, hOutputComm]
      simp only [List.map, List.length_cons, List.length_nil]
      rw [← hOutputPm0, ← hOutputPm1, ← hOutputPm2]
    have hOutputFullShape : (smFinal 703).shape = [1, 6, 15] := by
      rw [hOutputValue, allGatherPrimDimN_shape 2 ([720, 721, 722].map pmFinal).length ([720, 721, 722].map pmFinal) [1, 6, 5]]
      · simp only [List.map, List.length_cons, List.length_nil]
        native_decide
      · simp only [List.map, List.head?, Option.map, Option.getD]; exact hOutputShape0
    have hOutputOut : fact_final.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 703) ([720, 721, 722].map pmFinal) 2 [1, 6, 15] [1, 6, 5]
      refine { full_value := hOutputValue, full_shape := hOutputFullShape, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.map, List.length_cons, List.length_nil] <;> native_decide }
      intro shard hmem
      simp only [List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact hOutputShape0
      · exact hOutputShape1
      · exact hOutputShape2
    intro fact hfact
    have covered : fact ∈ [fact_reduction_output_0, fact_reduction_output_1, fact_final] ++ state_pre.facts := by
      exact (show state_post.facts ⊆ [fact_reduction_output_0, fact_reduction_output_1, fact_final] ++ state_pre.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl | rfl | rfl
      · exact hReductionOut0
      · exact hReductionOut1
      · exact hOutputOut
    · exact hframe fact old

#print axioms segment_atomic
end
end SyntheticReductionOutput
end TrainVerify.Denote
