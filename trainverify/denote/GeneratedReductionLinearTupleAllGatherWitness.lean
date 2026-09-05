import denote.RelationCompiler
import denote.KRankLinearReduction

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticReductionTuple
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := { numRanks := 1, nodes := [] }
def gPM : GraphDecl := { numRanks := 3, nodes := [] }
def activation_0 : RelationFact := .sharded 100 [200,201,202] 2 [1,6,12] [1,6,4]
def weight_0 : RelationFact := .sharded 300 [400,401,402] 1 [9,12] [9,4]
def activation_1 : RelationFact := .sharded 101 [210,211,212] 2 [1,6,12] [1,6,4]
def weight_1 : RelationFact := .sharded 301 [410,411,412] 1 [9,12] [9,4]
def gather_pre : RelationFact := .sharded 800 [810,811,812] 1 [2,15] [2,5]
def output_0 : RelationFact := .reduction 500 [600,601,602] [1,6,9]
def output_1 : RelationFact := .reduction 501 [610,611,612] [1,6,9]
def gather_post : RelationFact := .joined 800 899 [2,15]
def state_pre : RelationState where
  facts := [activation_0,weight_0,activation_1,weight_1,gather_pre]
  nonempty := by decide
def state_post : RelationState where
  facts := [output_0,output_1,gather_post]
  nonempty := by decide

set_option maxHeartbeats 500000 in
private def segment_atomic_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [100, 300], outs := [500] }, { rank := 0, op := "OpName.FW_linear", ins := [101, 301], outs := [501] }]
private def segment_atomic_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [200, 400], outs := [600] }, { rank := 0, op := "OpName.FW_linear", ins := [210, 410], outs := [610] }, { rank := 0, op := "OpName.AllGatherPrim", ins := [810, 811, 812], outs := [899], params := [1] }, { rank := 1, op := "OpName.FW_linear", ins := [211, 411], outs := [611] }, { rank := 1, op := "OpName.FW_linear", ins := [201, 401], outs := [601] }, { rank := 2, op := "OpName.FW_linear", ins := [212, 412], outs := [612] }, { rank := 2, op := "OpName.FW_linear", ins := [202, 402], outs := [602] }]

set_option maxHeartbeats 500000 in
private def segment_atomic : ClosedDepSegmentCertificate SyntheticReductionTuple.gSM SyntheticReductionTuple.gPM state_pre state_post where
  smNodes := segment_atomic_sm_nodes
  pmNodes := segment_atomic_pm_nodes
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := segment_atomic_sm_nodes
    let pmNodes : List NodeDecl := segment_atomic_pm_nodes
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gSM) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gPM) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hActivation0 : activation_0.Holds smStore pmStore := hstate activation_0 (by native_decide)
    change ShardedRel (smStore 100) ([200, 201, 202].map pmStore) 2 [1, 6, 12] [1, 6, 4] at hActivation0
    have hWeight0 : weight_0.Holds smStore pmStore := hstate weight_0 (by native_decide)
    change ShardedRel (smStore 300) ([400, 401, 402].map pmStore) 1 [9, 12] [9, 4] at hWeight0
    let pmActivationTids0 : List Tid := [200, 201, 202]
    let pmWeightTids0 : List Tid := [400, 401, 402]
    let pmOutputTids0 : List Tid := [600, 601, 602]
    let rankCount0 := pmActivationTids0.length
    have hSm0 : smFinal 500 = fw_linear (smStore 100) (smStore 300) := by
      calc
        smFinal 500 = fw_linear ((smNodes.take 0).foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gSM) smStore 100) ((smNodes.take 0).foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gSM) smStore 300) := by
          change (smNodes.foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gSM) smStore) 500 = _
          rw [show smNodes = smNodes.take 0 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [100, 300], outs := [500] }] ++ smNodes.drop 1 by native_decide]
          apply foldl_faithful_middle_writer SyntheticReductionTuple.gSM smStore (smNodes.take 0) (smNodes.drop 1) { rank := 0, op := "OpName.FW_linear", ins := [100, 300], outs := [500] } 500 (fun t => fw_linear (t 100) (t 300))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_linear_out SyntheticReductionTuple.gSM t 0 100 300 500
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_linear (smStore 100) (smStore 300) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionTuple.gSM (smNodes.take 0) smStore 100 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionTuple.gSM (smNodes.take 0) smStore 300 (by native_decide) (by native_decide)]
    have hPm0_0 : pmFinal 600 = fw_linear (pmStore 200) (pmStore 400) := by
      calc
        pmFinal 600 = fw_linear ((pmNodes.take 0).foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gPM) pmStore 200) ((pmNodes.take 0).foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gPM) pmStore 400) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gPM) pmStore) 600 = _
          rw [show pmNodes = pmNodes.take 0 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [200, 400], outs := [600] }] ++ pmNodes.drop 1 by native_decide]
          apply foldl_faithful_middle_writer SyntheticReductionTuple.gPM pmStore (pmNodes.take 0) (pmNodes.drop 1) { rank := 0, op := "OpName.FW_linear", ins := [200, 400], outs := [600] } 600 (fun t => fw_linear (t 200) (t 400))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_linear_out SyntheticReductionTuple.gPM t 0 200 400 600
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_linear (pmStore 200) (pmStore 400) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionTuple.gPM (pmNodes.take 0) pmStore 200 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionTuple.gPM (pmNodes.take 0) pmStore 400 (by native_decide) (by native_decide)]
    have hChunk0_0 : chunkPrim 3 0 (smStore 100) = pmStore 200 := by
      rw [hActivation0.full_value]
      have hcancel := TrainVerify.Denote.chunkPrim_allGatherPrimDimN_cancel_3d 3 0 1 6 4 (pmActivationTids0.map pmStore)
        (by simp [rankCount0, pmActivationTids0]) hActivation0.shard_shapes (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      simpa [rankCount0, pmActivationTids0] using hcancel
    have hShape0_0 : (pmFinal 600).shape = [1, 6, 9] := by
      rw [hPm0_0]
      have ha := hActivation0.shard_shapes (pmStore 200) (by simp [pmActivationTids0])
      have hw := hWeight0.shard_shapes (pmStore 400) (by simp [pmWeightTids0])
      simp [fw_linear, ha, hw]
      rfl
    have hPm0_1 : pmFinal 601 = fw_linear (pmStore 201) (pmStore 401) := by
      calc
        pmFinal 601 = fw_linear ((pmNodes.take 4).foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gPM) pmStore 201) ((pmNodes.take 4).foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gPM) pmStore 401) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gPM) pmStore) 601 = _
          rw [show pmNodes = pmNodes.take 4 ++ [{ rank := 1, op := "OpName.FW_linear", ins := [201, 401], outs := [601] }] ++ pmNodes.drop 5 by native_decide]
          apply foldl_faithful_middle_writer SyntheticReductionTuple.gPM pmStore (pmNodes.take 4) (pmNodes.drop 5) { rank := 1, op := "OpName.FW_linear", ins := [201, 401], outs := [601] } 601 (fun t => fw_linear (t 201) (t 401))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_linear_out SyntheticReductionTuple.gPM t 1 201 401 601
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_linear (pmStore 201) (pmStore 401) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionTuple.gPM (pmNodes.take 4) pmStore 201 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionTuple.gPM (pmNodes.take 4) pmStore 401 (by native_decide) (by native_decide)]
    have hChunk0_1 : chunkPrim 3 1 (smStore 100) = pmStore 201 := by
      rw [hActivation0.full_value]
      have hcancel := TrainVerify.Denote.chunkPrim_allGatherPrimDimN_cancel_3d 3 1 1 6 4 (pmActivationTids0.map pmStore)
        (by simp [rankCount0, pmActivationTids0]) hActivation0.shard_shapes (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      simpa [rankCount0, pmActivationTids0] using hcancel
    have hShape0_1 : (pmFinal 601).shape = [1, 6, 9] := by
      rw [hPm0_1]
      have ha := hActivation0.shard_shapes (pmStore 201) (by simp [pmActivationTids0])
      have hw := hWeight0.shard_shapes (pmStore 401) (by simp [pmWeightTids0])
      simp [fw_linear, ha, hw]
      rfl
    have hPm0_2 : pmFinal 602 = fw_linear (pmStore 202) (pmStore 402) := by
      calc
        pmFinal 602 = fw_linear ((pmNodes.take 6).foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gPM) pmStore 202) ((pmNodes.take 6).foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gPM) pmStore 402) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gPM) pmStore) 602 = _
          rw [show pmNodes = pmNodes.take 6 ++ [{ rank := 2, op := "OpName.FW_linear", ins := [202, 402], outs := [602] }] ++ pmNodes.drop 7 by native_decide]
          apply foldl_faithful_middle_writer SyntheticReductionTuple.gPM pmStore (pmNodes.take 6) (pmNodes.drop 7) { rank := 2, op := "OpName.FW_linear", ins := [202, 402], outs := [602] } 602 (fun t => fw_linear (t 202) (t 402))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_linear_out SyntheticReductionTuple.gPM t 2 202 402 602
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_linear (pmStore 202) (pmStore 402) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionTuple.gPM (pmNodes.take 6) pmStore 202 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionTuple.gPM (pmNodes.take 6) pmStore 402 (by native_decide) (by native_decide)]
    have hChunk0_2 : chunkPrim 3 2 (smStore 100) = pmStore 202 := by
      rw [hActivation0.full_value]
      have hcancel := TrainVerify.Denote.chunkPrim_allGatherPrimDimN_cancel_3d 3 2 1 6 4 (pmActivationTids0.map pmStore)
        (by simp [rankCount0, pmActivationTids0]) hActivation0.shard_shapes (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      simpa [rankCount0, pmActivationTids0] using hcancel
    have hShape0_2 : (pmFinal 602).shape = [1, 6, 9] := by
      rw [hPm0_2]
      have ha := hActivation0.shard_shapes (pmStore 202) (by simp [pmActivationTids0])
      have hw := hWeight0.shard_shapes (pmStore 402) (by simp [pmWeightTids0])
      simp [fw_linear, ha, hw]
      rfl
    have hWeightGather0 : smStore 300 = allGatherPrim rankCount0 0 (pmWeightTids0.map pmStore) := by
      change smStore 300 = allGatherPrim 3 0 ([400, 401, 402].map pmStore)
      rw [hWeight0.full_value]
      have hhead : ((pmWeightTids0.map pmStore).head?.map (fun t => t.shape)).getD [] = [9, 4] := by
        simpa [pmWeightTids0] using hWeight0.shard_shapes (pmStore 400) (by simp [pmWeightTids0])
      simpa [rankCount0, pmActivationTids0, pmWeightTids0] using
        (allGatherPrimDimN_1_eq_allGatherPrim_2d 3 ([400, 401, 402].map pmStore) 9 4 hhead (by native_decide) (by native_decide))
    have hFullShape0 : (smFinal 500).shape = [1, 6, 9] := by
      rw [hSm0]
      simp [fw_linear, hActivation0.full_shape, hWeight0.full_shape]
      rfl
    have hValue0 : smFinal 500 = allReducePrim (pmOutputTids0.map pmFinal).length 0 (pmOutputTids0.map pmFinal) := by
      rw [hSm0, hWeightGather0]
      have hComm := TrainVerify.Denote.fw_linear_allGather_eq_allReduce_fw_linear_chunk_3d 3 1 6 12 9 4 (smStore 100) (pmWeightTids0.map pmStore)
        hActivation0.full_shape (by native_decide) (by simp [rankCount0, pmActivationTids0, pmWeightTids0]) hWeight0.shard_shapes
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      have hContribs : List.ofFn (fun r : Fin 3 => fw_linear (chunkPrim 3 r.val (smStore 100)) ((pmWeightTids0.map pmStore).get ⟨r.val, by simpa [pmWeightTids0] using r.isLt⟩)) = [fw_linear (chunkPrim 3 0 (smStore 100)) (pmStore 400), fw_linear (chunkPrim 3 1 (smStore 100)) (pmStore 401), fw_linear (chunkPrim 3 2 (smStore 100)) (pmStore 402)] := by rfl
      rw [hContribs] at hComm
      simp [rankCount0, pmActivationTids0, pmWeightTids0, pmOutputTids0] at hComm ⊢
      rw [hChunk0_0, hChunk0_1, hChunk0_2] at hComm
      rw [hComm]
      rw [← hPm0_0, ← hPm0_1, ← hPm0_2]
    have hOut0 : output_0.Holds smFinal pmFinal := by
      change ReductionRel (smFinal 500) (pmOutputTids0.map pmFinal) [1, 6, 9]
      refine { full_value := hValue0, full_shape := hFullShape0, contributions_nonempty := by simp [pmOutputTids0], contribution_shapes := ?_, reduced_shape := ?_ }
      · intro contribution hmem
        simp only [pmOutputTids0, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact hShape0_0
        · exact hShape0_1
        · exact hShape0_2
      · rw [← hValue0]
        exact hFullShape0
    have hActivation1 : activation_1.Holds smStore pmStore := hstate activation_1 (by native_decide)
    change ShardedRel (smStore 101) ([210, 211, 212].map pmStore) 2 [1, 6, 12] [1, 6, 4] at hActivation1
    have hWeight1 : weight_1.Holds smStore pmStore := hstate weight_1 (by native_decide)
    change ShardedRel (smStore 301) ([410, 411, 412].map pmStore) 1 [9, 12] [9, 4] at hWeight1
    let pmActivationTids1 : List Tid := [210, 211, 212]
    let pmWeightTids1 : List Tid := [410, 411, 412]
    let pmOutputTids1 : List Tid := [610, 611, 612]
    let rankCount1 := pmActivationTids1.length
    have hSm1 : smFinal 501 = fw_linear (smStore 101) (smStore 301) := by
      calc
        smFinal 501 = fw_linear ((smNodes.take 1).foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gSM) smStore 101) ((smNodes.take 1).foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gSM) smStore 301) := by
          change (smNodes.foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gSM) smStore) 501 = _
          rw [show smNodes = smNodes.take 1 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [101, 301], outs := [501] }] ++ smNodes.drop 2 by native_decide]
          apply foldl_faithful_middle_writer SyntheticReductionTuple.gSM smStore (smNodes.take 1) (smNodes.drop 2) { rank := 0, op := "OpName.FW_linear", ins := [101, 301], outs := [501] } 501 (fun t => fw_linear (t 101) (t 301))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_linear_out SyntheticReductionTuple.gSM t 0 101 301 501
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_linear (smStore 101) (smStore 301) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionTuple.gSM (smNodes.take 1) smStore 101 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionTuple.gSM (smNodes.take 1) smStore 301 (by native_decide) (by native_decide)]
    have hPm1_0 : pmFinal 610 = fw_linear (pmStore 210) (pmStore 410) := by
      calc
        pmFinal 610 = fw_linear ((pmNodes.take 1).foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gPM) pmStore 210) ((pmNodes.take 1).foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gPM) pmStore 410) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gPM) pmStore) 610 = _
          rw [show pmNodes = pmNodes.take 1 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [210, 410], outs := [610] }] ++ pmNodes.drop 2 by native_decide]
          apply foldl_faithful_middle_writer SyntheticReductionTuple.gPM pmStore (pmNodes.take 1) (pmNodes.drop 2) { rank := 0, op := "OpName.FW_linear", ins := [210, 410], outs := [610] } 610 (fun t => fw_linear (t 210) (t 410))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_linear_out SyntheticReductionTuple.gPM t 0 210 410 610
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_linear (pmStore 210) (pmStore 410) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionTuple.gPM (pmNodes.take 1) pmStore 210 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionTuple.gPM (pmNodes.take 1) pmStore 410 (by native_decide) (by native_decide)]
    have hChunk1_0 : chunkPrim 3 0 (smStore 101) = pmStore 210 := by
      rw [hActivation1.full_value]
      have hcancel := TrainVerify.Denote.chunkPrim_allGatherPrimDimN_cancel_3d 3 0 1 6 4 (pmActivationTids1.map pmStore)
        (by simp [rankCount1, pmActivationTids1]) hActivation1.shard_shapes (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      simpa [rankCount1, pmActivationTids1] using hcancel
    have hShape1_0 : (pmFinal 610).shape = [1, 6, 9] := by
      rw [hPm1_0]
      have ha := hActivation1.shard_shapes (pmStore 210) (by simp [pmActivationTids1])
      have hw := hWeight1.shard_shapes (pmStore 410) (by simp [pmWeightTids1])
      simp [fw_linear, ha, hw]
      rfl
    have hPm1_1 : pmFinal 611 = fw_linear (pmStore 211) (pmStore 411) := by
      calc
        pmFinal 611 = fw_linear ((pmNodes.take 3).foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gPM) pmStore 211) ((pmNodes.take 3).foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gPM) pmStore 411) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gPM) pmStore) 611 = _
          rw [show pmNodes = pmNodes.take 3 ++ [{ rank := 1, op := "OpName.FW_linear", ins := [211, 411], outs := [611] }] ++ pmNodes.drop 4 by native_decide]
          apply foldl_faithful_middle_writer SyntheticReductionTuple.gPM pmStore (pmNodes.take 3) (pmNodes.drop 4) { rank := 1, op := "OpName.FW_linear", ins := [211, 411], outs := [611] } 611 (fun t => fw_linear (t 211) (t 411))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_linear_out SyntheticReductionTuple.gPM t 1 211 411 611
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_linear (pmStore 211) (pmStore 411) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionTuple.gPM (pmNodes.take 3) pmStore 211 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionTuple.gPM (pmNodes.take 3) pmStore 411 (by native_decide) (by native_decide)]
    have hChunk1_1 : chunkPrim 3 1 (smStore 101) = pmStore 211 := by
      rw [hActivation1.full_value]
      have hcancel := TrainVerify.Denote.chunkPrim_allGatherPrimDimN_cancel_3d 3 1 1 6 4 (pmActivationTids1.map pmStore)
        (by simp [rankCount1, pmActivationTids1]) hActivation1.shard_shapes (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      simpa [rankCount1, pmActivationTids1] using hcancel
    have hShape1_1 : (pmFinal 611).shape = [1, 6, 9] := by
      rw [hPm1_1]
      have ha := hActivation1.shard_shapes (pmStore 211) (by simp [pmActivationTids1])
      have hw := hWeight1.shard_shapes (pmStore 411) (by simp [pmWeightTids1])
      simp [fw_linear, ha, hw]
      rfl
    have hPm1_2 : pmFinal 612 = fw_linear (pmStore 212) (pmStore 412) := by
      calc
        pmFinal 612 = fw_linear ((pmNodes.take 5).foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gPM) pmStore 212) ((pmNodes.take 5).foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gPM) pmStore 412) := by
          change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gPM) pmStore) 612 = _
          rw [show pmNodes = pmNodes.take 5 ++ [{ rank := 2, op := "OpName.FW_linear", ins := [212, 412], outs := [612] }] ++ pmNodes.drop 6 by native_decide]
          apply foldl_faithful_middle_writer SyntheticReductionTuple.gPM pmStore (pmNodes.take 5) (pmNodes.drop 6) { rank := 2, op := "OpName.FW_linear", ins := [212, 412], outs := [612] } 612 (fun t => fw_linear (t 212) (t 412))
          · intro t
            rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by decide) (hunshuffle := by decide) (hattn := by decide)]
            unfold applyNodeDistributed
            rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), applyNodeRingAttn_eq_applyNode_of_not_ring]
            · exact applyNode_fw_linear_out SyntheticReductionTuple.gPM t 2 212 412 612
            · decide
            · decide
          · native_decide
          · native_decide
        _ = fw_linear (pmStore 212) (pmStore 412) := by
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionTuple.gPM (pmNodes.take 5) pmStore 212 (by native_decide) (by native_decide)]
          rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionTuple.gPM (pmNodes.take 5) pmStore 412 (by native_decide) (by native_decide)]
    have hChunk1_2 : chunkPrim 3 2 (smStore 101) = pmStore 212 := by
      rw [hActivation1.full_value]
      have hcancel := TrainVerify.Denote.chunkPrim_allGatherPrimDimN_cancel_3d 3 2 1 6 4 (pmActivationTids1.map pmStore)
        (by simp [rankCount1, pmActivationTids1]) hActivation1.shard_shapes (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      simpa [rankCount1, pmActivationTids1] using hcancel
    have hShape1_2 : (pmFinal 612).shape = [1, 6, 9] := by
      rw [hPm1_2]
      have ha := hActivation1.shard_shapes (pmStore 212) (by simp [pmActivationTids1])
      have hw := hWeight1.shard_shapes (pmStore 412) (by simp [pmWeightTids1])
      simp [fw_linear, ha, hw]
      rfl
    have hWeightGather1 : smStore 301 = allGatherPrim rankCount1 0 (pmWeightTids1.map pmStore) := by
      change smStore 301 = allGatherPrim 3 0 ([410, 411, 412].map pmStore)
      rw [hWeight1.full_value]
      have hhead : ((pmWeightTids1.map pmStore).head?.map (fun t => t.shape)).getD [] = [9, 4] := by
        simpa [pmWeightTids1] using hWeight1.shard_shapes (pmStore 410) (by simp [pmWeightTids1])
      simpa [rankCount1, pmActivationTids1, pmWeightTids1] using
        (allGatherPrimDimN_1_eq_allGatherPrim_2d 3 ([410, 411, 412].map pmStore) 9 4 hhead (by native_decide) (by native_decide))
    have hFullShape1 : (smFinal 501).shape = [1, 6, 9] := by
      rw [hSm1]
      simp [fw_linear, hActivation1.full_shape, hWeight1.full_shape]
      rfl
    have hValue1 : smFinal 501 = allReducePrim (pmOutputTids1.map pmFinal).length 0 (pmOutputTids1.map pmFinal) := by
      rw [hSm1, hWeightGather1]
      have hComm := TrainVerify.Denote.fw_linear_allGather_eq_allReduce_fw_linear_chunk_3d 3 1 6 12 9 4 (smStore 101) (pmWeightTids1.map pmStore)
        hActivation1.full_shape (by native_decide) (by simp [rankCount1, pmActivationTids1, pmWeightTids1]) hWeight1.shard_shapes
        (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      have hContribs : List.ofFn (fun r : Fin 3 => fw_linear (chunkPrim 3 r.val (smStore 101)) ((pmWeightTids1.map pmStore).get ⟨r.val, by simpa [pmWeightTids1] using r.isLt⟩)) = [fw_linear (chunkPrim 3 0 (smStore 101)) (pmStore 410), fw_linear (chunkPrim 3 1 (smStore 101)) (pmStore 411), fw_linear (chunkPrim 3 2 (smStore 101)) (pmStore 412)] := by rfl
      rw [hContribs] at hComm
      simp [rankCount1, pmActivationTids1, pmWeightTids1, pmOutputTids1] at hComm ⊢
      rw [hChunk1_0, hChunk1_1, hChunk1_2] at hComm
      rw [hComm]
      rw [← hPm1_0, ← hPm1_1, ← hPm1_2]
    have hOut1 : output_1.Holds smFinal pmFinal := by
      change ReductionRel (smFinal 501) (pmOutputTids1.map pmFinal) [1, 6, 9]
      refine { full_value := hValue1, full_shape := hFullShape1, contributions_nonempty := by simp [pmOutputTids1], contribution_shapes := ?_, reduced_shape := ?_ }
      · intro contribution hmem
        simp only [pmOutputTids1, List.map, List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact hShape1_0
        · exact hShape1_1
        · exact hShape1_2
      · rw [← hValue1]
        exact hFullShape1
    let gatherInputTids : List Tid := [810, 811, 812]
    let rankCount := gatherInputTids.length
    have hRankCount : rankCount = 3 := by native_decide
    have hRankGraph : rankCount = SyntheticReductionTuple.gPM.numRanks := by rfl
    have hGatherBefore : gatherInputTids.map (((pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gPM) pmStore) = gatherInputTids.map pmStore := by
      apply List.map_congr_left
      intro tid htid
      simp only [gatherInputTids, List.mem_cons, List.not_mem_nil, or_false] at htid
      rcases htid with h0 | h1 | h2
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionTuple.gPM (pmNodes.take 2) pmStore 810 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionTuple.gPM (pmNodes.take 2) pmStore 811 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionTuple.gPM (pmNodes.take 2) pmStore 812 (by native_decide) (by native_decide)
    have hGatherFinal : gatherInputTids.map pmFinal = gatherInputTids.map pmStore := by
      apply List.map_congr_left
      intro tid htid
      simp only [gatherInputTids, List.mem_cons, List.not_mem_nil, or_false] at htid
      rcases htid with h0 | h1 | h2
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionTuple.gPM pmNodes pmStore 810 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionTuple.gPM pmNodes pmStore 811 (by native_decide) (by native_decide)
      · subst tid
        exact foldl_applyNodeDistributedFaithful_at_not_written SyntheticReductionTuple.gPM pmNodes pmStore 812 (by native_decide) (by native_decide)
    have hGatherWriter : pmFinal 899 = allGatherPrimDimN 1 rankCount 0 (gatherInputTids.map pmFinal) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticReductionTuple.gPM) pmStore) 899 = _
      rw [show pmNodes = (pmNodes.take 2) ++ [{ rank := 0, op := "OpName.AllGatherPrim", ins := [810, 811, 812], outs := [899], params := [1] }] ++ (pmNodes.drop 3) by native_decide]
      rw [foldl_faithful_middle_writer SyntheticReductionTuple.gPM pmStore (pmNodes.take 2) (pmNodes.drop 3) { rank := 0, op := "OpName.AllGatherPrim", ins := [810, 811, 812], outs := [899], params := [1] } 899 (fun t => allGatherPrimDimN 1 rankCount 0 (gatherInputTids.map t))]
      · rw [hGatherBefore, hGatherFinal]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankGraph]
        simpa [gatherInputTids] using applyNode_allGatherPrimDimN_out SyntheticReductionTuple.gPM t 0 gatherInputTids 899 1
      · native_decide
      · native_decide
    have hinGather : gather_pre.Holds smFinal pmFinal := hframe gather_pre (by native_decide)
    change ShardedRel (smFinal 800) (gatherInputTids.map pmFinal) 1 [2, 15] [2, 5] at hinGather
    have hJoined : smFinal 800 = pmFinal 899 := (TrainVerify.Denote.RelationCompiler.ShardedRel.to_joined_allGather hinGather).trans hGatherWriter.symm
    have houtGather : gather_post.Holds smFinal pmFinal := by
      change smFinal 800 = pmFinal 899 ∧ (smFinal 800).shape = [2, 15] ∧ (pmFinal 899).shape = [2, 15]
      refine ⟨hJoined, hinGather.full_shape, ?_⟩
      rw [← hJoined]
      exact hinGather.full_shape
    intro fact hfact
    have covered : fact ∈ [output_0, output_1, gather_post] ++ state_pre.facts := by
      exact (show state_post.facts ⊆ [output_0, output_1, gather_post] ++ state_pre.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with new | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at new
      rcases new with h0 | h1 | h2
      · subst fact
        exact hOut0
      · subst fact
        exact hOut1
      · subst fact
        exact houtGather
    · exact hframe fact old

#print axioms segment_atomic
end
end SyntheticReductionTuple
end TrainVerify.Denote
