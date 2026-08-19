import denote.RelationCompiler
import denote.KRankLayernormGather
import denote.KRankAllToAll

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticMixedLayernormAllToAll
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := { numRanks := 1, nodes := [] }
def gPM : GraphDecl := { numRanks := 4, nodes := [] }
def fact_input : RelationFact :=
  .sharded 100 [200, 201, 202, 203] 1 [4, 12, 8] [4, 3, 8]
def fact_alltoall_input : RelationFact :=
  .sharded 120 [220, 221, 222, 223] 1 [4, 12, 8] [4, 3, 8]
def fact_layer : RelationFact :=
  .sharded 110 [300, 301, 302, 303] 1 [4, 12, 8] [4, 3, 8]
def fact_output : RelationFact :=
  .sharded 120 [400, 401, 402, 403] 2 [4, 12, 8] [4, 12, 2]
def gamma_eq : RelationFact := .tensorEq .pm 91 .sm 91
def gamma_shape : RelationFact := .tensorShape .pm 91 [8]
def beta_eq : RelationFact := .tensorEq .sm 92 .pm 92
def beta_shape : RelationFact := .tensorShape .pm 92 [8]
def state_pre : RelationState where
  facts := [fact_input, fact_alltoall_input, gamma_eq, gamma_shape, beta_eq, beta_shape]
  nonempty := by decide
def state_post : RelationState where
  facts := [fact_layer, fact_output]
  nonempty := by decide

private def segment_000092_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_layernorm", ins := [100, 91, 92], outs := [110] }]
private def segment_000092_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_layernorm", ins := [200, 91, 92], outs := [300] }, { rank := 1, op := "OpName.FW_layernorm", ins := [201, 91, 92], outs := [301] }, { rank := 2, op := "OpName.FW_layernorm", ins := [202, 91, 92], outs := [302] }, { rank := 0, op := "OpName.AllToAllPrim", ins := [220, 221, 222, 223], outs := [400], params := [1, 2] }, { rank := 1, op := "OpName.AllToAllPrim", ins := [220, 221, 222, 223], outs := [401], params := [1, 2] }, { rank := 2, op := "OpName.AllToAllPrim", ins := [220, 221, 222, 223], outs := [402], params := [1, 2] }, { rank := 3, op := "OpName.FW_layernorm", ins := [203, 91, 92], outs := [303] }, { rank := 3, op := "OpName.AllToAllPrim", ins := [220, 221, 222, 223], outs := [403], params := [1, 2] }]

private def segment_000092 :
    ClosedDepSegmentCertificate SyntheticMixedLayernormAllToAll.gSM SyntheticMixedLayernormAllToAll.gPM state_pre state_post where
  smNodes := segment_000092_sm_nodes
  pmNodes := segment_000092_pm_nodes
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := segment_000092_sm_nodes
    let pmNodes : List NodeDecl := segment_000092_pm_nodes
    let inputTids : List Tid := [220, 221, 222, 223]
    let outputTids : List Tid := [400, 401, 402, 403]
    let rankCount := outputTids.length
    have hRankCount : rankCount = SyntheticMixedLayernormAllToAll.gPM.numRanks := by native_decide
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gSM) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hLayerIn : fact_input.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 100) [pmStore 200, pmStore 201, pmStore 202, pmStore 203] 1 [4, 12, 8] [4, 3, 8] at hLayerIn
    have hAllToAllIn : fact_alltoall_input.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 120) [pmStore 220, pmStore 221, pmStore 222, pmStore 223] 1 [4, 12, 8] [4, 3, 8] at hAllToAllIn
    have hAllToAllInFinal : fact_alltoall_input.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 120) [pmFinal 220, pmFinal 221, pmFinal 222, pmFinal 223] 1 [4, 12, 8] [4, 3, 8] at hAllToAllInFinal
    have hExternalEqRaw0 : gamma_eq.Holds smStore pmStore := hstate _ (by native_decide)
    have hExternalEq0 : smStore 91 = pmStore 91 := by
      change pmStore 91 = smStore 91 at hExternalEqRaw0
      exact hExternalEqRaw0.symm
    have hExternalShape0 : gamma_shape.Holds smStore pmStore := hstate _ (by native_decide)
    change (pmStore 91).shape = [8] at hExternalShape0
    have hExternalEqRaw1 : beta_eq.Holds smStore pmStore := hstate _ (by native_decide)
    have hExternalEq1 : smStore 92 = pmStore 92 := by
      change smStore 92 = pmStore 92 at hExternalEqRaw1
      exact hExternalEqRaw1
    have hExternalShape1 : beta_shape.Holds smStore pmStore := hstate _ (by native_decide)
    change (pmStore 92).shape = [8] at hExternalShape1
    have hLayerSm : smFinal 110 = fw_layernorm (smStore 100) (smStore 91) (smStore 92) := by
      change (smNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gSM) smStore) 110 = _
      rw [show smNodes = smNodes.take 0 ++ [{ rank := 0, op := "OpName.FW_layernorm", ins := [100, 91, 92], outs := [110] }] ++ smNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticMixedLayernormAllToAll.gSM smStore (smNodes.take 0) (smNodes.drop 1) { rank := 0, op := "OpName.FW_layernorm", ins := [100, 91, 92], outs := [110] } 110 (fun t => fw_layernorm (t 100) (t 91) (t 92)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_layernorm_out SyntheticMixedLayernormAllToAll.gSM t 0 100 91 92 110 []
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gSM (smNodes.take 0) smStore 100 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gSM (smNodes.take 0) smStore 91 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gSM (smNodes.take 0) smStore 92 (by native_decide) (by native_decide)]
    have hLayerPm0 : pmFinal 300 = fw_layernorm (pmStore 200) (pmStore 91) (pmStore 92) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 300 = _
      rw [show pmNodes = pmNodes.take 0 ++ [{ rank := 0, op := "OpName.FW_layernorm", ins := [200, 91, 92], outs := [300] }] ++ pmNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticMixedLayernormAllToAll.gPM pmStore (pmNodes.take 0) (pmNodes.drop 1) { rank := 0, op := "OpName.FW_layernorm", ins := [200, 91, 92], outs := [300] } 300 (fun t => fw_layernorm (t 200) (t 91) (t 92)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_layernorm_out SyntheticMixedLayernormAllToAll.gPM t 0 200 91 92 300 []
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.take 0) pmStore 200 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.take 0) pmStore 91 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.take 0) pmStore 92 (by native_decide) (by native_decide)]
    have hLayerPm1 : pmFinal 301 = fw_layernorm (pmStore 201) (pmStore 91) (pmStore 92) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 301 = _
      rw [show pmNodes = pmNodes.take 1 ++ [{ rank := 1, op := "OpName.FW_layernorm", ins := [201, 91, 92], outs := [301] }] ++ pmNodes.drop 2 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticMixedLayernormAllToAll.gPM pmStore (pmNodes.take 1) (pmNodes.drop 2) { rank := 1, op := "OpName.FW_layernorm", ins := [201, 91, 92], outs := [301] } 301 (fun t => fw_layernorm (t 201) (t 91) (t 92)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_layernorm_out SyntheticMixedLayernormAllToAll.gPM t 1 201 91 92 301 []
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.take 1) pmStore 201 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.take 1) pmStore 91 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.take 1) pmStore 92 (by native_decide) (by native_decide)]
    have hLayerPm2 : pmFinal 302 = fw_layernorm (pmStore 202) (pmStore 91) (pmStore 92) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 302 = _
      rw [show pmNodes = pmNodes.take 2 ++ [{ rank := 2, op := "OpName.FW_layernorm", ins := [202, 91, 92], outs := [302] }] ++ pmNodes.drop 3 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticMixedLayernormAllToAll.gPM pmStore (pmNodes.take 2) (pmNodes.drop 3) { rank := 2, op := "OpName.FW_layernorm", ins := [202, 91, 92], outs := [302] } 302 (fun t => fw_layernorm (t 202) (t 91) (t 92)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_layernorm_out SyntheticMixedLayernormAllToAll.gPM t 2 202 91 92 302 []
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.take 2) pmStore 202 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.take 2) pmStore 91 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.take 2) pmStore 92 (by native_decide) (by native_decide)]
    have hLayerPm3 : pmFinal 303 = fw_layernorm (pmStore 203) (pmStore 91) (pmStore 92) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 303 = _
      rw [show pmNodes = pmNodes.take 6 ++ [{ rank := 3, op := "OpName.FW_layernorm", ins := [203, 91, 92], outs := [303] }] ++ pmNodes.drop 7 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticMixedLayernormAllToAll.gPM pmStore (pmNodes.take 6) (pmNodes.drop 7) { rank := 3, op := "OpName.FW_layernorm", ins := [203, 91, 92], outs := [303] } 303 (fun t => fw_layernorm (t 203) (t 91) (t 92)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_layernorm_out SyntheticMixedLayernormAllToAll.gPM t 3 203 91 92 303 []
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.take 6) pmStore 203 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.take 6) pmStore 91 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.take 6) pmStore 92 (by native_decide) (by native_decide)]
    have hLayerComm := (TrainVerify.Denote.fw_layernorm_distribute_allGatherPrimDimN_dim1_K_3d (K := [pmStore 200, pmStore 201, pmStore 202, pmStore 203].length) (b := 4) (s := 3) (d := 8) (xs := [pmStore 200, pmStore 201, pmStore 202, pmStore 203]) (gamma := pmStore 91) (beta := pmStore 92) (by simp) (by omega) (by omega) (by omega) rfl (fun x hx => hLayerIn.shard_shapes x hx) hExternalShape0 hExternalShape1)
    have hLayerValue : smFinal 110 = allGatherPrimDimN 1 [pmFinal 300, pmFinal 301, pmFinal 302, pmFinal 303].length 0 [pmFinal 300, pmFinal 301, pmFinal 302, pmFinal 303] := by
      rw [hLayerSm, hExternalEq0, hExternalEq1, hLayerIn.full_value, hLayerComm]
      simp only [List.map, List.length_cons, List.length_nil]
      rw [← hLayerPm0, ← hLayerPm1, ← hLayerPm2, ← hLayerPm3]
    have hLayerShape0 : (pmFinal 300).shape = [4, 3, 8] := by
      rw [hLayerPm0]
      unfold fw_layernorm
      rw [hLayerIn.shard_shapes (pmStore 200) (by simp)]
      rfl
    have hLayerShape1 : (pmFinal 301).shape = [4, 3, 8] := by
      rw [hLayerPm1]
      unfold fw_layernorm
      rw [hLayerIn.shard_shapes (pmStore 201) (by simp)]
      rfl
    have hLayerShape2 : (pmFinal 302).shape = [4, 3, 8] := by
      rw [hLayerPm2]
      unfold fw_layernorm
      rw [hLayerIn.shard_shapes (pmStore 202) (by simp)]
      rfl
    have hLayerShape3 : (pmFinal 303).shape = [4, 3, 8] := by
      rw [hLayerPm3]
      unfold fw_layernorm
      rw [hLayerIn.shard_shapes (pmStore 203) (by simp)]
      rfl
    have hLayerFullShape : (smFinal 110).shape = [4, 12, 8] := by
      rw [hLayerValue, allGatherPrimDimN_shape 1 [pmFinal 300, pmFinal 301, pmFinal 302, pmFinal 303].length [pmFinal 300, pmFinal 301, pmFinal 302, pmFinal 303] [4, 3, 8]]
      · simp only [List.length_cons, List.length_nil]
        native_decide
      · simp only [List.head?, Option.map, Option.getD]
        exact hLayerShape0
    have hLayerOut : fact_layer.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 110) [pmFinal 300, pmFinal 301, pmFinal 302, pmFinal 303] 1 [4, 12, 8] [4, 3, 8]
      refine {
        full_value := hLayerValue
        full_shape := hLayerFullShape
        shards_nonempty := by simp
        gather_dim_lt := by native_decide
        shard_shapes := ?_
        shape_contract := by simp only [List.length_cons, List.length_nil] <;> native_decide
      }
      intro shard hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl
      · exact hLayerShape0
      · exact hLayerShape1
      · exact hLayerShape2
      · exact hLayerShape3
    let xs := inputTids.map pmFinal
    have hHead : ((xs.head?.map (fun t => t.shape)).getD []) = [4, 3, 8] := by
      simp only [xs, inputTids, List.map, List.head?, Option.map, Option.getD]
      exact hAllToAllInFinal.shard_shapes (pmFinal 220) (by simp)
    have hRankXs : rankCount = xs.length := by
      simp [rankCount, outputTids, xs, inputTids]
    have hInputPrefix0_0 : ((pmNodes.take 3).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 220 = pmFinal 220 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.drop 3) ((pmNodes.take 3).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 220 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 3 ++ pmNodes.drop 3 = pmNodes by exact List.take_append_drop 3 pmNodes] at h
      exact h.symm
    have hInputPrefix0_1 : ((pmNodes.take 3).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 221 = pmFinal 221 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.drop 3) ((pmNodes.take 3).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 221 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 3 ++ pmNodes.drop 3 = pmNodes by exact List.take_append_drop 3 pmNodes] at h
      exact h.symm
    have hInputPrefix0_2 : ((pmNodes.take 3).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 222 = pmFinal 222 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.drop 3) ((pmNodes.take 3).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 222 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 3 ++ pmNodes.drop 3 = pmNodes by exact List.take_append_drop 3 pmNodes] at h
      exact h.symm
    have hInputPrefix0_3 : ((pmNodes.take 3).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 223 = pmFinal 223 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.drop 3) ((pmNodes.take 3).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 223 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 3 ++ pmNodes.drop 3 = pmNodes by exact List.take_append_drop 3 pmNodes] at h
      exact h.symm
    have hInputs0 : inputTids.map ((pmNodes.take 3).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) = xs := by
      simp only [inputTids, xs, List.map]
      rw [hInputPrefix0_0, hInputPrefix0_1, hInputPrefix0_2, hInputPrefix0_3]
    have hAllToAll0 : pmFinal 400 = allToAllPrimWithDims rankCount 0 xs 1 2 := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 400 = _
      rw [show pmNodes = pmNodes.take 3 ++ [{ rank := 0, op := "OpName.AllToAllPrim", ins := [220, 221, 222, 223], outs := [400], params := [1, 2] }] ++ pmNodes.drop 4 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticMixedLayernormAllToAll.gPM pmStore (pmNodes.take 3) (pmNodes.drop 4) { rank := 0, op := "OpName.AllToAllPrim", ins := [220, 221, 222, 223], outs := [400], params := [1, 2] } 400 (fun t => allToAllPrimWithDims rankCount 0 (inputTids.map t) 1 2)]
      · rw [hInputs0]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount]
        simpa [inputTids] using applyNode_allToAllPrimWithDims_out SyntheticMixedLayernormAllToAll.gPM t 0 inputTids 400 1 2
      · native_decide
      · native_decide
    have hAllToAllShape0 : (pmFinal 400).shape = [4, 12, 2] := by
      rw [hAllToAll0, allToAllPrimWithDims_shape rankCount 0 xs 1 2 [4, 3, 8] hHead (by native_decide)]
      native_decide
    have hInputPrefix1_0 : ((pmNodes.take 4).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 220 = pmFinal 220 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.drop 4) ((pmNodes.take 4).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 220 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 4 ++ pmNodes.drop 4 = pmNodes by exact List.take_append_drop 4 pmNodes] at h
      exact h.symm
    have hInputPrefix1_1 : ((pmNodes.take 4).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 221 = pmFinal 221 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.drop 4) ((pmNodes.take 4).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 221 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 4 ++ pmNodes.drop 4 = pmNodes by exact List.take_append_drop 4 pmNodes] at h
      exact h.symm
    have hInputPrefix1_2 : ((pmNodes.take 4).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 222 = pmFinal 222 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.drop 4) ((pmNodes.take 4).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 222 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 4 ++ pmNodes.drop 4 = pmNodes by exact List.take_append_drop 4 pmNodes] at h
      exact h.symm
    have hInputPrefix1_3 : ((pmNodes.take 4).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 223 = pmFinal 223 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.drop 4) ((pmNodes.take 4).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 223 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 4 ++ pmNodes.drop 4 = pmNodes by exact List.take_append_drop 4 pmNodes] at h
      exact h.symm
    have hInputs1 : inputTids.map ((pmNodes.take 4).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) = xs := by
      simp only [inputTids, xs, List.map]
      rw [hInputPrefix1_0, hInputPrefix1_1, hInputPrefix1_2, hInputPrefix1_3]
    have hAllToAll1 : pmFinal 401 = allToAllPrimWithDims rankCount 1 xs 1 2 := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 401 = _
      rw [show pmNodes = pmNodes.take 4 ++ [{ rank := 1, op := "OpName.AllToAllPrim", ins := [220, 221, 222, 223], outs := [401], params := [1, 2] }] ++ pmNodes.drop 5 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticMixedLayernormAllToAll.gPM pmStore (pmNodes.take 4) (pmNodes.drop 5) { rank := 1, op := "OpName.AllToAllPrim", ins := [220, 221, 222, 223], outs := [401], params := [1, 2] } 401 (fun t => allToAllPrimWithDims rankCount 1 (inputTids.map t) 1 2)]
      · rw [hInputs1]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount]
        simpa [inputTids] using applyNode_allToAllPrimWithDims_out SyntheticMixedLayernormAllToAll.gPM t 1 inputTids 401 1 2
      · native_decide
      · native_decide
    have hAllToAllShape1 : (pmFinal 401).shape = [4, 12, 2] := by
      rw [hAllToAll1, allToAllPrimWithDims_shape rankCount 1 xs 1 2 [4, 3, 8] hHead (by native_decide)]
      native_decide
    have hInputPrefix2_0 : ((pmNodes.take 5).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 220 = pmFinal 220 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.drop 5) ((pmNodes.take 5).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 220 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 5 ++ pmNodes.drop 5 = pmNodes by exact List.take_append_drop 5 pmNodes] at h
      exact h.symm
    have hInputPrefix2_1 : ((pmNodes.take 5).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 221 = pmFinal 221 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.drop 5) ((pmNodes.take 5).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 221 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 5 ++ pmNodes.drop 5 = pmNodes by exact List.take_append_drop 5 pmNodes] at h
      exact h.symm
    have hInputPrefix2_2 : ((pmNodes.take 5).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 222 = pmFinal 222 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.drop 5) ((pmNodes.take 5).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 222 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 5 ++ pmNodes.drop 5 = pmNodes by exact List.take_append_drop 5 pmNodes] at h
      exact h.symm
    have hInputPrefix2_3 : ((pmNodes.take 5).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 223 = pmFinal 223 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.drop 5) ((pmNodes.take 5).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 223 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 5 ++ pmNodes.drop 5 = pmNodes by exact List.take_append_drop 5 pmNodes] at h
      exact h.symm
    have hInputs2 : inputTids.map ((pmNodes.take 5).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) = xs := by
      simp only [inputTids, xs, List.map]
      rw [hInputPrefix2_0, hInputPrefix2_1, hInputPrefix2_2, hInputPrefix2_3]
    have hAllToAll2 : pmFinal 402 = allToAllPrimWithDims rankCount 2 xs 1 2 := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 402 = _
      rw [show pmNodes = pmNodes.take 5 ++ [{ rank := 2, op := "OpName.AllToAllPrim", ins := [220, 221, 222, 223], outs := [402], params := [1, 2] }] ++ pmNodes.drop 6 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticMixedLayernormAllToAll.gPM pmStore (pmNodes.take 5) (pmNodes.drop 6) { rank := 2, op := "OpName.AllToAllPrim", ins := [220, 221, 222, 223], outs := [402], params := [1, 2] } 402 (fun t => allToAllPrimWithDims rankCount 2 (inputTids.map t) 1 2)]
      · rw [hInputs2]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount]
        simpa [inputTids] using applyNode_allToAllPrimWithDims_out SyntheticMixedLayernormAllToAll.gPM t 2 inputTids 402 1 2
      · native_decide
      · native_decide
    have hAllToAllShape2 : (pmFinal 402).shape = [4, 12, 2] := by
      rw [hAllToAll2, allToAllPrimWithDims_shape rankCount 2 xs 1 2 [4, 3, 8] hHead (by native_decide)]
      native_decide
    have hInputPrefix3_0 : ((pmNodes.take 7).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 220 = pmFinal 220 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.drop 7) ((pmNodes.take 7).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 220 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 7 ++ pmNodes.drop 7 = pmNodes by exact List.take_append_drop 7 pmNodes] at h
      exact h.symm
    have hInputPrefix3_1 : ((pmNodes.take 7).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 221 = pmFinal 221 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.drop 7) ((pmNodes.take 7).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 221 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 7 ++ pmNodes.drop 7 = pmNodes by exact List.take_append_drop 7 pmNodes] at h
      exact h.symm
    have hInputPrefix3_2 : ((pmNodes.take 7).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 222 = pmFinal 222 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.drop 7) ((pmNodes.take 7).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 222 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 7 ++ pmNodes.drop 7 = pmNodes by exact List.take_append_drop 7 pmNodes] at h
      exact h.symm
    have hInputPrefix3_3 : ((pmNodes.take 7).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 223 = pmFinal 223 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLayernormAllToAll.gPM (pmNodes.drop 7) ((pmNodes.take 7).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 223 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 7 ++ pmNodes.drop 7 = pmNodes by exact List.take_append_drop 7 pmNodes] at h
      exact h.symm
    have hInputs3 : inputTids.map ((pmNodes.take 7).foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) = xs := by
      simp only [inputTids, xs, List.map]
      rw [hInputPrefix3_0, hInputPrefix3_1, hInputPrefix3_2, hInputPrefix3_3]
    have hAllToAll3 : pmFinal 403 = allToAllPrimWithDims rankCount 3 xs 1 2 := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLayernormAllToAll.gPM) pmStore) 403 = _
      rw [show pmNodes = pmNodes.take 7 ++ [{ rank := 3, op := "OpName.AllToAllPrim", ins := [220, 221, 222, 223], outs := [403], params := [1, 2] }] ++ pmNodes.drop 8 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticMixedLayernormAllToAll.gPM pmStore (pmNodes.take 7) (pmNodes.drop 8) { rank := 3, op := "OpName.AllToAllPrim", ins := [220, 221, 222, 223], outs := [403], params := [1, 2] } 403 (fun t => allToAllPrimWithDims rankCount 3 (inputTids.map t) 1 2)]
      · rw [hInputs3]
      · intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
          (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp only [applyNodeDistributedFaithful, applyNodeDistributed, applyNodeRingAttn]
        rw [hRankCount]
        simpa [inputTids] using applyNode_allToAllPrimWithDims_out SyntheticMixedLayernormAllToAll.gPM t 3 inputTids 403 1 2
      · native_decide
      · native_decide
    have hAllToAllShape3 : (pmFinal 403).shape = [4, 12, 2] := by
      rw [hAllToAll3, allToAllPrimWithDims_shape rankCount 3 xs 1 2 [4, 3, 8] hHead (by native_decide)]
      native_decide
    have hOrderedOutputs : outputTids.map pmFinal =
        List.ofFn (fun r : Fin rankCount => allToAllPrimWithDims rankCount r.1 xs 1 2) := by
      simp only [outputTids, rankCount, List.map]
      rw [hAllToAll0, hAllToAll1, hAllToAll2, hAllToAll3]
      rfl
    have hGatherShape : (allGatherPrimDimN 1 rankCount 0 xs).shape = [4, 12, 8] := by
      rw [hRankXs]
      calc
        _ = (smFinal 120).shape := congrArg (fun t => t.shape) hAllToAllInFinal.full_value.symm
        _ = _ := hAllToAllInFinal.full_shape
    have hOdim : 2 < (allGatherPrimDimN 1 rankCount 0 xs).shape.length := by
      rw [hGatherShape]
      native_decide
    have hDiv : (allGatherPrimDimN 1 rankCount 0 xs).shape.getD 2 0 % rankCount = 0 := by
      rw [hGatherShape]
      native_decide
    have hOdimXs := hOdim
    have hDivXs := hDiv
    rw [hRankXs] at hOdimXs hDivXs
    have hFinalOut : fact_output.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 120) [pmFinal 400, pmFinal 401, pmFinal 402, pmFinal 403] 2 [4, 12, 8] [4, 12, 2]
      refine {
        full_value := ?_
        full_shape := hAllToAllInFinal.full_shape
        shards_nonempty := by simp
        gather_dim_lt := by native_decide
        shard_shapes := ?_
        shape_contract := by simp only [List.length_cons, List.length_nil] <;> native_decide
      }
      · rw [show [pmFinal 400, pmFinal 401, pmFinal 402, pmFinal 403] = outputTids.map pmFinal by rfl, hOrderedOutputs, List.length_ofFn]
        rw [hRankXs, TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn 1 2 xs (by simp [xs, inputTids]) hOdimXs hDivXs]
        simp only [rankCount, outputTids, xs, inputTids, List.map, List.length_cons, List.length_nil]
        exact hAllToAllInFinal.full_value
      · intro shard hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl | rfl
        · exact hAllToAllShape0
        · exact hAllToAllShape1
        · exact hAllToAllShape2
        · exact hAllToAllShape3
    intro fact hfact
    have covered : fact ∈ [fact_layer, fact_output] ++ state_pre.facts := by
      exact (show state_post.facts ⊆ [fact_layer, fact_output] ++ state_pre.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl | rfl
      · exact hLayerOut
      · exact hFinalOut
    · exact hframe fact old

#print axioms segment_000092
end
end SyntheticMixedLayernormAllToAll
end TrainVerify.Denote
