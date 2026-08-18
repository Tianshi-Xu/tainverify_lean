import denote.RelationCompiler
import denote.KRankLinearGather
import denote.KRankLayernormGather

namespace TrainVerify.Denote
open RelationCompiler

namespace SyntheticLinear
noncomputable section

def gSM : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_linear", ins := [100, 90], outs := [110] }] }
def gPM : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_linear", ins := [200, 90], outs := [300] }, { rank := 1, op := "OpName.FW_linear", ins := [201, 90], outs := [301] }, { rank := 2, op := "OpName.FW_linear", ins := [202, 90], outs := [302] }] }

def fact_in : RelationFact := .sharded 100 [200, 201, 202] 1 [2, 9, 5] [2, 3, 5]
def fact_out : RelationFact := .sharded 110 [300, 301, 302] 1 [2, 9, 7] [2, 3, 7]
def external_eq_90 : RelationFact := .tensorEq .sm 90 .pm 90
def external_shape_90 : RelationFact := .tensorShape .pm 90 [7, 5]

def state_pre : RelationState where
  facts := [fact_in, external_eq_90, external_shape_90]
  nonempty := by decide

def state_post : RelationState where
  facts := [fact_out]
  nonempty := by decide

private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [100, 90], outs := [110] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [200, 90], outs := [300] }, { rank := 1, op := "OpName.FW_linear", ins := [201, 90], outs := [301] }, { rank := 2, op := "OpName.FW_linear", ins := [202, 90], outs := [302] }]

private def segment_000000 :
    ClosedDepSegmentCertificate SyntheticLinear.gSM SyntheticLinear.gPM state_pre state_post where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := segment_000000_sm_nodes
    let pmNodes : List NodeDecl := segment_000000_pm_nodes
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticLinear.gSM) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hIn0 : fact_in.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 100) [pmStore 200, pmStore 201, pmStore 202] 1 [2, 9, 5] [2, 3, 5] at hIn0
    have hExternalEq0 : external_eq_90.Holds smStore pmStore := hstate _ (by native_decide)
    change smStore 90 = pmStore 90 at hExternalEq0
    have hExternalShape0 : external_shape_90.Holds smStore pmStore := hstate _ (by native_decide)
    change (pmStore 90).shape = [7, 5] at hExternalShape0
    have hSmWriter : smFinal 110 = fw_linear (smStore 100) (smStore 90) := by
      change (smNodes.foldl (applyNodeDistributedFaithful SyntheticLinear.gSM) smStore) 110 = _
      rw [show smNodes = smNodes.take 0 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [100, 90], outs := [110] }] ++ smNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticLinear.gSM smStore (smNodes.take 0) (smNodes.drop 1)
        { rank := 0, op := "OpName.FW_linear", ins := [100, 90], outs := [110] } 110 (fun t => fw_linear (t 100) (t 90)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out SyntheticLinear.gSM t 0 100 90 110
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticLinear.gSM (smNodes.take 0) smStore 100 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written SyntheticLinear.gSM (smNodes.take 0) smStore 90 (by native_decide) (by native_decide)]
    have hPmWriter0 : pmFinal 300 = fw_linear (pmStore 200) (pmStore 90) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore) 300 = _
      rw [show pmNodes = pmNodes.take 0 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [200, 90], outs := [300] }] ++ pmNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticLinear.gPM pmStore (pmNodes.take 0) (pmNodes.drop 1)
        { rank := 0, op := "OpName.FW_linear", ins := [200, 90], outs := [300] } 300 (fun t => fw_linear (t 200) (t 90)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out SyntheticLinear.gPM t 0 200 90 300
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticLinear.gPM (pmNodes.take 0) pmStore 200 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written SyntheticLinear.gPM (pmNodes.take 0) pmStore 90 (by native_decide) (by native_decide)]
    have hPmWriter1 : pmFinal 301 = fw_linear (pmStore 201) (pmStore 90) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore) 301 = _
      rw [show pmNodes = pmNodes.take 1 ++ [{ rank := 1, op := "OpName.FW_linear", ins := [201, 90], outs := [301] }] ++ pmNodes.drop 2 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticLinear.gPM pmStore (pmNodes.take 1) (pmNodes.drop 2)
        { rank := 1, op := "OpName.FW_linear", ins := [201, 90], outs := [301] } 301 (fun t => fw_linear (t 201) (t 90)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out SyntheticLinear.gPM t 1 201 90 301
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticLinear.gPM (pmNodes.take 1) pmStore 201 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written SyntheticLinear.gPM (pmNodes.take 1) pmStore 90 (by native_decide) (by native_decide)]
    have hPmWriter2 : pmFinal 302 = fw_linear (pmStore 202) (pmStore 90) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticLinear.gPM) pmStore) 302 = _
      rw [show pmNodes = pmNodes.take 2 ++ [{ rank := 2, op := "OpName.FW_linear", ins := [202, 90], outs := [302] }] ++ pmNodes.drop 3 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticLinear.gPM pmStore (pmNodes.take 2) (pmNodes.drop 3)
        { rank := 2, op := "OpName.FW_linear", ins := [202, 90], outs := [302] } 302 (fun t => fw_linear (t 202) (t 90)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out SyntheticLinear.gPM t 2 202 90 302
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticLinear.gPM (pmNodes.take 2) pmStore 202 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written SyntheticLinear.gPM (pmNodes.take 2) pmStore 90 (by native_decide) (by native_decide)]
    have hComm := (TrainVerify.Denote.fw_linear_3d_allGatherPrimDimN_dim1_comm (K := [pmStore 200, pmStore 201, pmStore 202].length) (b := 2) (s := 3) (i := 5) (o := 7) (xs := [pmStore 200, pmStore 201, pmStore 202]) (w := pmStore 90) (by simp) (by omega) (by omega) (by omega) (by omega) rfl (fun x hx => hIn0.shard_shapes x hx) hExternalShape0)
    have hOutValue : smFinal 110 = allGatherPrimDimN 1 [pmFinal 300, pmFinal 301, pmFinal 302].length 0 [pmFinal 300, pmFinal 301, pmFinal 302] := by
      rw [hSmWriter]
      rw [hExternalEq0]
      rw [hIn0.full_value]
      rw [hComm]
      simp only [List.map, List.length_cons, List.length_nil]
      rw [← hPmWriter0, ← hPmWriter1, ← hPmWriter2]
    have hOutShape0 : (pmFinal 300).shape = [2, 3, 7] := by
      rw [hPmWriter0]
      exact fw_linear_3d_shape 2 3 5 7 _ _ (hIn0.shard_shapes (pmStore 200) (by simp)) hExternalShape0
    have hOutShape1 : (pmFinal 301).shape = [2, 3, 7] := by
      rw [hPmWriter1]
      exact fw_linear_3d_shape 2 3 5 7 _ _ (hIn0.shard_shapes (pmStore 201) (by simp)) hExternalShape0
    have hOutShape2 : (pmFinal 302).shape = [2, 3, 7] := by
      rw [hPmWriter2]
      exact fw_linear_3d_shape 2 3 5 7 _ _ (hIn0.shard_shapes (pmStore 202) (by simp)) hExternalShape0
    have hout : fact_out.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 110) [pmFinal 300, pmFinal 301, pmFinal 302] 1 [2, 9, 7] [2, 3, 7]
      refine {
        full_value := hOutValue
        full_shape := ?_
        shards_nonempty := by simp
        gather_dim_lt := by norm_num
        shard_shapes := ?_
        shape_contract := by norm_num
      }
      · rw [hOutValue]
        rw [allGatherPrimDimN_shape 1 [pmFinal 300, pmFinal 301, pmFinal 302].length [pmFinal 300, pmFinal 301, pmFinal 302] [2, 3, 7]]
        · norm_num
        · simp only [List.head?, Option.map, Option.getD]
          exact hOutShape0
      · intro shard hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact hOutShape0
        · exact hOutShape1
        · exact hOutShape2
    intro fact hfact
    have covered : fact ∈ [fact_out] ++ state_pre.facts := by
      exact (show state_post.facts ⊆ [fact_out] ++ state_pre.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hout
    · exact hframe fact old

#check segment_000000
end
end SyntheticLinear

namespace SyntheticLayernorm
noncomputable section

def gSM : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_layernorm", ins := [100, 91, 92], outs := [110] }] }
def gPM : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_layernorm", ins := [200, 91, 92], outs := [300] }, { rank := 1, op := "OpName.FW_layernorm", ins := [201, 91, 92], outs := [301] }, { rank := 2, op := "OpName.FW_layernorm", ins := [202, 91, 92], outs := [302] }] }

def fact_in : RelationFact := .sharded 100 [200, 201, 202] 1 [2, 9, 5] [2, 3, 5]
def fact_out : RelationFact := .sharded 110 [300, 301, 302] 1 [2, 9, 5] [2, 3, 5]
def external_eq_91 : RelationFact := .tensorEq .sm 91 .pm 91
def external_shape_91 : RelationFact := .tensorShape .pm 91 [5]
def external_eq_92 : RelationFact := .tensorEq .sm 92 .pm 92
def external_shape_92 : RelationFact := .tensorShape .pm 92 [5]

def state_pre : RelationState where
  facts := [fact_in, external_eq_91, external_shape_91, external_eq_92, external_shape_92]
  nonempty := by decide

def state_post : RelationState where
  facts := [fact_out]
  nonempty := by decide

private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_layernorm", ins := [100, 91, 92], outs := [110] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_layernorm", ins := [200, 91, 92], outs := [300] }, { rank := 1, op := "OpName.FW_layernorm", ins := [201, 91, 92], outs := [301] }, { rank := 2, op := "OpName.FW_layernorm", ins := [202, 91, 92], outs := [302] }]

private def segment_000000 :
    ClosedDepSegmentCertificate SyntheticLayernorm.gSM SyntheticLayernorm.gPM state_pre state_post where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := segment_000000_sm_nodes
    let pmNodes : List NodeDecl := segment_000000_pm_nodes
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticLayernorm.gSM) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hIn0 : fact_in.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 100) [pmStore 200, pmStore 201, pmStore 202] 1 [2, 9, 5] [2, 3, 5] at hIn0
    have hExternalEq0 : external_eq_91.Holds smStore pmStore := hstate _ (by native_decide)
    change smStore 91 = pmStore 91 at hExternalEq0
    have hExternalShape0 : external_shape_91.Holds smStore pmStore := hstate _ (by native_decide)
    change (pmStore 91).shape = [5] at hExternalShape0
    have hExternalEq1 : external_eq_92.Holds smStore pmStore := hstate _ (by native_decide)
    change smStore 92 = pmStore 92 at hExternalEq1
    have hExternalShape1 : external_shape_92.Holds smStore pmStore := hstate _ (by native_decide)
    change (pmStore 92).shape = [5] at hExternalShape1
    have hSmWriter : smFinal 110 = fw_layernorm (smStore 100) (smStore 91) (smStore 92) := by
      change (smNodes.foldl (applyNodeDistributedFaithful SyntheticLayernorm.gSM) smStore) 110 = _
      rw [show smNodes = smNodes.take 0 ++ [{ rank := 0, op := "OpName.FW_layernorm", ins := [100, 91, 92], outs := [110] }] ++ smNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticLayernorm.gSM smStore (smNodes.take 0) (smNodes.drop 1)
        { rank := 0, op := "OpName.FW_layernorm", ins := [100, 91, 92], outs := [110] } 110 (fun t => fw_layernorm (t 100) (t 91) (t 92)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_layernorm_out SyntheticLayernorm.gSM t 0 100 91 92 110 []
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticLayernorm.gSM (smNodes.take 0) smStore 100 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written SyntheticLayernorm.gSM (smNodes.take 0) smStore 91 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written SyntheticLayernorm.gSM (smNodes.take 0) smStore 92 (by native_decide) (by native_decide)]
    have hPmWriter0 : pmFinal 300 = fw_layernorm (pmStore 200) (pmStore 91) (pmStore 92) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore) 300 = _
      rw [show pmNodes = pmNodes.take 0 ++ [{ rank := 0, op := "OpName.FW_layernorm", ins := [200, 91, 92], outs := [300] }] ++ pmNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticLayernorm.gPM pmStore (pmNodes.take 0) (pmNodes.drop 1)
        { rank := 0, op := "OpName.FW_layernorm", ins := [200, 91, 92], outs := [300] } 300 (fun t => fw_layernorm (t 200) (t 91) (t 92)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_layernorm_out SyntheticLayernorm.gPM t 0 200 91 92 300 []
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticLayernorm.gPM (pmNodes.take 0) pmStore 200 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written SyntheticLayernorm.gPM (pmNodes.take 0) pmStore 91 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written SyntheticLayernorm.gPM (pmNodes.take 0) pmStore 92 (by native_decide) (by native_decide)]
    have hPmWriter1 : pmFinal 301 = fw_layernorm (pmStore 201) (pmStore 91) (pmStore 92) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore) 301 = _
      rw [show pmNodes = pmNodes.take 1 ++ [{ rank := 1, op := "OpName.FW_layernorm", ins := [201, 91, 92], outs := [301] }] ++ pmNodes.drop 2 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticLayernorm.gPM pmStore (pmNodes.take 1) (pmNodes.drop 2)
        { rank := 1, op := "OpName.FW_layernorm", ins := [201, 91, 92], outs := [301] } 301 (fun t => fw_layernorm (t 201) (t 91) (t 92)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_layernorm_out SyntheticLayernorm.gPM t 1 201 91 92 301 []
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticLayernorm.gPM (pmNodes.take 1) pmStore 201 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written SyntheticLayernorm.gPM (pmNodes.take 1) pmStore 91 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written SyntheticLayernorm.gPM (pmNodes.take 1) pmStore 92 (by native_decide) (by native_decide)]
    have hPmWriter2 : pmFinal 302 = fw_layernorm (pmStore 202) (pmStore 91) (pmStore 92) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticLayernorm.gPM) pmStore) 302 = _
      rw [show pmNodes = pmNodes.take 2 ++ [{ rank := 2, op := "OpName.FW_layernorm", ins := [202, 91, 92], outs := [302] }] ++ pmNodes.drop 3 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticLayernorm.gPM pmStore (pmNodes.take 2) (pmNodes.drop 3)
        { rank := 2, op := "OpName.FW_layernorm", ins := [202, 91, 92], outs := [302] } 302 (fun t => fw_layernorm (t 202) (t 91) (t 92)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_layernorm_out SyntheticLayernorm.gPM t 2 202 91 92 302 []
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticLayernorm.gPM (pmNodes.take 2) pmStore 202 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written SyntheticLayernorm.gPM (pmNodes.take 2) pmStore 91 (by native_decide) (by native_decide),
        foldl_applyNodeDistributedFaithful_at_not_written SyntheticLayernorm.gPM (pmNodes.take 2) pmStore 92 (by native_decide) (by native_decide)]
    have hComm := (TrainVerify.Denote.fw_layernorm_distribute_allGatherPrimDimN_dim1_K_3d (K := [pmStore 200, pmStore 201, pmStore 202].length) (b := 2) (s := 3) (d := 5) (xs := [pmStore 200, pmStore 201, pmStore 202]) (gamma := pmStore 91) (beta := pmStore 92) (by simp) (by omega) (by omega) (by omega) rfl (fun x hx => hIn0.shard_shapes x hx) hExternalShape0 hExternalShape1)
    have hOutValue : smFinal 110 = allGatherPrimDimN 1 [pmFinal 300, pmFinal 301, pmFinal 302].length 0 [pmFinal 300, pmFinal 301, pmFinal 302] := by
      rw [hSmWriter]
      rw [hExternalEq0]
      rw [hExternalEq1]
      rw [hIn0.full_value]
      rw [hComm]
      simp only [List.map, List.length_cons, List.length_nil]
      rw [← hPmWriter0, ← hPmWriter1, ← hPmWriter2]
    have hOutShape0 : (pmFinal 300).shape = [2, 3, 5] := by
      rw [hPmWriter0]
      unfold fw_layernorm
      rw [(hIn0.shard_shapes (pmStore 200) (by simp))]
      rfl
    have hOutShape1 : (pmFinal 301).shape = [2, 3, 5] := by
      rw [hPmWriter1]
      unfold fw_layernorm
      rw [(hIn0.shard_shapes (pmStore 201) (by simp))]
      rfl
    have hOutShape2 : (pmFinal 302).shape = [2, 3, 5] := by
      rw [hPmWriter2]
      unfold fw_layernorm
      rw [(hIn0.shard_shapes (pmStore 202) (by simp))]
      rfl
    have hout : fact_out.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 110) [pmFinal 300, pmFinal 301, pmFinal 302] 1 [2, 9, 5] [2, 3, 5]
      refine {
        full_value := hOutValue
        full_shape := ?_
        shards_nonempty := by simp
        gather_dim_lt := by norm_num
        shard_shapes := ?_
        shape_contract := by norm_num
      }
      · rw [hOutValue]
        rw [allGatherPrimDimN_shape 1 [pmFinal 300, pmFinal 301, pmFinal 302].length [pmFinal 300, pmFinal 301, pmFinal 302] [2, 3, 5]]
        · norm_num
        · simp only [List.head?, Option.map, Option.getD]
          exact hOutShape0
      · intro shard hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact hOutShape0
        · exact hOutShape1
        · exact hOutShape2
    intro fact hfact
    have covered : fact ∈ [fact_out] ++ state_pre.facts := by
      exact (show state_post.facts ⊆ [fact_out] ++ state_pre.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl
      exact hout
    · exact hframe fact old

#check segment_000000
end
end SyntheticLayernorm

end TrainVerify.Denote
