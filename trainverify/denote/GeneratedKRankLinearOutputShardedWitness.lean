import denote.RelationCompiler

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticLinearOutput
noncomputable section
set_option maxHeartbeats 500000

def gSM : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_linear", ins := [100, 101], outs := [110] }] }
def gPM : GraphDecl := { numRanks := 3, nodes := [{ rank := 0, op := "OpName.FW_linear", ins := [200, 201], outs := [301] }, { rank := 1, op := "OpName.FW_linear", ins := [200, 202], outs := [302] }, { rank := 2, op := "OpName.FW_linear", ins := [200, 203], outs := [303] }] }

def fact_activation : RelationFact := .joined 100 200 [1, 5, 7]
def fact_weight : RelationFact := .sharded 101 [201, 202, 203] 0 [33, 7] [11, 7]
def fact_output : RelationFact := .sharded 110 [301, 302, 303] 2 [1, 5, 33] [1, 5, 11]
def state_pre : RelationState where
  facts := [fact_activation, fact_weight]
  nonempty := by decide
def state_post : RelationState where
  facts := [fact_output]
  nonempty := by decide

private def segment_000000_smNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [100, 101], outs := [110] }]
private def segment_000000_pmNodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [200, 201], outs := [301] }, { rank := 1, op := "OpName.FW_linear", ins := [200, 202], outs := [302] }, { rank := 2, op := "OpName.FW_linear", ins := [200, 203], outs := [303] }]
@[irreducible] private def segment_000000_smFinal (s : Store) : Store :=
  segment_000000_smNodes.foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gSM) s
@[irreducible] private def segment_000000_pmFinal (s : Store) : Store :=
  segment_000000_pmNodes.foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) s

private theorem segment_000000_smWriter (smStore : Store) :
    (segment_000000_smFinal smStore) 110 = fw_linear ((segment_000000_smFinal smStore) 100) ((segment_000000_smFinal smStore) 101) := by
  have hfinal : (segment_000000_smFinal smStore) = segment_000000_smNodes.foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gSM) smStore := by
    unfold segment_000000_smFinal
    rfl
  have hout_nodes : segment_000000_smNodes = (segment_000000_smNodes.take 0) ++ [{ rank := 0, op := "OpName.FW_linear", ins := [100, 101], outs := [110] }] ++ (segment_000000_smNodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_smFinal smStore) 110 = fw_linear (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gSM) smStore 100) (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gSM) smStore 101) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticLinearOutput.gSM smStore
      (segment_000000_smNodes.take 0) (segment_000000_smNodes.drop 1)
      { rank := 0, op := "OpName.FW_linear", ins := [100, 101], outs := [110] } 110
      (fun t => fw_linear (t 100) (t 101)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out SyntheticLinearOutput.gSM t 0 100 101 110
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gSM) smStore 100 = (segment_000000_smFinal smStore) 100 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLinearOutput.gSM smStore
      (segment_000000_smNodes.take 0) ({ rank := 0, op := "OpName.FW_linear", ins := [100, 101], outs := [110] } :: (segment_000000_smNodes.drop 1)) 100
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gSM) smStore 101 = (segment_000000_smFinal smStore) 101 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLinearOutput.gSM smStore
      (segment_000000_smNodes.take 0) ({ rank := 0, op := "OpName.FW_linear", ins := [100, 101], outs := [110] } :: (segment_000000_smNodes.drop 1)) 101
      (by native_decide) (by native_decide)
  have hout : (segment_000000_smFinal smStore) 110 = fw_linear ((segment_000000_smFinal smStore) 100) ((segment_000000_smFinal smStore) 101) := by
    calc
      _ = fw_linear (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gSM) smStore 100) (((segment_000000_smNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gSM) smStore 101) := hout_prefix
      _ = fw_linear ((segment_000000_smFinal smStore) 100) ((segment_000000_smFinal smStore) 101) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_pmWriter0 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 301 = fw_linear ((segment_000000_pmFinal pmStore) 200) ((segment_000000_pmFinal pmStore) 201) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 0) ++ [{ rank := 0, op := "OpName.FW_linear", ins := [200, 201], outs := [301] }] ++ (segment_000000_pmNodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 301 = fw_linear (((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore 200) (((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore 201) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticLinearOutput.gPM pmStore
      (segment_000000_pmNodes.take 0) (segment_000000_pmNodes.drop 1)
      { rank := 0, op := "OpName.FW_linear", ins := [200, 201], outs := [301] } 301
      (fun t => fw_linear (t 200) (t 201)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out SyntheticLinearOutput.gPM t 0 200 201 301
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore 200 = (segment_000000_pmFinal pmStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLinearOutput.gPM pmStore
      (segment_000000_pmNodes.take 0) ({ rank := 0, op := "OpName.FW_linear", ins := [200, 201], outs := [301] } :: (segment_000000_pmNodes.drop 1)) 200
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore 201 = (segment_000000_pmFinal pmStore) 201 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLinearOutput.gPM pmStore
      (segment_000000_pmNodes.take 0) ({ rank := 0, op := "OpName.FW_linear", ins := [200, 201], outs := [301] } :: (segment_000000_pmNodes.drop 1)) 201
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 301 = fw_linear ((segment_000000_pmFinal pmStore) 200) ((segment_000000_pmFinal pmStore) 201) := by
    calc
      _ = fw_linear (((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore 200) (((segment_000000_pmNodes.take 0)).foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore 201) := hout_prefix
      _ = fw_linear ((segment_000000_pmFinal pmStore) 200) ((segment_000000_pmFinal pmStore) 201) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_pmWriter1 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 302 = fw_linear ((segment_000000_pmFinal pmStore) 200) ((segment_000000_pmFinal pmStore) 202) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 1) ++ [{ rank := 1, op := "OpName.FW_linear", ins := [200, 202], outs := [302] }] ++ (segment_000000_pmNodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 302 = fw_linear (((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore 200) (((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore 202) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticLinearOutput.gPM pmStore
      (segment_000000_pmNodes.take 1) (segment_000000_pmNodes.drop 2)
      { rank := 1, op := "OpName.FW_linear", ins := [200, 202], outs := [302] } 302
      (fun t => fw_linear (t 200) (t 202)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out SyntheticLinearOutput.gPM t 1 200 202 302
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore 200 = (segment_000000_pmFinal pmStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLinearOutput.gPM pmStore
      (segment_000000_pmNodes.take 1) ({ rank := 1, op := "OpName.FW_linear", ins := [200, 202], outs := [302] } :: (segment_000000_pmNodes.drop 2)) 200
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore 202 = (segment_000000_pmFinal pmStore) 202 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLinearOutput.gPM pmStore
      (segment_000000_pmNodes.take 1) ({ rank := 1, op := "OpName.FW_linear", ins := [200, 202], outs := [302] } :: (segment_000000_pmNodes.drop 2)) 202
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 302 = fw_linear ((segment_000000_pmFinal pmStore) 200) ((segment_000000_pmFinal pmStore) 202) := by
    calc
      _ = fw_linear (((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore 200) (((segment_000000_pmNodes.take 1)).foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore 202) := hout_prefix
      _ = fw_linear ((segment_000000_pmFinal pmStore) 200) ((segment_000000_pmFinal pmStore) 202) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_pmWriter2 (pmStore : Store) :
    (segment_000000_pmFinal pmStore) 303 = fw_linear ((segment_000000_pmFinal pmStore) 200) ((segment_000000_pmFinal pmStore) 203) := by
  have hfinal : (segment_000000_pmFinal pmStore) = segment_000000_pmNodes.foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore := by
    unfold segment_000000_pmFinal
    rfl
  have hout_nodes : segment_000000_pmNodes = (segment_000000_pmNodes.take 2) ++ [{ rank := 2, op := "OpName.FW_linear", ins := [200, 203], outs := [303] }] ++ (segment_000000_pmNodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pmFinal pmStore) 303 = fw_linear (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore 200) (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore 203) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SyntheticLinearOutput.gPM pmStore
      (segment_000000_pmNodes.take 2) (segment_000000_pmNodes.drop 3)
      { rank := 2, op := "OpName.FW_linear", ins := [200, 203], outs := [303] } 303
      (fun t => fw_linear (t 200) (t 203)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_linear_out SyntheticLinearOutput.gPM t 2 200 203 303
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore 200 = (segment_000000_pmFinal pmStore) 200 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLinearOutput.gPM pmStore
      (segment_000000_pmNodes.take 2) ({ rank := 2, op := "OpName.FW_linear", ins := [200, 203], outs := [303] } :: (segment_000000_pmNodes.drop 3)) 200
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore 203 = (segment_000000_pmFinal pmStore) 203 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SyntheticLinearOutput.gPM pmStore
      (segment_000000_pmNodes.take 2) ({ rank := 2, op := "OpName.FW_linear", ins := [200, 203], outs := [303] } :: (segment_000000_pmNodes.drop 3)) 203
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pmFinal pmStore) 303 = fw_linear ((segment_000000_pmFinal pmStore) 200) ((segment_000000_pmFinal pmStore) 203) := by
    calc
      _ = fw_linear (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore 200) (((segment_000000_pmNodes.take 2)).foldl (applyNodeDistributedFaithful SyntheticLinearOutput.gPM) pmStore 203) := hout_prefix
      _ = fw_linear ((segment_000000_pmFinal pmStore) 200) ((segment_000000_pmFinal pmStore) 203) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_out (smStore pmStore : Store)
    (hActivation : fact_activation.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore))
    (hWeight : fact_weight.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore)) :
    fact_output.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore) := by
  change (segment_000000_smFinal smStore) 100 = (segment_000000_pmFinal pmStore) 200 ∧
    ((segment_000000_smFinal smStore) 100).shape = [1, 5, 7] ∧
    ((segment_000000_pmFinal pmStore) 200).shape = [1, 5, 7] at hActivation
  change ShardedRel ((segment_000000_smFinal smStore) 101) [(segment_000000_pmFinal pmStore) 201, (segment_000000_pmFinal pmStore) 202, (segment_000000_pmFinal pmStore) 203] 0 [33, 7] [11, 7] at hWeight
  have hSm := segment_000000_smWriter smStore
  have hPm0 := segment_000000_pmWriter0 pmStore
  have hPm1 := segment_000000_pmWriter1 pmStore
  have hPm2 := segment_000000_pmWriter2 pmStore
  have hComm := (TrainVerify.Denote.fw_linear_3d_weight_allGatherPrimDimN_dim0_comm
    (K := [(segment_000000_pmFinal pmStore) 201, (segment_000000_pmFinal pmStore) 202, (segment_000000_pmFinal pmStore) 203].length) (b := 1) (s := 5) (i := 7) (o := 11)
    (x := (segment_000000_pmFinal pmStore) 200) (ws := [(segment_000000_pmFinal pmStore) 201, (segment_000000_pmFinal pmStore) 202, (segment_000000_pmFinal pmStore) 203])
    (by simp) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by simp) hActivation.2.2 (fun w hw => hWeight.shard_shapes w hw))
  have hValue : (segment_000000_smFinal smStore) 110 = allGatherPrimDimN 2 [(segment_000000_pmFinal pmStore) 301, (segment_000000_pmFinal pmStore) 302, (segment_000000_pmFinal pmStore) 303].length 0 [(segment_000000_pmFinal pmStore) 301, (segment_000000_pmFinal pmStore) 302, (segment_000000_pmFinal pmStore) 303] := by
    rw [hSm, hActivation.1, hWeight.full_value, hComm]
    simp only [List.map, List.length_cons, List.length_nil]
    rw [← hPm0, ← hPm1, ← hPm2]
  have hOutShape0 : ((segment_000000_pmFinal pmStore) 301).shape = [1, 5, 11] := by
    rw [hPm0]
    exact fw_linear_3d_shape 1 5 7 11 _ _ hActivation.2.2
      (hWeight.shard_shapes ((segment_000000_pmFinal pmStore) 201) (by simp))
  have hOutShape1 : ((segment_000000_pmFinal pmStore) 302).shape = [1, 5, 11] := by
    rw [hPm1]
    exact fw_linear_3d_shape 1 5 7 11 _ _ hActivation.2.2
      (hWeight.shard_shapes ((segment_000000_pmFinal pmStore) 202) (by simp))
  have hOutShape2 : ((segment_000000_pmFinal pmStore) 303).shape = [1, 5, 11] := by
    rw [hPm2]
    exact fw_linear_3d_shape 1 5 7 11 _ _ hActivation.2.2
      (hWeight.shard_shapes ((segment_000000_pmFinal pmStore) 203) (by simp))
  unfold fact_output RelationFact.Holds
  change ShardedRel ((segment_000000_smFinal smStore) 110) [(segment_000000_pmFinal pmStore) 301, (segment_000000_pmFinal pmStore) 302, (segment_000000_pmFinal pmStore) 303] 2 [1, 5, 33] [1, 5, 11]
  refine {
    full_value := hValue
    full_shape := ?_
    shards_nonempty := by simp
    gather_dim_lt := by native_decide
    shard_shapes := ?_
    shape_contract := by simp only [List.length_cons, List.length_nil]; native_decide
  }
  · rw [hValue]
    rw [allGatherPrimDimN_shape 2 [(segment_000000_pmFinal pmStore) 301, (segment_000000_pmFinal pmStore) 302, (segment_000000_pmFinal pmStore) 303].length [(segment_000000_pmFinal pmStore) 301, (segment_000000_pmFinal pmStore) 302, (segment_000000_pmFinal pmStore) 303] [1, 5, 11]]
    · simp only [List.length_cons, List.length_nil]
      native_decide
    · simp only [List.head?, Option.map, Option.getD]
      exact hOutShape0
  · intro shard hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hOutShape0
    · exact hOutShape1
    · exact hOutShape2

private theorem segment_000000_sound (smStore pmStore : Store) (hstate : state_pre.Holds smStore pmStore) :
    state_post.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore) := by
  have hframe : state_pre.Holds (segment_000000_smFinal smStore) (segment_000000_pmFinal pmStore) := by
    unfold segment_000000_smFinal segment_000000_pmFinal
    apply RelationState.Holds.fold_frame segment_000000_smNodes segment_000000_pmNodes smStore pmStore hstate
    · native_decide
    · native_decide
    · native_decide
    · native_decide
  have hActivation := hframe fact_activation (by native_decide)
  have hWeight := hframe fact_weight (by native_decide)
  have hout := segment_000000_out smStore pmStore hActivation hWeight
  intro fact hfact
  have covered : fact ∈ [fact_output] ++ state_pre.facts := by
    exact (show state_post.facts ⊆ [fact_output] ++ state_pre.facts by native_decide) hfact
  simp only [List.mem_append] at covered
  rcases covered with fresh | old
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
    rcases fresh with rfl
    exact hout
  · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate SyntheticLinearOutput.gSM SyntheticLinearOutput.gPM state_pre state_post where
  smNodes := segment_000000_smNodes
  pmNodes := segment_000000_pmNodes
  sound := by
    intro smStore pmStore hstate
    simpa only [segment_000000_smFinal, segment_000000_pmFinal] using segment_000000_sound smStore pmStore hstate

#print axioms segment_000000
end
end SyntheticLinearOutput
end TrainVerify.Denote
