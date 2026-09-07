import denote.RelationCompiler
import denote.KRankBWSumSequence
open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler
namespace SumWitness
noncomputable section
set_option maxHeartbeats 500000
def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_float", ins := [8], outs := [10] }, { rank := 0, op := "OpName.FW_sum", ins := [10], outs := [20] }, { rank := 0, op := "OpName.BW_sum", ins := [9, 10], outs := [30] }], replicaGroups := [] }
def pmGraph : GraphDecl := { numRanks := 2, nodes := [{ rank := 0, op := "OpName.FW_float", ins := [8], outs := [1000] }, { rank := 1, op := "OpName.FW_float", ins := [8], outs := [993] }, { rank := 0, op := "OpName.FW_sum", ins := [1000], outs := [2000] }, { rank := 0, op := "OpName.BW_sum", ins := [9, 1000], outs := [3000] }, { rank := 1, op := "OpName.FW_sum", ins := [993], outs := [1993] }, { rank := 1, op := "OpName.BW_sum", ins := [9, 993], outs := [2993] }], replicaGroups := [] }
private def fact_g : RelationFact := .reduction 9 [9] [1]
private def fact_x : RelationFact := .sharded 10 [1000, 993] 1 [2, 6, 5] [2, 3, 5]
private def fact_sum : RelationFact := .reduction 20 [2000, 1993] [1]
private def fact_bw : RelationFact := .sharded 30 [3000, 2993] 1 [2, 6, 5] [2, 3, 5]
private def anchor : RelationFact := .tensorShape .sm 8 [1]
private def state_before : RelationState where
  facts := [fact_g, fact_x, anchor]
  nonempty := by decide
private def state_after : RelationState where
  facts := [fact_g, fact_x, fact_sum, fact_bw, anchor]
  nonempty := by decide
private def segment_000000_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_sum", ins := [10], outs := [20] }, { rank := 0, op := "OpName.BW_sum", ins := [9, 10], outs := [30] }]
private def segment_000000_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_sum", ins := [1000], outs := [2000] }, { rank := 0, op := "OpName.BW_sum", ins := [9, 1000], outs := [3000] }, { rank := 1, op := "OpName.FW_sum", ins := [993], outs := [1993] }, { rank := 1, op := "OpName.BW_sum", ins := [9, 993], outs := [2993] }]
@[irreducible] private def segment_000000_sm_final (store : Store) : Store :=
  segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SumWitness.smGraph) store
@[irreducible] private def segment_000000_pm_final (store : Store) : Store :=
  segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SumWitness.pmGraph) store

private theorem segment_000000_sumSm (smStore : Store) :
    (segment_000000_sm_final smStore) 20 = fw_sum ((segment_000000_sm_final smStore) 10) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SumWitness.smGraph) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.FW_sum", ins := [10], outs := [20] }] ++ (segment_000000_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 20 = fw_sum (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SumWitness.smGraph) smStore 10) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SumWitness.smGraph smStore
      (segment_000000_sm_nodes.take 0) (segment_000000_sm_nodes.drop 1)
      { rank := 0, op := "OpName.FW_sum", ins := [10], outs := [20] } 20
      (fun t => fw_sum (t 10)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_sum_out SumWitness.smGraph t 0 10 20
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SumWitness.smGraph) smStore 10 = (segment_000000_sm_final smStore) 10 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SumWitness.smGraph smStore
      (segment_000000_sm_nodes.take 0) ({ rank := 0, op := "OpName.FW_sum", ins := [10], outs := [20] } :: (segment_000000_sm_nodes.drop 1)) 10
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 20 = fw_sum ((segment_000000_sm_final smStore) 10) := by
    calc
      _ = fw_sum (((segment_000000_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful SumWitness.smGraph) smStore 10) := hout_prefix
      _ = fw_sum ((segment_000000_sm_final smStore) 10) := by rw [hout_read_0]
  exact hout

private theorem segment_000000_bwSm (smStore : Store) :
    (segment_000000_sm_final smStore) 30 = bw_sum ((segment_000000_sm_final smStore) 9) ((segment_000000_sm_final smStore) 10) := by
  have hfinal : (segment_000000_sm_final smStore) = segment_000000_sm_nodes.foldl (applyNodeDistributedFaithful SumWitness.smGraph) smStore := by
    unfold segment_000000_sm_final
    rfl
  have hout_nodes : segment_000000_sm_nodes = (segment_000000_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_sum", ins := [9, 10], outs := [30] }] ++ (segment_000000_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_sm_final smStore) 30 = bw_sum (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SumWitness.smGraph) smStore 9) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SumWitness.smGraph) smStore 10) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SumWitness.smGraph smStore
      (segment_000000_sm_nodes.take 1) (segment_000000_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_sum", ins := [9, 10], outs := [30] } 30
      (fun t => bw_sum (t 9) (t 10)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_sum_out SumWitness.smGraph t 0 9 10 30
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SumWitness.smGraph) smStore 9 = (segment_000000_sm_final smStore) 9 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SumWitness.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_sum", ins := [9, 10], outs := [30] } :: (segment_000000_sm_nodes.drop 2)) 9
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SumWitness.smGraph) smStore 10 = (segment_000000_sm_final smStore) 10 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SumWitness.smGraph smStore
      (segment_000000_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_sum", ins := [9, 10], outs := [30] } :: (segment_000000_sm_nodes.drop 2)) 10
      (by native_decide) (by native_decide)
  have hout : (segment_000000_sm_final smStore) 30 = bw_sum ((segment_000000_sm_final smStore) 9) ((segment_000000_sm_final smStore) 10) := by
    calc
      _ = bw_sum (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SumWitness.smGraph) smStore 9) (((segment_000000_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful SumWitness.smGraph) smStore 10) := hout_prefix
      _ = bw_sum ((segment_000000_sm_final smStore) 9) ((segment_000000_sm_final smStore) 10) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_sumPm0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 2000 = fw_sum ((segment_000000_pm_final pmStore) 1000) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SumWitness.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.FW_sum", ins := [1000], outs := [2000] }] ++ (segment_000000_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2000 = fw_sum (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SumWitness.pmGraph) pmStore 1000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SumWitness.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) (segment_000000_pm_nodes.drop 1)
      { rank := 0, op := "OpName.FW_sum", ins := [1000], outs := [2000] } 2000
      (fun t => fw_sum (t 1000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_sum_out SumWitness.pmGraph t 0 1000 2000
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SumWitness.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SumWitness.pmGraph pmStore
      (segment_000000_pm_nodes.take 0) ({ rank := 0, op := "OpName.FW_sum", ins := [1000], outs := [2000] } :: (segment_000000_pm_nodes.drop 1)) 1000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2000 = fw_sum ((segment_000000_pm_final pmStore) 1000) := by
    calc
      _ = fw_sum (((segment_000000_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful SumWitness.pmGraph) pmStore 1000) := hout_prefix
      _ = fw_sum ((segment_000000_pm_final pmStore) 1000) := by rw [hout_read_0]
  exact hout

private theorem segment_000000_bwPm0 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 3000 = bw_sum ((segment_000000_pm_final pmStore) 9) ((segment_000000_pm_final pmStore) 1000) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SumWitness.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_sum", ins := [9, 1000], outs := [3000] }] ++ (segment_000000_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 3000 = bw_sum (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SumWitness.pmGraph) pmStore 9) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SumWitness.pmGraph) pmStore 1000) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SumWitness.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) (segment_000000_pm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_sum", ins := [9, 1000], outs := [3000] } 3000
      (fun t => bw_sum (t 9) (t 1000)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_sum_out SumWitness.pmGraph t 0 9 1000 3000
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SumWitness.pmGraph) pmStore 9 = (segment_000000_pm_final pmStore) 9 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SumWitness.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_sum", ins := [9, 1000], outs := [3000] } :: (segment_000000_pm_nodes.drop 2)) 9
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SumWitness.pmGraph) pmStore 1000 = (segment_000000_pm_final pmStore) 1000 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SumWitness.pmGraph pmStore
      (segment_000000_pm_nodes.take 1) ({ rank := 0, op := "OpName.BW_sum", ins := [9, 1000], outs := [3000] } :: (segment_000000_pm_nodes.drop 2)) 1000
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 3000 = bw_sum ((segment_000000_pm_final pmStore) 9) ((segment_000000_pm_final pmStore) 1000) := by
    calc
      _ = bw_sum (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SumWitness.pmGraph) pmStore 9) (((segment_000000_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful SumWitness.pmGraph) pmStore 1000) := hout_prefix
      _ = bw_sum ((segment_000000_pm_final pmStore) 9) ((segment_000000_pm_final pmStore) 1000) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_sumPm1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 1993 = fw_sum ((segment_000000_pm_final pmStore) 993) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SumWitness.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 2) ++ [{ rank := 1, op := "OpName.FW_sum", ins := [993], outs := [1993] }] ++ (segment_000000_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 1993 = fw_sum (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SumWitness.pmGraph) pmStore 993) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SumWitness.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) (segment_000000_pm_nodes.drop 3)
      { rank := 1, op := "OpName.FW_sum", ins := [993], outs := [1993] } 1993
      (fun t => fw_sum (t 993)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_fw_sum_out SumWitness.pmGraph t 1 993 1993
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SumWitness.pmGraph) pmStore 993 = (segment_000000_pm_final pmStore) 993 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SumWitness.pmGraph pmStore
      (segment_000000_pm_nodes.take 2) ({ rank := 1, op := "OpName.FW_sum", ins := [993], outs := [1993] } :: (segment_000000_pm_nodes.drop 3)) 993
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 1993 = fw_sum ((segment_000000_pm_final pmStore) 993) := by
    calc
      _ = fw_sum (((segment_000000_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful SumWitness.pmGraph) pmStore 993) := hout_prefix
      _ = fw_sum ((segment_000000_pm_final pmStore) 993) := by rw [hout_read_0]
  exact hout

private theorem segment_000000_bwPm1 (pmStore : Store) :
    (segment_000000_pm_final pmStore) 2993 = bw_sum ((segment_000000_pm_final pmStore) 9) ((segment_000000_pm_final pmStore) 993) := by
  have hfinal : (segment_000000_pm_final pmStore) = segment_000000_pm_nodes.foldl (applyNodeDistributedFaithful SumWitness.pmGraph) pmStore := by
    unfold segment_000000_pm_final
    rfl
  have hout_nodes : segment_000000_pm_nodes = (segment_000000_pm_nodes.take 3) ++ [{ rank := 1, op := "OpName.BW_sum", ins := [9, 993], outs := [2993] }] ++ (segment_000000_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000000_pm_final pmStore) 2993 = bw_sum (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SumWitness.pmGraph) pmStore 9) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SumWitness.pmGraph) pmStore 993) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer SumWitness.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) (segment_000000_pm_nodes.drop 4)
      { rank := 1, op := "OpName.BW_sum", ins := [9, 993], outs := [2993] } 2993
      (fun t => bw_sum (t 9) (t 993)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
        simp [applyNodeDistributed, applyNodeRingAttn]
        exact applyNode_bw_sum_out SumWitness.pmGraph t 1 9 993 2993
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SumWitness.pmGraph) pmStore 9 = (segment_000000_pm_final pmStore) 9 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SumWitness.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_sum", ins := [9, 993], outs := [2993] } :: (segment_000000_pm_nodes.drop 4)) 9
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SumWitness.pmGraph) pmStore 993 = (segment_000000_pm_final pmStore) 993 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final SumWitness.pmGraph pmStore
      (segment_000000_pm_nodes.take 3) ({ rank := 1, op := "OpName.BW_sum", ins := [9, 993], outs := [2993] } :: (segment_000000_pm_nodes.drop 4)) 993
      (by native_decide) (by native_decide)
  have hout : (segment_000000_pm_final pmStore) 2993 = bw_sum ((segment_000000_pm_final pmStore) 9) ((segment_000000_pm_final pmStore) 993) := by
    calc
      _ = bw_sum (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SumWitness.pmGraph) pmStore 9) (((segment_000000_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful SumWitness.pmGraph) pmStore 993) := hout_prefix
      _ = bw_sum ((segment_000000_pm_final pmStore) 9) ((segment_000000_pm_final pmStore) 993) := by rw [hout_read_0, hout_read_1]
  exact hout

private theorem segment_000000_sound (smStore pmStore : Store)
    (hstate : state_before.Holds smStore pmStore) :
    state_after.Holds (segment_000000_sm_final smStore) (segment_000000_pm_final pmStore) := by
  let smFinal := segment_000000_sm_final smStore
  let pmFinal := segment_000000_pm_final pmStore
  have hframe : state_before.Holds smFinal pmFinal := by
    unfold smFinal pmFinal segment_000000_sm_final segment_000000_pm_final
    apply RelationState.Holds.fold_frame segment_000000_sm_nodes segment_000000_pm_nodes smStore pmStore hstate
    · native_decide
    · native_decide
    · native_decide
    · native_decide
  have hx : fact_x.Holds smFinal pmFinal := hframe _ (by native_decide)
  have hg : fact_g.Holds smFinal pmFinal := hframe _ (by native_decide)
  change ShardedRel (smFinal 10) [pmFinal 1000, pmFinal 993] 1 [2, 6, 5] [2, 3, 5] at hx
  change ReductionRel (smFinal 9) [pmFinal 9] [1] at hg
  have hxValue : smFinal 10 = allGatherPrimDimN 1 2 0 [pmFinal 1000, pmFinal 993] := by
    simpa only [List.length_cons, List.length_nil] using hx.full_value
  have hgValue : smFinal 9 = pmFinal 9 := ReductionRel.singleton_value hg
  have hSumSm := segment_000000_sumSm smStore
  change smFinal 20 = fw_sum (smFinal 10) at hSumSm
  have hBwSm := segment_000000_bwSm smStore
  change smFinal 30 = bw_sum (smFinal 9) (smFinal 10) at hBwSm
  have hSumPm0 := segment_000000_sumPm0 pmStore
  change pmFinal 2000 = fw_sum (pmFinal 1000) at hSumPm0
  have hBwPm0 := segment_000000_bwPm0 pmStore
  change pmFinal 3000 = bw_sum (pmFinal 9) (pmFinal 1000) at hBwPm0
  have hXShape0 := hx.shard_shapes (pmFinal 1000) (by simp)
  have hSumPm1 := segment_000000_sumPm1 pmStore
  change pmFinal 1993 = fw_sum (pmFinal 993) at hSumPm1
  have hBwPm1 := segment_000000_bwPm1 pmStore
  change pmFinal 2993 = bw_sum (pmFinal 9) (pmFinal 993) at hBwPm1
  have hXShape1 := hx.shard_shapes (pmFinal 993) (by simp)
  have hSumComm := TrainVerify.Denote.fw_sum_allGatherPrimDimN_eq_allReducePrim_fw_sum 1 2 [pmFinal 1000, pmFinal 993] rfl (by simp) [2, 3, 5]
    (by simpa using hXShape0) hx.shard_shapes hx.gather_dim_lt (by native_decide) (by native_decide)
  have hSumValue : smFinal 20 = allReducePrim [pmFinal 2000, pmFinal 1993].length 0 [pmFinal 2000, pmFinal 1993] := by
    rw [hSumSm, hxValue, hSumComm]
    simp only [List.map, List.length_cons, List.length_nil]
    rw [← hSumPm0, ← hSumPm1]
  have hSumOut : fact_sum.Holds smFinal pmFinal := by
    change ReductionRel (smFinal 20) [pmFinal 2000, pmFinal 1993] [1]
    refine { full_value := hSumValue, full_shape := ?_, contributions_nonempty := by simp, contribution_shapes := ?_, reduced_shape := ?_ }
    · rw [hSumSm]
      exact fw_sum_shape _
    · intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with h0 | h1
      · subst t
        rw [hSumPm0]
        exact fw_sum_shape _
      · subst t
        rw [hSumPm1]
        exact fw_sum_shape _
    · rw [← hSumValue]
      rw [hSumSm]
      exact fw_sum_shape _
  have hBwComm : bw_sum (smFinal 9)
      (allGatherPrimDimN 1 2 0 [pmFinal 1000, pmFinal 993]) =
      allGatherPrimDimN 1 2 0 [bw_sum (smFinal 9) (pmFinal 1000), bw_sum (smFinal 9) (pmFinal 993)] := by
    simpa only [List.length_cons, List.length_nil, List.map] using
      (TrainVerify.Denote.bw_sum_allGatherPrimDimN_dim1_rank3
        (smFinal 9) [pmFinal 1000, pmFinal 993] 2 3 5
        hx.shards_nonempty (by decide) (by decide) (by decide) hx.shard_shapes)
  have hBwOut : fact_bw.Holds smFinal pmFinal := by
    change ShardedRel (smFinal 30) [pmFinal 3000, pmFinal 2993] 1 [2, 6, 5] [2, 3, 5]
    constructor
    · change smFinal 30 = allGatherPrimDimN 1 2 0 [pmFinal 3000, pmFinal 2993]
      rw [hBwSm, hxValue, hBwComm, hgValue]
      rw [← hBwPm0, ← hBwPm1]
    · rw [hBwSm, bw_sum_shape, hx.full_shape]
    · simp
    · exact hx.gather_dim_lt
    · intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with h0 | h1
      · subst t
        rw [hBwPm0, bw_sum_shape, hXShape0]
      · subst t
        rw [hBwPm1, bw_sum_shape, hXShape1]
    · exact hx.shape_contract
  intro fact hfact
  have covered : fact ∈ [fact_sum, fact_bw] ++ state_before.facts := by
    exact (show state_after.facts ⊆ [fact_sum, fact_bw] ++ state_before.facts by native_decide) hfact
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at covered
  rcases covered with fresh | old
  · rcases fresh with rfl | rfl
    · exact hSumOut
    · exact hBwOut
  · exact hframe fact old

private def segment_000000 : ClosedDepSegmentCertificate SumWitness.smGraph SumWitness.pmGraph state_before state_after where
  smNodes := segment_000000_sm_nodes
  pmNodes := segment_000000_pm_nodes
  sound := by
    intro smStore pmStore hstate
    simpa only [segment_000000_sm_final, segment_000000_pm_final] using segment_000000_sound smStore pmStore hstate

#print axioms segment_000000
end
end SumWitness
