import denote.RelationCompiler
import denote.KRankLinearGather

namespace TrainVerify.Denote
open RelationCompiler
namespace SyntheticMixedLinear
noncomputable section
set_option maxHeartbeats 1000000

def gSM : GraphDecl := { numRanks := 1, nodes := [] }
def gPM : GraphDecl := { numRanks := 3, nodes := [] }
def fact_input_a : RelationFact := .sharded 100 [200,201,202] 1 [2,9,5] [2,3,5]
def fact_input_b : RelationFact := .sharded 110 [210,211,212] 1 [2,9,5] [2,3,5]
def fact_gather_in : RelationFact := .sharded 120 [220,221,222] 1 [2,9,5] [2,3,5]
def fact_weight : RelationFact := .sharded 132 [232,233,234] 0 [12,5] [4,5]
def eq_a : RelationFact := .tensorEq .sm 130 .pm 130
def shape_a : RelationFact := .tensorShape .pm 130 [5,5]
def eq_b : RelationFact := .tensorEq .sm 131 .pm 131
def shape_b : RelationFact := .tensorShape .pm 131 [5,5]
def fact_out_a : RelationFact := .sharded 140 [240,241,242] 1 [2,9,5] [2,3,5]
def fact_out_b : RelationFact := .sharded 141 [250,251,252] 1 [2,9,5] [2,3,5]
def fact_joined : RelationFact := .joined 120 260 [2,9,5]
def fact_final : RelationFact := .sharded 142 [270,271,272] 2 [2,9,12] [2,9,4]
def state_pre : RelationState where
  facts := [fact_input_a,fact_input_b,fact_gather_in,fact_weight,eq_a,shape_a,eq_b,shape_b]
  nonempty := by decide
def state_post : RelationState where
  facts := [fact_out_a,fact_out_b,fact_joined,fact_final]
  nonempty := by decide
private def segment_000059_sm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [100, 130], outs := [140] }, { rank := 0, op := "OpName.FW_linear", ins := [120, 132], outs := [142] }, { rank := 0, op := "OpName.FW_linear", ins := [110, 131], outs := [141] }]
private def segment_000059_pm_nodes : List NodeDecl := [{ rank := 0, op := "OpName.FW_linear", ins := [200, 130], outs := [240] }, { rank := 0, op := "OpName.FW_linear", ins := [210, 131], outs := [250] }, { rank := 1, op := "OpName.FW_linear", ins := [201, 130], outs := [241] }, { rank := 1, op := "OpName.FW_linear", ins := [211, 131], outs := [251] }, { rank := 2, op := "OpName.FW_linear", ins := [202, 130], outs := [242] }, { rank := 0, op := "OpName.AllGatherPrim", ins := [220, 221, 222], outs := [260], params := [1] }, { rank := 2, op := "OpName.FW_linear", ins := [212, 131], outs := [252] }, { rank := 0, op := "OpName.FW_linear", ins := [260, 232], outs := [270] }, { rank := 1, op := "OpName.FW_linear", ins := [260, 233], outs := [271] }, { rank := 2, op := "OpName.FW_linear", ins := [260, 234], outs := [272] }]

private def segment_000059 :
    ClosedDepSegmentCertificate SyntheticMixedLinear.gSM SyntheticMixedLinear.gPM state_pre state_post where
  smNodes := segment_000059_sm_nodes
  pmNodes := segment_000059_pm_nodes
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := segment_000059_sm_nodes
    let pmNodes : List NodeDecl := segment_000059_pm_nodes
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gSM) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gPM) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hLocalIn0 : fact_input_a.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 100) [pmStore 200, pmStore 201, pmStore 202] 1 [2, 9, 5] [2, 3, 5] at hLocalIn0
    have hLocalEq0 : eq_a.Holds smStore pmStore := hstate _ (by native_decide)
    change smStore 130 = pmStore 130 at hLocalEq0
    have hLocalShape0 : shape_a.Holds smStore pmStore := hstate _ (by native_decide)
    change (pmStore 130).shape = [5, 5] at hLocalShape0
    have hLocalIn1 : fact_input_b.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 110) [pmStore 210, pmStore 211, pmStore 212] 1 [2, 9, 5] [2, 3, 5] at hLocalIn1
    have hLocalEq1 : eq_b.Holds smStore pmStore := hstate _ (by native_decide)
    change smStore 131 = pmStore 131 at hLocalEq1
    have hLocalShape1 : shape_b.Holds smStore pmStore := hstate _ (by native_decide)
    change (pmStore 131).shape = [5, 5] at hLocalShape1
    have hGatherIn : fact_gather_in.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 120) [pmStore 220, pmStore 221, pmStore 222] 1 [2, 9, 5] [2, 3, 5] at hGatherIn
    have hWeight : fact_weight.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 132) [pmStore 232, pmStore 233, pmStore 234] 0 [12, 5] [4, 5] at hWeight
    have hLocal0Sm : smFinal 140 = fw_linear (smStore 100) (smStore 130) := by
      change (smNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gSM) smStore) 140 = _
      rw [show smNodes = smNodes.take 0 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [100, 130], outs := [140] }] ++ smNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticMixedLinear.gSM smStore (smNodes.take 0) (smNodes.drop 1)
        { rank := 0, op := "OpName.FW_linear", ins := [100, 130], outs := [140] } 140 (fun t => fw_linear (t 100) (t 130)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out SyntheticMixedLinear.gSM t 0 100 130 140
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gSM (smNodes.take 0) smStore 100 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gSM (smNodes.take 0) smStore 130 (by native_decide) (by native_decide)]
    have hLocal0Pm0 : pmFinal 240 = fw_linear (pmStore 200) (pmStore 130) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gPM) pmStore) 240 = _
      rw [show pmNodes = pmNodes.take 0 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [200, 130], outs := [240] }] ++ pmNodes.drop 1 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticMixedLinear.gPM pmStore (pmNodes.take 0) (pmNodes.drop 1)
        { rank := 0, op := "OpName.FW_linear", ins := [200, 130], outs := [240] } 240 (fun t => fw_linear (t 200) (t 130)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out SyntheticMixedLinear.gPM t 0 200 130 240
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gPM (pmNodes.take 0) pmStore 200 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gPM (pmNodes.take 0) pmStore 130 (by native_decide) (by native_decide)]
    have hLocal0Pm1 : pmFinal 241 = fw_linear (pmStore 201) (pmStore 130) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gPM) pmStore) 241 = _
      rw [show pmNodes = pmNodes.take 2 ++ [{ rank := 1, op := "OpName.FW_linear", ins := [201, 130], outs := [241] }] ++ pmNodes.drop 3 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticMixedLinear.gPM pmStore (pmNodes.take 2) (pmNodes.drop 3)
        { rank := 1, op := "OpName.FW_linear", ins := [201, 130], outs := [241] } 241 (fun t => fw_linear (t 201) (t 130)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out SyntheticMixedLinear.gPM t 1 201 130 241
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gPM (pmNodes.take 2) pmStore 201 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gPM (pmNodes.take 2) pmStore 130 (by native_decide) (by native_decide)]
    have hLocal0Pm2 : pmFinal 242 = fw_linear (pmStore 202) (pmStore 130) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gPM) pmStore) 242 = _
      rw [show pmNodes = pmNodes.take 4 ++ [{ rank := 2, op := "OpName.FW_linear", ins := [202, 130], outs := [242] }] ++ pmNodes.drop 5 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticMixedLinear.gPM pmStore (pmNodes.take 4) (pmNodes.drop 5)
        { rank := 2, op := "OpName.FW_linear", ins := [202, 130], outs := [242] } 242 (fun t => fw_linear (t 202) (t 130)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out SyntheticMixedLinear.gPM t 2 202 130 242
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gPM (pmNodes.take 4) pmStore 202 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gPM (pmNodes.take 4) pmStore 130 (by native_decide) (by native_decide)]
    have hLocal1Sm : smFinal 141 = fw_linear (smStore 110) (smStore 131) := by
      change (smNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gSM) smStore) 141 = _
      rw [show smNodes = smNodes.take 2 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [110, 131], outs := [141] }] ++ smNodes.drop 3 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticMixedLinear.gSM smStore (smNodes.take 2) (smNodes.drop 3)
        { rank := 0, op := "OpName.FW_linear", ins := [110, 131], outs := [141] } 141 (fun t => fw_linear (t 110) (t 131)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out SyntheticMixedLinear.gSM t 0 110 131 141
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gSM (smNodes.take 2) smStore 110 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gSM (smNodes.take 2) smStore 131 (by native_decide) (by native_decide)]
    have hLocal1Pm0 : pmFinal 250 = fw_linear (pmStore 210) (pmStore 131) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gPM) pmStore) 250 = _
      rw [show pmNodes = pmNodes.take 1 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [210, 131], outs := [250] }] ++ pmNodes.drop 2 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticMixedLinear.gPM pmStore (pmNodes.take 1) (pmNodes.drop 2)
        { rank := 0, op := "OpName.FW_linear", ins := [210, 131], outs := [250] } 250 (fun t => fw_linear (t 210) (t 131)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out SyntheticMixedLinear.gPM t 0 210 131 250
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gPM (pmNodes.take 1) pmStore 210 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gPM (pmNodes.take 1) pmStore 131 (by native_decide) (by native_decide)]
    have hLocal1Pm1 : pmFinal 251 = fw_linear (pmStore 211) (pmStore 131) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gPM) pmStore) 251 = _
      rw [show pmNodes = pmNodes.take 3 ++ [{ rank := 1, op := "OpName.FW_linear", ins := [211, 131], outs := [251] }] ++ pmNodes.drop 4 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticMixedLinear.gPM pmStore (pmNodes.take 3) (pmNodes.drop 4)
        { rank := 1, op := "OpName.FW_linear", ins := [211, 131], outs := [251] } 251 (fun t => fw_linear (t 211) (t 131)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out SyntheticMixedLinear.gPM t 1 211 131 251
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gPM (pmNodes.take 3) pmStore 211 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gPM (pmNodes.take 3) pmStore 131 (by native_decide) (by native_decide)]
    have hLocal1Pm2 : pmFinal 252 = fw_linear (pmStore 212) (pmStore 131) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gPM) pmStore) 252 = _
      rw [show pmNodes = pmNodes.take 6 ++ [{ rank := 2, op := "OpName.FW_linear", ins := [212, 131], outs := [252] }] ++ pmNodes.drop 7 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticMixedLinear.gPM pmStore (pmNodes.take 6) (pmNodes.drop 7)
        { rank := 2, op := "OpName.FW_linear", ins := [212, 131], outs := [252] } 252 (fun t => fw_linear (t 212) (t 131)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out SyntheticMixedLinear.gPM t 2 212 131 252
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gPM (pmNodes.take 6) pmStore 212 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gPM (pmNodes.take 6) pmStore 131 (by native_decide) (by native_decide)]
    have hGatherWriter : pmFinal 260 = allGatherPrimDimN 1 3 0 [pmStore 220, pmStore 221, pmStore 222] := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gPM) pmStore) 260 = _
      rw [show pmNodes = pmNodes.take 5 ++ [{ rank := 0, op := "OpName.AllGatherPrim", ins := [220, 221, 222], outs := [260], params := [1] }] ++ pmNodes.drop 6 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticMixedLinear.gPM pmStore (pmNodes.take 5) (pmNodes.drop 6)
        { rank := 0, op := "OpName.AllGatherPrim", ins := [220, 221, 222], outs := [260], params := [1] } 260 (fun t => allGatherPrimDimN 1 3 0 [t 220, t 221, t 222]) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_allGatherPrimDimN_out SyntheticMixedLinear.gPM t 0 [220, 221, 222] 260 1
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gPM (pmNodes.take 5) pmStore 220 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gPM (pmNodes.take 5) pmStore 221 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gPM (pmNodes.take 5) pmStore 222 (by native_decide) (by native_decide)]
    have hOutputSm : smFinal 142 = fw_linear (smStore 120) (smStore 132) := by
      change (smNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gSM) smStore) 142 = _
      rw [show smNodes = smNodes.take 1 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [120, 132], outs := [142] }] ++ smNodes.drop 2 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticMixedLinear.gSM smStore (smNodes.take 1) (smNodes.drop 2)
        { rank := 0, op := "OpName.FW_linear", ins := [120, 132], outs := [142] } 142 (fun t => fw_linear (t 120) (t 132)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out SyntheticMixedLinear.gSM t 0 120 132 142
        ) (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gSM (smNodes.take 1) smStore 120 (by native_decide) (by native_decide)]
      rw [foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gSM (smNodes.take 1) smStore 132 (by native_decide) (by native_decide)]
    have hOutputPmRaw0 : pmFinal 270 = fw_linear (((pmNodes.take 7).foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gPM) pmStore) 260) (pmStore 232) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gPM) pmStore) 270 = _
      rw [show pmNodes = pmNodes.take 7 ++ [{ rank := 0, op := "OpName.FW_linear", ins := [260, 232], outs := [270] }] ++ pmNodes.drop 8 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticMixedLinear.gPM pmStore (pmNodes.take 7) (pmNodes.drop 8)
        { rank := 0, op := "OpName.FW_linear", ins := [260, 232], outs := [270] } 270 (fun t => fw_linear (t 260) (t 232)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out SyntheticMixedLinear.gPM t 0 260 232 270
        ) (by native_decide) (by native_decide)]
      congr 2
    have hJoinedPrefix0 : ((pmNodes.take 7).foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gPM) pmStore) 260 = pmFinal 260 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gPM (pmNodes.drop 7) ((pmNodes.take 7).foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gPM) pmStore) 260 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 7 ++ pmNodes.drop 7 = pmNodes by exact List.take_append_drop 7 pmNodes] at h
      exact h.symm
    have hOutputPm0 : pmFinal 270 = fw_linear (pmFinal 260) (pmStore 232) := by
      rw [hOutputPmRaw0, hJoinedPrefix0]
    have hOutputPmRaw1 : pmFinal 271 = fw_linear (((pmNodes.take 8).foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gPM) pmStore) 260) (pmStore 233) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gPM) pmStore) 271 = _
      rw [show pmNodes = pmNodes.take 8 ++ [{ rank := 1, op := "OpName.FW_linear", ins := [260, 233], outs := [271] }] ++ pmNodes.drop 9 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticMixedLinear.gPM pmStore (pmNodes.take 8) (pmNodes.drop 9)
        { rank := 1, op := "OpName.FW_linear", ins := [260, 233], outs := [271] } 271 (fun t => fw_linear (t 260) (t 233)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out SyntheticMixedLinear.gPM t 1 260 233 271
        ) (by native_decide) (by native_decide)]
      congr 2
    have hJoinedPrefix1 : ((pmNodes.take 8).foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gPM) pmStore) 260 = pmFinal 260 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gPM (pmNodes.drop 8) ((pmNodes.take 8).foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gPM) pmStore) 260 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 8 ++ pmNodes.drop 8 = pmNodes by exact List.take_append_drop 8 pmNodes] at h
      exact h.symm
    have hOutputPm1 : pmFinal 271 = fw_linear (pmFinal 260) (pmStore 233) := by
      rw [hOutputPmRaw1, hJoinedPrefix1]
    have hOutputPmRaw2 : pmFinal 272 = fw_linear (((pmNodes.take 9).foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gPM) pmStore) 260) (pmStore 234) := by
      change (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gPM) pmStore) 272 = _
      rw [show pmNodes = pmNodes.take 9 ++ [{ rank := 2, op := "OpName.FW_linear", ins := [260, 234], outs := [272] }] ++ pmNodes.drop 10 by native_decide]
      rw [foldl_faithful_middle_writer SyntheticMixedLinear.gPM pmStore (pmNodes.take 9) (pmNodes.drop 10)
        { rank := 2, op := "OpName.FW_linear", ins := [260, 234], outs := [272] } 272 (fun t => fw_linear (t 260) (t 234)) (by
          intro t
          rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
            (hshuffle := by native_decide) (hunshuffle := by native_decide) (hattn := by native_decide)]
          simp [applyNodeDistributed, applyNodeRingAttn]
          exact applyNode_fw_linear_out SyntheticMixedLinear.gPM t 2 260 234 272
        ) (by native_decide) (by native_decide)]
      congr 2
    have hJoinedPrefix2 : ((pmNodes.take 9).foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gPM) pmStore) 260 = pmFinal 260 := by
      have h := foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gPM (pmNodes.drop 9) ((pmNodes.take 9).foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gPM) pmStore) 260 (by native_decide) (by native_decide)
      rw [← List.foldl_append, show pmNodes.take 9 ++ pmNodes.drop 9 = pmNodes by exact List.take_append_drop 9 pmNodes] at h
      exact h.symm
    have hOutputPm2 : pmFinal 272 = fw_linear (pmFinal 260) (pmStore 234) := by
      rw [hOutputPmRaw2, hJoinedPrefix2]
    have hLocalComm0 := (TrainVerify.Denote.fw_linear_3d_allGatherPrimDimN_dim1_comm (K := [pmStore 200, pmStore 201, pmStore 202].length) (b := 2) (s := 3) (i := 5) (o := 5) (xs := [pmStore 200, pmStore 201, pmStore 202]) (w := pmStore 130) (by simp) (by omega) (by omega) (by omega) (by omega) rfl (fun x hx => hLocalIn0.shard_shapes x hx) hLocalShape0)
    have hLocalValue0 : smFinal 140 = allGatherPrimDimN 1 [pmFinal 240, pmFinal 241, pmFinal 242].length 0 [pmFinal 240, pmFinal 241, pmFinal 242] := by
      rw [hLocal0Sm, hLocalEq0, hLocalIn0.full_value, hLocalComm0]
      simp only [List.map, List.length_cons, List.length_nil]
      rw [← hLocal0Pm0, ← hLocal0Pm1, ← hLocal0Pm2]
    have hLocalShapeOut0_0 : (pmFinal 240).shape = [2, 3, 5] := by
      rw [hLocal0Pm0]
      exact fw_linear_3d_shape 2 3 5 5 _ _ (hLocalIn0.shard_shapes _ (by simp)) hLocalShape0
    have hLocalShapeOut0_1 : (pmFinal 241).shape = [2, 3, 5] := by
      rw [hLocal0Pm1]
      exact fw_linear_3d_shape 2 3 5 5 _ _ (hLocalIn0.shard_shapes _ (by simp)) hLocalShape0
    have hLocalShapeOut0_2 : (pmFinal 242).shape = [2, 3, 5] := by
      rw [hLocal0Pm2]
      exact fw_linear_3d_shape 2 3 5 5 _ _ (hLocalIn0.shard_shapes _ (by simp)) hLocalShape0
    have hLocalOut0 : fact_out_a.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 140) [pmFinal 240, pmFinal 241, pmFinal 242] 1 [2, 9, 5] [2, 3, 5]
      refine { full_value := hLocalValue0, full_shape := ?_, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil] <;> native_decide }
      · rw [hLocalValue0, allGatherPrimDimN_shape 1 [pmFinal 240, pmFinal 241, pmFinal 242].length [pmFinal 240, pmFinal 241, pmFinal 242] [2, 3, 5]]
        · simp only [List.length_cons, List.length_nil]
          native_decide
        · simp only [List.head?, Option.map, Option.getD]; exact hLocalShapeOut0_0
      · intro shard hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact hLocalShapeOut0_0
        · exact hLocalShapeOut0_1
        · exact hLocalShapeOut0_2
    have hLocalComm1 := (TrainVerify.Denote.fw_linear_3d_allGatherPrimDimN_dim1_comm (K := [pmStore 210, pmStore 211, pmStore 212].length) (b := 2) (s := 3) (i := 5) (o := 5) (xs := [pmStore 210, pmStore 211, pmStore 212]) (w := pmStore 131) (by simp) (by omega) (by omega) (by omega) (by omega) rfl (fun x hx => hLocalIn1.shard_shapes x hx) hLocalShape1)
    have hLocalValue1 : smFinal 141 = allGatherPrimDimN 1 [pmFinal 250, pmFinal 251, pmFinal 252].length 0 [pmFinal 250, pmFinal 251, pmFinal 252] := by
      rw [hLocal1Sm, hLocalEq1, hLocalIn1.full_value, hLocalComm1]
      simp only [List.map, List.length_cons, List.length_nil]
      rw [← hLocal1Pm0, ← hLocal1Pm1, ← hLocal1Pm2]
    have hLocalShapeOut1_0 : (pmFinal 250).shape = [2, 3, 5] := by
      rw [hLocal1Pm0]
      exact fw_linear_3d_shape 2 3 5 5 _ _ (hLocalIn1.shard_shapes _ (by simp)) hLocalShape1
    have hLocalShapeOut1_1 : (pmFinal 251).shape = [2, 3, 5] := by
      rw [hLocal1Pm1]
      exact fw_linear_3d_shape 2 3 5 5 _ _ (hLocalIn1.shard_shapes _ (by simp)) hLocalShape1
    have hLocalShapeOut1_2 : (pmFinal 252).shape = [2, 3, 5] := by
      rw [hLocal1Pm2]
      exact fw_linear_3d_shape 2 3 5 5 _ _ (hLocalIn1.shard_shapes _ (by simp)) hLocalShape1
    have hLocalOut1 : fact_out_b.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 141) [pmFinal 250, pmFinal 251, pmFinal 252] 1 [2, 9, 5] [2, 3, 5]
      refine { full_value := hLocalValue1, full_shape := ?_, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil] <;> native_decide }
      · rw [hLocalValue1, allGatherPrimDimN_shape 1 [pmFinal 250, pmFinal 251, pmFinal 252].length [pmFinal 250, pmFinal 251, pmFinal 252] [2, 3, 5]]
        · simp only [List.length_cons, List.length_nil]
          native_decide
        · simp only [List.head?, Option.map, Option.getD]; exact hLocalShapeOut1_0
      · intro shard hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact hLocalShapeOut1_0
        · exact hLocalShapeOut1_1
        · exact hLocalShapeOut1_2
    have hGatherFinal : fact_gather_in.Holds smFinal pmFinal := hframe _ (by native_decide)
    change ShardedRel (smFinal 120) [pmFinal 220, pmFinal 221, pmFinal 222] 1 [2, 9, 5] [2, 3, 5] at hGatherFinal
    have hGatherInputsFinal : [pmFinal 220, pmFinal 221, pmFinal 222] = [pmStore 220, pmStore 221, pmStore 222] := by
      have h220 := foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gPM pmNodes pmStore 220 (by native_decide) (by native_decide)
      have h221 := foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gPM pmNodes pmStore 221 (by native_decide) (by native_decide)
      have h222 := foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gPM pmNodes pmStore 222 (by native_decide) (by native_decide)
      change [(pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gPM) pmStore) 220, (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gPM) pmStore) 221, (pmNodes.foldl (applyNodeDistributedFaithful SyntheticMixedLinear.gPM) pmStore) 222] = [pmStore 220, pmStore 221, pmStore 222]
      rw [h220, h221, h222]
    have hJoinedValue : smFinal 120 = pmFinal 260 := by
      rw [TrainVerify.Denote.RelationCompiler.ShardedRel.to_joined_allGather hGatherFinal, hGatherInputsFinal]
      simp only [List.length_cons, List.length_nil]
      exact hGatherWriter.symm
    have hJoinedOut : fact_joined.Holds smFinal pmFinal := by
      change smFinal 120 = pmFinal 260 ∧ (smFinal 120).shape = [2, 9, 5] ∧ (pmFinal 260).shape = [2, 9, 5]
      refine ⟨hJoinedValue, hGatherFinal.full_shape, ?_⟩
      rw [← hJoinedValue]
      exact hGatherFinal.full_shape
    have hOutputComm := (TrainVerify.Denote.fw_linear_3d_weight_allGatherPrimDimN_dim0_comm (K := [pmStore 232, pmStore 233, pmStore 234].length) (b := 2) (s := 9) (i := 5) (o := 4) (x := pmFinal 260) (ws := [pmStore 232, pmStore 233, pmStore 234]) (by simp) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by simp) (by rw [← hJoinedValue]; exact hGatherFinal.full_shape) (fun w hw => hWeight.shard_shapes w hw))
    have hOutputValue : smFinal 142 = allGatherPrimDimN 2 [pmFinal 270, pmFinal 271, pmFinal 272].length 0 [pmFinal 270, pmFinal 271, pmFinal 272] := by
      rw [hOutputSm]
      have hSmAct : smStore 120 = pmFinal 260 := by
        have h := foldl_applyNodeDistributedFaithful_at_not_written SyntheticMixedLinear.gSM smNodes smStore 120 (by native_decide) (by native_decide)
        rw [← h]
        exact hJoinedValue
      rw [hSmAct, hWeight.full_value, hOutputComm]
      simp only [List.map, List.length_cons, List.length_nil]
      rw [← hOutputPm0, ← hOutputPm1, ← hOutputPm2]
    have hOutputShape0 : (pmFinal 270).shape = [2, 9, 4] := by
      rw [hOutputPm0]
      exact fw_linear_3d_shape 2 9 5 4 _ _ (by rw [← hJoinedValue]; exact hGatherFinal.full_shape) (hWeight.shard_shapes _ (by simp))
    have hOutputShape1 : (pmFinal 271).shape = [2, 9, 4] := by
      rw [hOutputPm1]
      exact fw_linear_3d_shape 2 9 5 4 _ _ (by rw [← hJoinedValue]; exact hGatherFinal.full_shape) (hWeight.shard_shapes _ (by simp))
    have hOutputShape2 : (pmFinal 272).shape = [2, 9, 4] := by
      rw [hOutputPm2]
      exact fw_linear_3d_shape 2 9 5 4 _ _ (by rw [← hJoinedValue]; exact hGatherFinal.full_shape) (hWeight.shard_shapes _ (by simp))
    have hFinalOut : fact_final.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 142) [pmFinal 270, pmFinal 271, pmFinal 272] 2 [2, 9, 12] [2, 9, 4]
      refine { full_value := hOutputValue, full_shape := ?_, shards_nonempty := by simp, gather_dim_lt := by native_decide, shard_shapes := ?_, shape_contract := by simp only [List.length_cons, List.length_nil] <;> native_decide }
      · rw [hOutputValue, allGatherPrimDimN_shape 2 [pmFinal 270, pmFinal 271, pmFinal 272].length [pmFinal 270, pmFinal 271, pmFinal 272] [2, 9, 4]]
        · simp only [List.length_cons, List.length_nil]
          native_decide
        · simp only [List.head?, Option.map, Option.getD]; exact hOutputShape0
      · intro shard hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with rfl | rfl | rfl
        · exact hOutputShape0
        · exact hOutputShape1
        · exact hOutputShape2
    intro fact hfact
    have covered : fact ∈ [fact_out_a, fact_out_b, fact_joined, fact_final] ++ state_pre.facts := by
      exact (show state_post.facts ⊆ [fact_out_a, fact_out_b, fact_joined, fact_final] ++ state_pre.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl | rfl | rfl | rfl
      · exact hLocalOut0
      · exact hLocalOut1
      · exact hJoinedOut
      · exact hFinalOut
    · exact hframe fact old

#print axioms segment_000059
end
end SyntheticMixedLinear
end TrainVerify.Denote
