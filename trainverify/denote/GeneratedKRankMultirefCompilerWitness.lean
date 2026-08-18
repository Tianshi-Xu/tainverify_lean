/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.SyntheticMultiref2

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_input : RelationFact :=
  .sharded 100 [200, 201, 202, 203] 1 [1, 8, 3] [1, 2, 3]

private def fact_output_0 : RelationFact :=
  .sharded 110 [300, 310, 320, 330] 1 [1, 8, 3] [1, 2, 3]

private def fact_output_1 : RelationFact :=
  .sharded 111 [301, 311, 321, 331] 1 [1, 8, 3] [1, 2, 3]

private def anchor : RelationFact :=
  .tensorShape .sm 999 [1]

private def state_pre : RelationState where
  facts := [anchor, fact_input]
  nonempty := by decide

private def state_post : RelationState where
  facts := [anchor, fact_output_0, fact_output_1]
  nonempty := by decide

end
end TrainVerify.Denote.SyntheticMultiref2

namespace TrainVerify.Denote.SyntheticMultiref2
noncomputable section
private def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_identity", ins := [400], outs := [500] }, { rank := 0, op := "OpName.FW_identity", ins := [401], outs := [501] }, { rank := 0, op := "OpName.FW_identity", ins := [402], outs := [502] }, { rank := 0, op := "OpName.FW_multiref", ins := [100], outs := [110, 111], params := [2] }] }
private def pmGraph : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.FW_identity", ins := [600], outs := [700] }, { rank := 1, op := "OpName.FW_identity", ins := [601], outs := [701] }, { rank := 2, op := "OpName.FW_identity", ins := [602], outs := [702] }, { rank := 3, op := "OpName.FW_identity", ins := [603], outs := [703] }, { rank := 0, op := "OpName.FW_identity", ins := [604], outs := [704] }, { rank := 1, op := "OpName.FW_identity", ins := [605], outs := [705] }, { rank := 2, op := "OpName.FW_identity", ins := [606], outs := [706] }, { rank := 3, op := "OpName.FW_identity", ins := [607], outs := [707] }, { rank := 0, op := "OpName.FW_identity", ins := [608], outs := [708] }, { rank := 1, op := "OpName.FW_identity", ins := [609], outs := [709] }, { rank := 2, op := "OpName.FW_identity", ins := [610], outs := [710] }, { rank := 3, op := "OpName.FW_identity", ins := [611], outs := [711] }, { rank := 0, op := "OpName.FW_identity", ins := [612], outs := [712] }, { rank := 1, op := "OpName.FW_identity", ins := [613], outs := [713] }, { rank := 2, op := "OpName.FW_identity", ins := [614], outs := [714] }, { rank := 3, op := "OpName.FW_identity", ins := [615], outs := [715] }, { rank := 0, op := "OpName.FW_identity", ins := [616], outs := [716] }, { rank := 1, op := "OpName.FW_identity", ins := [617], outs := [717] }, { rank := 2, op := "OpName.FW_identity", ins := [618], outs := [718] }, { rank := 3, op := "OpName.FW_identity", ins := [619], outs := [719] }, { rank := 0, op := "OpName.FW_identity", ins := [620], outs := [720] }, { rank := 0, op := "OpName.FW_multiref", ins := [200], outs := [300, 301], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [201], outs := [310, 311], params := [2] }, { rank := 2, op := "OpName.FW_multiref", ins := [202], outs := [320, 321], params := [2] }, { rank := 3, op := "OpName.FW_multiref", ins := [203], outs := [330, 331], params := [2] }] }
private def segment_000005_sm_node : NodeDecl := { rank := 0, op := "OpName.FW_multiref", ins := [100], outs := [110, 111], params := [2] }
private def segment_000005_pm_node_0 : NodeDecl := { rank := 0, op := "OpName.FW_multiref", ins := [200], outs := [300, 301], params := [2] }
private def segment_000005_pm_node_1 : NodeDecl := { rank := 1, op := "OpName.FW_multiref", ins := [201], outs := [310, 311], params := [2] }
private def segment_000005_pm_node_2 : NodeDecl := { rank := 2, op := "OpName.FW_multiref", ins := [202], outs := [320, 321], params := [2] }
private def segment_000005_pm_node_3 : NodeDecl := { rank := 3, op := "OpName.FW_multiref", ins := [203], outs := [330, 331], params := [2] }
private def segment_000005_sm_nodes : List NodeDecl := [segment_000005_sm_node]
private def segment_000005_pm_nodes : List NodeDecl := [segment_000005_pm_node_0, segment_000005_pm_node_1, segment_000005_pm_node_2, segment_000005_pm_node_3]

private def segment_000005 :
    ClosedDepSegmentCertificate SyntheticMultiref2.smGraph SyntheticMultiref2.pmGraph state_pre state_post where
  smNodes := segment_000005_sm_nodes
  pmNodes := segment_000005_pm_nodes
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := segment_000005_sm_nodes
    let pmNodes : List NodeDecl := segment_000005_pm_nodes
    let pmTids : List Tid := [200, 201, 202, 203]
    let rankCount := pmTids.length
    have hRankCount : rankCount = SyntheticMultiref2.pmGraph.numRanks := by native_decide
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticMultiref2.smGraph) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticMultiref2.pmGraph) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hin : fact_input.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 100) (pmTids.map pmStore) 1 [1, 8, 3] [1, 2, 3] at hin
    have hSm_o0 : smFinal 110 = smStore 100 := by
      simpa [smFinal, smNodes, segment_000005_sm_nodes, segment_000005_sm_node] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref2.smGraph smStore [] []
          0 100 [110, 111] 2 110
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hPm0_o0 : pmFinal 300 = pmStore 200 := by
      simpa [pmFinal, pmNodes, segment_000005_pm_nodes, segment_000005_pm_node_0, segment_000005_pm_node_1, segment_000005_pm_node_2, segment_000005_pm_node_3] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref2.pmGraph pmStore
          []
          [{ rank := 1, op := "OpName.FW_multiref", ins := [201], outs := [310, 311], params := [2] }, { rank := 2, op := "OpName.FW_multiref", ins := [202], outs := [320, 321], params := [2] }, { rank := 3, op := "OpName.FW_multiref", ins := [203], outs := [330, 331], params := [2] }]
          0 200 [300, 301] 2 300
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hPm1_o0 : pmFinal 310 = pmStore 201 := by
      simpa [pmFinal, pmNodes, segment_000005_pm_nodes, segment_000005_pm_node_0, segment_000005_pm_node_1, segment_000005_pm_node_2, segment_000005_pm_node_3] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref2.pmGraph pmStore
          [{ rank := 0, op := "OpName.FW_multiref", ins := [200], outs := [300, 301], params := [2] }]
          [{ rank := 2, op := "OpName.FW_multiref", ins := [202], outs := [320, 321], params := [2] }, { rank := 3, op := "OpName.FW_multiref", ins := [203], outs := [330, 331], params := [2] }]
          1 201 [310, 311] 2 310
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hPm2_o0 : pmFinal 320 = pmStore 202 := by
      simpa [pmFinal, pmNodes, segment_000005_pm_nodes, segment_000005_pm_node_0, segment_000005_pm_node_1, segment_000005_pm_node_2, segment_000005_pm_node_3] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref2.pmGraph pmStore
          [{ rank := 0, op := "OpName.FW_multiref", ins := [200], outs := [300, 301], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [201], outs := [310, 311], params := [2] }]
          [{ rank := 3, op := "OpName.FW_multiref", ins := [203], outs := [330, 331], params := [2] }]
          2 202 [320, 321] 2 320
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hPm3_o0 : pmFinal 330 = pmStore 203 := by
      simpa [pmFinal, pmNodes, segment_000005_pm_nodes, segment_000005_pm_node_0, segment_000005_pm_node_1, segment_000005_pm_node_2, segment_000005_pm_node_3] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref2.pmGraph pmStore
          [{ rank := 0, op := "OpName.FW_multiref", ins := [200], outs := [300, 301], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [201], outs := [310, 311], params := [2] }, { rank := 2, op := "OpName.FW_multiref", ins := [202], outs := [320, 321], params := [2] }]
          []
          3 203 [330, 331] 2 330
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hout_o0 : fact_output_0.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 110) ([300, 310, 320, 330].map pmFinal) 1 [1, 8, 3] [1, 2, 3]
      simpa only [pmTids, List.map, hSm_o0, hPm0_o0, hPm1_o0, hPm2_o0, hPm3_o0] using hin
    have hSm_o1 : smFinal 111 = smStore 100 := by
      simpa [smFinal, smNodes, segment_000005_sm_nodes, segment_000005_sm_node] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref2.smGraph smStore [] []
          0 100 [110, 111] 2 111
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hPm0_o1 : pmFinal 301 = pmStore 200 := by
      simpa [pmFinal, pmNodes, segment_000005_pm_nodes, segment_000005_pm_node_0, segment_000005_pm_node_1, segment_000005_pm_node_2, segment_000005_pm_node_3] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref2.pmGraph pmStore
          []
          [{ rank := 1, op := "OpName.FW_multiref", ins := [201], outs := [310, 311], params := [2] }, { rank := 2, op := "OpName.FW_multiref", ins := [202], outs := [320, 321], params := [2] }, { rank := 3, op := "OpName.FW_multiref", ins := [203], outs := [330, 331], params := [2] }]
          0 200 [300, 301] 2 301
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hPm1_o1 : pmFinal 311 = pmStore 201 := by
      simpa [pmFinal, pmNodes, segment_000005_pm_nodes, segment_000005_pm_node_0, segment_000005_pm_node_1, segment_000005_pm_node_2, segment_000005_pm_node_3] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref2.pmGraph pmStore
          [{ rank := 0, op := "OpName.FW_multiref", ins := [200], outs := [300, 301], params := [2] }]
          [{ rank := 2, op := "OpName.FW_multiref", ins := [202], outs := [320, 321], params := [2] }, { rank := 3, op := "OpName.FW_multiref", ins := [203], outs := [330, 331], params := [2] }]
          1 201 [310, 311] 2 311
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hPm2_o1 : pmFinal 321 = pmStore 202 := by
      simpa [pmFinal, pmNodes, segment_000005_pm_nodes, segment_000005_pm_node_0, segment_000005_pm_node_1, segment_000005_pm_node_2, segment_000005_pm_node_3] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref2.pmGraph pmStore
          [{ rank := 0, op := "OpName.FW_multiref", ins := [200], outs := [300, 301], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [201], outs := [310, 311], params := [2] }]
          [{ rank := 3, op := "OpName.FW_multiref", ins := [203], outs := [330, 331], params := [2] }]
          2 202 [320, 321] 2 321
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hPm3_o1 : pmFinal 331 = pmStore 203 := by
      simpa [pmFinal, pmNodes, segment_000005_pm_nodes, segment_000005_pm_node_0, segment_000005_pm_node_1, segment_000005_pm_node_2, segment_000005_pm_node_3] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref2.pmGraph pmStore
          [{ rank := 0, op := "OpName.FW_multiref", ins := [200], outs := [300, 301], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [201], outs := [310, 311], params := [2] }, { rank := 2, op := "OpName.FW_multiref", ins := [202], outs := [320, 321], params := [2] }]
          []
          3 203 [330, 331] 2 331
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hout_o1 : fact_output_1.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 111) ([301, 311, 321, 331].map pmFinal) 1 [1, 8, 3] [1, 2, 3]
      simpa only [pmTids, List.map, hSm_o1, hPm0_o1, hPm1_o1, hPm2_o1, hPm3_o1] using hin
    intro fact hfact
    have covered : fact ∈ [fact_output_0, fact_output_1] ++ state_pre.facts := by
      exact (show state_post.facts ⊆ [fact_output_0, fact_output_1] ++ state_pre.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl | rfl
      · exact hout_o0
      · exact hout_o1
    · exact hframe fact old

#print axioms segment_000005
end
end TrainVerify.Denote.SyntheticMultiref2

namespace TrainVerify.Denote.SyntheticMultiref3

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_input : RelationFact :=
  .sharded 100 [200, 201, 202, 203] 1 [1, 8, 3] [1, 2, 3]

private def fact_output_0 : RelationFact :=
  .sharded 110 [300, 310, 320, 330] 1 [1, 8, 3] [1, 2, 3]

private def fact_output_1 : RelationFact :=
  .sharded 111 [301, 311, 321, 331] 1 [1, 8, 3] [1, 2, 3]

private def fact_output_2 : RelationFact :=
  .sharded 112 [302, 312, 322, 332] 1 [1, 8, 3] [1, 2, 3]

private def anchor : RelationFact :=
  .tensorShape .sm 999 [1]

private def state_pre : RelationState where
  facts := [anchor, fact_input]
  nonempty := by decide

private def state_post : RelationState where
  facts := [anchor, fact_output_0, fact_output_1, fact_output_2]
  nonempty := by decide

end
end TrainVerify.Denote.SyntheticMultiref3
namespace TrainVerify.Denote.SyntheticMultiref3
noncomputable section
private def smGraph : GraphDecl := { numRanks := 1, nodes := [{ rank := 0, op := "OpName.FW_identity", ins := [400], outs := [500] }, { rank := 0, op := "OpName.FW_identity", ins := [401], outs := [501] }, { rank := 0, op := "OpName.FW_identity", ins := [402], outs := [502] }, { rank := 0, op := "OpName.FW_multiref", ins := [100], outs := [110, 111, 112], params := [3] }] }
private def pmGraph : GraphDecl := { numRanks := 4, nodes := [{ rank := 0, op := "OpName.FW_identity", ins := [600], outs := [700] }, { rank := 1, op := "OpName.FW_identity", ins := [601], outs := [701] }, { rank := 2, op := "OpName.FW_identity", ins := [602], outs := [702] }, { rank := 3, op := "OpName.FW_identity", ins := [603], outs := [703] }, { rank := 0, op := "OpName.FW_identity", ins := [604], outs := [704] }, { rank := 1, op := "OpName.FW_identity", ins := [605], outs := [705] }, { rank := 2, op := "OpName.FW_identity", ins := [606], outs := [706] }, { rank := 3, op := "OpName.FW_identity", ins := [607], outs := [707] }, { rank := 0, op := "OpName.FW_identity", ins := [608], outs := [708] }, { rank := 1, op := "OpName.FW_identity", ins := [609], outs := [709] }, { rank := 2, op := "OpName.FW_identity", ins := [610], outs := [710] }, { rank := 3, op := "OpName.FW_identity", ins := [611], outs := [711] }, { rank := 0, op := "OpName.FW_identity", ins := [612], outs := [712] }, { rank := 1, op := "OpName.FW_identity", ins := [613], outs := [713] }, { rank := 2, op := "OpName.FW_identity", ins := [614], outs := [714] }, { rank := 3, op := "OpName.FW_identity", ins := [615], outs := [715] }, { rank := 0, op := "OpName.FW_identity", ins := [616], outs := [716] }, { rank := 1, op := "OpName.FW_identity", ins := [617], outs := [717] }, { rank := 2, op := "OpName.FW_identity", ins := [618], outs := [718] }, { rank := 3, op := "OpName.FW_identity", ins := [619], outs := [719] }, { rank := 0, op := "OpName.FW_identity", ins := [620], outs := [720] }, { rank := 0, op := "OpName.FW_multiref", ins := [200], outs := [300, 301, 302], params := [3] }, { rank := 1, op := "OpName.FW_multiref", ins := [201], outs := [310, 311, 312], params := [3] }, { rank := 2, op := "OpName.FW_multiref", ins := [202], outs := [320, 321, 322], params := [3] }, { rank := 3, op := "OpName.FW_multiref", ins := [203], outs := [330, 331, 332], params := [3] }] }
private def segment_000007_sm_node : NodeDecl := { rank := 0, op := "OpName.FW_multiref", ins := [100], outs := [110, 111, 112], params := [3] }
private def segment_000007_pm_node_0 : NodeDecl := { rank := 0, op := "OpName.FW_multiref", ins := [200], outs := [300, 301, 302], params := [3] }
private def segment_000007_pm_node_1 : NodeDecl := { rank := 1, op := "OpName.FW_multiref", ins := [201], outs := [310, 311, 312], params := [3] }
private def segment_000007_pm_node_2 : NodeDecl := { rank := 2, op := "OpName.FW_multiref", ins := [202], outs := [320, 321, 322], params := [3] }
private def segment_000007_pm_node_3 : NodeDecl := { rank := 3, op := "OpName.FW_multiref", ins := [203], outs := [330, 331, 332], params := [3] }
private def segment_000007_sm_nodes : List NodeDecl := [segment_000007_sm_node]
private def segment_000007_pm_nodes : List NodeDecl := [segment_000007_pm_node_0, segment_000007_pm_node_1, segment_000007_pm_node_2, segment_000007_pm_node_3]

private def segment_000007 :
    ClosedDepSegmentCertificate SyntheticMultiref3.smGraph SyntheticMultiref3.pmGraph state_pre state_post where
  smNodes := segment_000007_sm_nodes
  pmNodes := segment_000007_pm_nodes
  sound := by
    intro smStore pmStore hstate
    let smNodes : List NodeDecl := segment_000007_sm_nodes
    let pmNodes : List NodeDecl := segment_000007_pm_nodes
    let pmTids : List Tid := [200, 201, 202, 203]
    let rankCount := pmTids.length
    have hRankCount : rankCount = SyntheticMultiref3.pmGraph.numRanks := by native_decide
    let smFinal := smNodes.foldl (applyNodeDistributedFaithful SyntheticMultiref3.smGraph) smStore
    let pmFinal := pmNodes.foldl (applyNodeDistributedFaithful SyntheticMultiref3.pmGraph) pmStore
    have hframe : state_pre.Holds smFinal pmFinal := by
      apply RelationState.Holds.fold_frame smNodes pmNodes smStore pmStore hstate
      · native_decide
      · native_decide
      · native_decide
      · native_decide
    have hin : fact_input.Holds smStore pmStore := hstate _ (by native_decide)
    change ShardedRel (smStore 100) (pmTids.map pmStore) 1 [1, 8, 3] [1, 2, 3] at hin
    have hSm_o0 : smFinal 110 = smStore 100 := by
      simpa [smFinal, smNodes, segment_000007_sm_nodes, segment_000007_sm_node] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref3.smGraph smStore [] []
          0 100 [110, 111, 112] 3 110
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hPm0_o0 : pmFinal 300 = pmStore 200 := by
      simpa [pmFinal, pmNodes, segment_000007_pm_nodes, segment_000007_pm_node_0, segment_000007_pm_node_1, segment_000007_pm_node_2, segment_000007_pm_node_3] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref3.pmGraph pmStore
          []
          [{ rank := 1, op := "OpName.FW_multiref", ins := [201], outs := [310, 311, 312], params := [3] }, { rank := 2, op := "OpName.FW_multiref", ins := [202], outs := [320, 321, 322], params := [3] }, { rank := 3, op := "OpName.FW_multiref", ins := [203], outs := [330, 331, 332], params := [3] }]
          0 200 [300, 301, 302] 3 300
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hPm1_o0 : pmFinal 310 = pmStore 201 := by
      simpa [pmFinal, pmNodes, segment_000007_pm_nodes, segment_000007_pm_node_0, segment_000007_pm_node_1, segment_000007_pm_node_2, segment_000007_pm_node_3] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref3.pmGraph pmStore
          [{ rank := 0, op := "OpName.FW_multiref", ins := [200], outs := [300, 301, 302], params := [3] }]
          [{ rank := 2, op := "OpName.FW_multiref", ins := [202], outs := [320, 321, 322], params := [3] }, { rank := 3, op := "OpName.FW_multiref", ins := [203], outs := [330, 331, 332], params := [3] }]
          1 201 [310, 311, 312] 3 310
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hPm2_o0 : pmFinal 320 = pmStore 202 := by
      simpa [pmFinal, pmNodes, segment_000007_pm_nodes, segment_000007_pm_node_0, segment_000007_pm_node_1, segment_000007_pm_node_2, segment_000007_pm_node_3] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref3.pmGraph pmStore
          [{ rank := 0, op := "OpName.FW_multiref", ins := [200], outs := [300, 301, 302], params := [3] }, { rank := 1, op := "OpName.FW_multiref", ins := [201], outs := [310, 311, 312], params := [3] }]
          [{ rank := 3, op := "OpName.FW_multiref", ins := [203], outs := [330, 331, 332], params := [3] }]
          2 202 [320, 321, 322] 3 320
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hPm3_o0 : pmFinal 330 = pmStore 203 := by
      simpa [pmFinal, pmNodes, segment_000007_pm_nodes, segment_000007_pm_node_0, segment_000007_pm_node_1, segment_000007_pm_node_2, segment_000007_pm_node_3] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref3.pmGraph pmStore
          [{ rank := 0, op := "OpName.FW_multiref", ins := [200], outs := [300, 301, 302], params := [3] }, { rank := 1, op := "OpName.FW_multiref", ins := [201], outs := [310, 311, 312], params := [3] }, { rank := 2, op := "OpName.FW_multiref", ins := [202], outs := [320, 321, 322], params := [3] }]
          []
          3 203 [330, 331, 332] 3 330
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hout_o0 : fact_output_0.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 110) ([300, 310, 320, 330].map pmFinal) 1 [1, 8, 3] [1, 2, 3]
      simpa only [pmTids, List.map, hSm_o0, hPm0_o0, hPm1_o0, hPm2_o0, hPm3_o0] using hin
    have hSm_o1 : smFinal 111 = smStore 100 := by
      simpa [smFinal, smNodes, segment_000007_sm_nodes, segment_000007_sm_node] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref3.smGraph smStore [] []
          0 100 [110, 111, 112] 3 111
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hPm0_o1 : pmFinal 301 = pmStore 200 := by
      simpa [pmFinal, pmNodes, segment_000007_pm_nodes, segment_000007_pm_node_0, segment_000007_pm_node_1, segment_000007_pm_node_2, segment_000007_pm_node_3] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref3.pmGraph pmStore
          []
          [{ rank := 1, op := "OpName.FW_multiref", ins := [201], outs := [310, 311, 312], params := [3] }, { rank := 2, op := "OpName.FW_multiref", ins := [202], outs := [320, 321, 322], params := [3] }, { rank := 3, op := "OpName.FW_multiref", ins := [203], outs := [330, 331, 332], params := [3] }]
          0 200 [300, 301, 302] 3 301
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hPm1_o1 : pmFinal 311 = pmStore 201 := by
      simpa [pmFinal, pmNodes, segment_000007_pm_nodes, segment_000007_pm_node_0, segment_000007_pm_node_1, segment_000007_pm_node_2, segment_000007_pm_node_3] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref3.pmGraph pmStore
          [{ rank := 0, op := "OpName.FW_multiref", ins := [200], outs := [300, 301, 302], params := [3] }]
          [{ rank := 2, op := "OpName.FW_multiref", ins := [202], outs := [320, 321, 322], params := [3] }, { rank := 3, op := "OpName.FW_multiref", ins := [203], outs := [330, 331, 332], params := [3] }]
          1 201 [310, 311, 312] 3 311
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hPm2_o1 : pmFinal 321 = pmStore 202 := by
      simpa [pmFinal, pmNodes, segment_000007_pm_nodes, segment_000007_pm_node_0, segment_000007_pm_node_1, segment_000007_pm_node_2, segment_000007_pm_node_3] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref3.pmGraph pmStore
          [{ rank := 0, op := "OpName.FW_multiref", ins := [200], outs := [300, 301, 302], params := [3] }, { rank := 1, op := "OpName.FW_multiref", ins := [201], outs := [310, 311, 312], params := [3] }]
          [{ rank := 3, op := "OpName.FW_multiref", ins := [203], outs := [330, 331, 332], params := [3] }]
          2 202 [320, 321, 322] 3 321
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hPm3_o1 : pmFinal 331 = pmStore 203 := by
      simpa [pmFinal, pmNodes, segment_000007_pm_nodes, segment_000007_pm_node_0, segment_000007_pm_node_1, segment_000007_pm_node_2, segment_000007_pm_node_3] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref3.pmGraph pmStore
          [{ rank := 0, op := "OpName.FW_multiref", ins := [200], outs := [300, 301, 302], params := [3] }, { rank := 1, op := "OpName.FW_multiref", ins := [201], outs := [310, 311, 312], params := [3] }, { rank := 2, op := "OpName.FW_multiref", ins := [202], outs := [320, 321, 322], params := [3] }]
          []
          3 203 [330, 331, 332] 3 331
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hout_o1 : fact_output_1.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 111) ([301, 311, 321, 331].map pmFinal) 1 [1, 8, 3] [1, 2, 3]
      simpa only [pmTids, List.map, hSm_o1, hPm0_o1, hPm1_o1, hPm2_o1, hPm3_o1] using hin
    have hSm_o2 : smFinal 112 = smStore 100 := by
      simpa [smFinal, smNodes, segment_000007_sm_nodes, segment_000007_sm_node] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref3.smGraph smStore [] []
          0 100 [110, 111, 112] 3 112
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hPm0_o2 : pmFinal 302 = pmStore 200 := by
      simpa [pmFinal, pmNodes, segment_000007_pm_nodes, segment_000007_pm_node_0, segment_000007_pm_node_1, segment_000007_pm_node_2, segment_000007_pm_node_3] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref3.pmGraph pmStore
          []
          [{ rank := 1, op := "OpName.FW_multiref", ins := [201], outs := [310, 311, 312], params := [3] }, { rank := 2, op := "OpName.FW_multiref", ins := [202], outs := [320, 321, 322], params := [3] }, { rank := 3, op := "OpName.FW_multiref", ins := [203], outs := [330, 331, 332], params := [3] }]
          0 200 [300, 301, 302] 3 302
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hPm1_o2 : pmFinal 312 = pmStore 201 := by
      simpa [pmFinal, pmNodes, segment_000007_pm_nodes, segment_000007_pm_node_0, segment_000007_pm_node_1, segment_000007_pm_node_2, segment_000007_pm_node_3] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref3.pmGraph pmStore
          [{ rank := 0, op := "OpName.FW_multiref", ins := [200], outs := [300, 301, 302], params := [3] }]
          [{ rank := 2, op := "OpName.FW_multiref", ins := [202], outs := [320, 321, 322], params := [3] }, { rank := 3, op := "OpName.FW_multiref", ins := [203], outs := [330, 331, 332], params := [3] }]
          1 201 [310, 311, 312] 3 312
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hPm2_o2 : pmFinal 322 = pmStore 202 := by
      simpa [pmFinal, pmNodes, segment_000007_pm_nodes, segment_000007_pm_node_0, segment_000007_pm_node_1, segment_000007_pm_node_2, segment_000007_pm_node_3] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref3.pmGraph pmStore
          [{ rank := 0, op := "OpName.FW_multiref", ins := [200], outs := [300, 301, 302], params := [3] }, { rank := 1, op := "OpName.FW_multiref", ins := [201], outs := [310, 311, 312], params := [3] }]
          [{ rank := 3, op := "OpName.FW_multiref", ins := [203], outs := [330, 331, 332], params := [3] }]
          2 202 [320, 321, 322] 3 322
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hPm3_o2 : pmFinal 332 = pmStore 203 := by
      simpa [pmFinal, pmNodes, segment_000007_pm_nodes, segment_000007_pm_node_0, segment_000007_pm_node_1, segment_000007_pm_node_2, segment_000007_pm_node_3] using
        (foldl_faithful_multiref_middle_writer SyntheticMultiref3.pmGraph pmStore
          [{ rank := 0, op := "OpName.FW_multiref", ins := [200], outs := [300, 301, 302], params := [3] }, { rank := 1, op := "OpName.FW_multiref", ins := [201], outs := [310, 311, 312], params := [3] }, { rank := 2, op := "OpName.FW_multiref", ins := [202], outs := [320, 321, 322], params := [3] }]
          []
          3 203 [330, 331, 332] 3 332
          rfl (by native_decide) (by native_decide) (by native_decide)
          (by native_decide) (by native_decide))
    have hout_o2 : fact_output_2.Holds smFinal pmFinal := by
      change ShardedRel (smFinal 112) ([302, 312, 322, 332].map pmFinal) 1 [1, 8, 3] [1, 2, 3]
      simpa only [pmTids, List.map, hSm_o2, hPm0_o2, hPm1_o2, hPm2_o2, hPm3_o2] using hin
    intro fact hfact
    have covered : fact ∈ [fact_output_0, fact_output_1, fact_output_2] ++ state_pre.facts := by
      exact (show state_post.facts ⊆ [fact_output_0, fact_output_1, fact_output_2] ++ state_pre.facts by native_decide) hfact
    simp only [List.mem_append] at covered
    rcases covered with fresh | old
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
      rcases fresh with rfl | rfl | rfl
      · exact hout_o0
      · exact hout_o1
      · exact hout_o2
    · exact hframe fact old

#print axioms segment_000007
end
end TrainVerify.Denote.SyntheticMultiref3
