/- Goal 4 faithful support and layer-12 checkpoint. -/
import denote.yoco_goals.Goal4LateScopedBridge
import denote.yoco_goals.Goal4FaithfulFullTheorem
import denote.yoco_goals.Goal1ExternalFinalComposition
import denote.yoco_goals.L12ZigzagMoERouter

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

def goal1TopkNode (rank logits probs mapTid scores : Nat) : NodeDecl :=
  { rank := rank, op := "OpName.FW_topk_routing", ins := [logits],
    outs := [probs, mapTid, scores], params := [8, 1] }

theorem goal1_topk_scores_reduce (g : GraphDecl) (init : Store)
    (k rank logits probs mapTid scores rows : Nat)
    (hk : k < g.nodes.length)
    (hn : g.nodes[k]'hk = goal1TopkNode rank logits probs mapTid scores)
    (hps : probs ≠ scores) (hms : mapTid ≠ scores)
    (hshape : (denoteGraphDistributedFaithful g init logits).shape = [rows, 64])
    (ha : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (haw : ∀ n ∈ g.nodes.drop (k + 1), scores ∉ n.outs)
    (hp : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpw : ∀ n ∈ g.nodes.drop k, logits ∉ n.outs) :
    denoteGraphDistributedFaithful g init scores =
      (fw_topk_routing (denoteGraphDistributedFaithful g init logits) 8 64).2.2 := by
  have hr := denoteGraphDistributedFaithful_reduce1 g init k
    (goal1TopkNode rank logits probs mapTid scores) logits scores
    (fun x => (fw_topk_routing x 8 (x.shape.reverse.head?.getD 1)).2.2)
    hk hn (by
      intro s
      unfold goal1TopkNode
      rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
        (by simp) (by simp) (by simp)]
      exact applyNode_fw_topk_routing_scores_out g s rank logits probs mapTid scores
        [8, 1] hps hms)
    ha haw hp hpw
  rw [hr, hshape]
  rfl

theorem goal1_gate_scores_of_logits
    {full rank0 rank1 fullScore rank0Score rank1Score cu : Tensor}
    (h : Zigzag2Rel full rank0 rank1 cu [4096, 64] [2048, 64])
    (hdec : decodeCuSeqlens cu = [0, 4096])
    (hf : fullScore = (fw_topk_routing full 8 64).2.2)
    (h0 : rank0Score = (fw_topk_routing rank0 8 64).2.2)
    (h1 : rank1Score = (fw_topk_routing rank1 8 64).2.2) :
    Zigzag2Rel fullScore rank0Score rank1Score cu [4096, 64] [2048, 64] := by
  rw [hf, h0, h1]
  exact Zigzag2Rel.topk_routing_gate_scores 2048 64 8 h
    (by decide) (by decide) (by decide) (by simpa only [Nat.reduceMul] using hdec)

theorem goal4_goal1_sm_shape_coverage : ∀ p ∈ sm_goal_1InitShapes,
    ∃ g ∈ goal_4_full_initGoals, g.ts = p.1 ∧ g.tsShape = p.2 := by
  native_decide

theorem goal4_goal1_pm_shape_coverage : ∀ p ∈ pm_goal_1InitShapes,
    ∃ g ∈ goal_4_full_initGoals, ∃ i,
      ∃ hi : i < g.tps.length, ∃ hj : i < g.tpShapes.length,
      (g.tps[i]'hi).tid = p.1 ∧ g.tpShapes[i]'hj = p.2 := by
  native_decide

theorem goal4_goal1_sm_shapes (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_4.numRanks goal_4_full_initGoals initSM initPM) :
    StoreShapesHold initSM sm_goal_1InitEnv := by
  intro tid sh hlookup
  have hmem : (tid, sh) ∈ sm_goal_1InitShapes :=
    shapeEnvOfList_mem_of_eq_some hlookup
  rcases goal4_goal1_sm_shape_coverage (tid, sh) hmem with ⟨g, hg, htid, hsh⟩
  have hh := hInit g hg
  unfold InitGoalHolds at hh
  simpa only [htid, hsh] using hh.1

theorem goal4_goal1_pm_shapes (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_4.numRanks goal_4_full_initGoals initSM initPM) :
    StoreShapesHold initPM pm_goal_1InitEnv := by
  intro tid sh hlookup
  have hmem : (tid, sh) ∈ pm_goal_1InitShapes :=
    shapeEnvOfList_mem_of_eq_some hlookup
  rcases goal4_goal1_pm_shape_coverage (tid, sh) hmem with
    ⟨g, hg, i, hi, hj, htid, hsh⟩
  have hh := hInit g hg
  unfold InitGoalHolds at hh
  have halign := congrArg (fun xs : List Shape => xs.getD i []) hh.2.1
  simp only [List.map_map, List.getD, List.getElem?_map,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
    Option.map, Option.getD, Function.comp_apply, htid, hsh] at halign
  exact halign

def goal4CanonicalCuAliasTids : List Tid :=
  [5656, 5710, 5764, 5818, 5872, 5926, 5980, 6034, 6088, 6142, 6196, 6250,
   5772, 5826, 5880, 5934, 5988, 6042, 6096, 6150]

theorem goal4_canonical_cu_alias (initPM : Store)
    (hClasses : InputValueClassesHold pmInputValueClasses initPM)
    (tid : Tid) (htid : tid ∈ goal4CanonicalCuAliasTids) :
    denoteGraphDistributedFaithful pm_goal_4 initPM tid =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252 := by
  have hleaf (g : GraphDecl) (t : Tid)
      (hnil : ∀ n ∈ g.nodes, n.outs ≠ [])
      (hw : ∀ n ∈ g.nodes, t ∉ n.outs) :
      denoteGraphDistributedFaithful g initPM t = initPM t := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes initPM t hnil hw
  unfold goal4CanonicalCuAliasTids at htid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at htid
  rcases htid with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [hleaf _ _ (by native_decide) (by native_decide),
      hleaf _ _ (by native_decide) (by native_decide)] <;>
    exact hClasses.eq_of_mem (c := pmInputValueClasses[1]'(by native_decide))
      (by native_decide) (by native_decide) (by native_decide)

theorem zigzag_transport
    {full full' rank0 rank0' rank1 rank1' cu cu' : Tensor}
    {fullShape shardShape : Shape}
    (h : Zigzag2Rel full' rank0' rank1' cu' fullShape shardShape)
    (hf : full = full') (h0 : rank0 = rank0') (h1 : rank1 = rank1')
    (hcu : cu = cu') : Zigzag2Rel full rank0 rank1 cu fullShape shardShape := by
  rw [hf, h0, h1, hcu]
  exact h


structure Goal4L12Checkpoint (initSM initPM : Store) : Prop where
  cache : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 9723) [4096, 1024] [2048, 1024]
  l12 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_4 initSM 5628)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 9832) (denoteGraphDistributedFaithful pm_goal_4 initPM 9833)
    (denoteGraphDistributedFaithful pm_goal_4 initPM 5656) [4096, 64] [2048, 64]

structure Goal4L12AttentionCheckpoint (initSM initPM : Store) : Prop where
  cache : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 9723) [4096, 1024] [2048, 1024]
  attention12 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5620)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 9812)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 9813)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 1024] [2048, 1024]

theorem goal4_l12_attention_checkpoint_of_external
    (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_4.numRanks goal_4_full_initGoals initSM initPM)
    (hContract : Goal4ExternalInputContract initSM initPM) :
    Goal4L12AttentionCheckpoint initSM initPM := by
  have hSM1 := goal4_goal1_sm_shapes initSM initPM hInit
  have hPM1 := goal4_goal1_pm_shapes initSM initPM hInit
  have hInit1 : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM := hInit
  have h6252 : initPM 6252 = initPM 6250 :=
    hContract.2.1.eq_of_mem (c := pmInputValueClasses[1]'(by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hPacked6252 : PackedCuSeqlensWF (initPM 6252) 4096 2 := by
    rw [h6252]
    exact hContract.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hCore : Goal1AncestryInputContract initSM initPM :=
    ⟨hContract.1, hContract.2.1, hPacked6252⟩
  exact ⟨goal1_external_to_cache_faithful_composition initSM initPM hSM1 hPM1 hInit1,
    goal1_external_to_l12_attention_residual initSM initPM hSM1 hPM1 hInit1 hCore⟩

structure Goal4L12BackboneCheckpoint (initSM initPM : Store) : Prop where
  cache : Gather2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5595)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 9722)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 9723) [4096, 1024] [2048, 1024]
  router12 : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5625)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 9826)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 9827)
    (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64]

theorem goal4_l12_router_from_attention
    (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_4.numRanks goal_4_full_initGoals initSM initPM)
    (hAttention : Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5620)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9812)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9813)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 1024] [2048, 1024]) :
    Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5625)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9826)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9827)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] := by
  have hPM1 := goal4_goal1_pm_shapes initSM initPM hInit
  have hInit1 : InitGoalsHold pm_goal_1.numRanks goal_1_full_initGoals initSM initPM := hInit
  have hN12 := l12_zigzag_moe_norm_from_attention_output initSM initPM hInit1 hAttention
  exact (l12_zigzag_moe_router_all_from_norm_input
    initSM initPM hPM1 hInit1 hN12).2.2

theorem goal4_l12_backbone_checkpoint_from_attention
    (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_4.numRanks goal_4_full_initGoals initSM initPM)
    (mid : Goal4L12AttentionCheckpoint initSM initPM) :
    Goal4L12BackboneCheckpoint initSM initPM := by
  exact ⟨mid.cache, goal4_l12_router_from_attention initSM initPM hInit mid.attention12⟩

theorem goal4_l12_backbone_checkpoint_of_external
    (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_4.numRanks goal_4_full_initGoals initSM initPM)
    (hContract : Goal4ExternalInputContract initSM initPM) :
    Goal4L12BackboneCheckpoint initSM initPM := by
  exact goal4_l12_backbone_checkpoint_from_attention initSM initPM hInit
    (goal4_l12_attention_checkpoint_of_external initSM initPM hInit hContract)

theorem goal4_l12_gate_score_from_backbone
    (initSM initPM : Store)
    (hContract : Goal4ExternalInputContract initSM initPM)
    (mid : Goal4L12BackboneCheckpoint initSM initPM) :
    Zigzag2Rel (denoteGraphDistributedFaithful sm_goal_1 initSM 5628)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9832)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 9833)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) [4096, 64] [2048, 64] := by
  have h6252 : initPM 6252 = initPM 6250 :=
    hContract.2.1.eq_of_mem (c := pmInputValueClasses[1]'(by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hPacked6252 : PackedCuSeqlensWF (initPM 6252) 4096 2 := by
    rw [h6252]
    exact hContract.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hCuLeaf : denoteGraphDistributedFaithful pm_goal_1 initPM 6252 = initPM 6252 := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM 6252 (by native_decide) (by native_decide)
  have hDec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096] := by
    rw [hCuLeaf]
    exact hPacked6252.decoded_single
  exact goal1_gate_scores_of_logits mid.router12 hDec
    (goal1_topk_scores_reduce sm_goal_1 initSM 523 0 5625 5626 5627 5628 4096
      (by native_decide) (by native_decide) (by decide) (by decide) mid.router12.full_shape
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (goal1_topk_scores_reduce pm_goal_1 initPM 1163 0 9826 9828 9830 9832 2048
      (by native_decide) (by native_decide) (by decide) (by decide) mid.router12.rank0_shape
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))
    (goal1_topk_scores_reduce pm_goal_1 initPM 1164 1 9827 9829 9831 9833 2048
      (by native_decide) (by native_decide) (by decide) (by decide) mid.router12.rank1_shape
      (by native_decide) (by native_decide) (by native_decide) (by native_decide))

theorem goal4_l12_checkpoint_of_external
    (initSM initPM : Store)
    (_hSM : StoreShapesHold initSM sm_goal_4InitEnv)
    (_hPM : StoreShapesHold initPM pm_goal_4InitEnv)
    (hInit : InitGoalsHold pm_goal_4.numRanks goal_4_full_initGoals initSM initPM)
    (hContract : Goal4ExternalInputContract initSM initPM) :
    Goal4L12Checkpoint initSM initPM := by
  have mid := goal4_l12_backbone_checkpoint_of_external initSM initPM hInit hContract
  have hScore12 := goal4_l12_gate_score_from_backbone initSM initPM hContract mid
  exact {
    cache := mid.cache
    l12 := zigzag_transport hScore12
      (goal4_late_sm_to_goal1 initSM 5628 (by decide))
      (goal4_late_pm_to_goal1 initPM 9832 (by decide))
      (goal4_late_pm_to_goal1 initPM 9833 (by decide))
      (goal4_canonical_cu_alias initPM hContract.2.1 5656 (by decide))
  }

end
end TrainVerify.Denote.GeneratedPatterns
