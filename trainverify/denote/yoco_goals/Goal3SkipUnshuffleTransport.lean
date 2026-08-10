/- Goal 3: erase the 48 stack-only unshuffle nodes and transport the
   observable model-body store to the faithful Goal-1 graph. -/
import denote.yoco_goals.Goal3FaithfulFullTheorem
import denote.yoco_goals.Goal1ExternalFinalComposition

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

private def skipUnshuffle (n : NodeDecl) : Bool :=
  decide (n.op ≠ "OpName.FW_maybe_unshuffle")

private def goal3SmExcludedTids : List Tid :=
  ((sm.nodes.take 939).filter fun n => !skipUnshuffle n).flatMap (fun n => n.outs)

private def goal3PmExcludedTids : List Tid :=
  ((pm.nodes.take 2055).filter fun n => !skipUnshuffle n).flatMap (fun n => n.outs)

private def ScopedEq (excluded : List Tid) (s t : Store) : Prop :=
  ∀ tid, tid ∉ excluded → s tid = t tid

private theorem storeSet_scoped_congr (excluded : List Tid) (s t : Store)
    (pairs : List (Tid × Tensor)) (h : ScopedEq excluded s t) :
    ScopedEq excluded (storeSet s pairs) (storeSet t pairs) := by
  intro tid htid
  unfold storeSet
  cases hp : pairs.find? (fun p => decide (p.1 = tid)) with
  | none => exact h tid htid
  | some p => rfl

private theorem map_store_eq {excluded xs : List Tid} {s t : Store}
    (h : ScopedEq excluded s t)
    (hxs : ∀ tid ∈ xs, tid ∉ excluded) : xs.map s = xs.map t := by
  apply List.map_congr_left
  intro tid htid
  exact h tid (hxs tid htid)

private theorem buddy_map_store_eq (excluded : List Tid) (g : GraphDecl)
    (n : NodeDecl) (s t : Store) (h : ScopedEq excluded s t) (idx : Nat)
    (hread : ∀ m ∈ g.replicaBuddies n, m.ins.getD idx 0 ∉ excluded) :
    (g.replicaBuddies n).map (fun m => s (m.ins.getD idx 0)) =
      (g.replicaBuddies n).map (fun m => t (m.ins.getD idx 0)) := by
  apply List.map_congr_left
  intro m hm
  exact h _ (hread m hm)

private theorem applyNode_scoped_congr (excluded : List Tid) (g : GraphDecl)
    (s t : Store) (n : NodeDecl) (h : ScopedEq excluded s t)
    (hins : ∀ tid ∈ n.ins, tid ∉ excluded) :
    ScopedEq excluded (applyNode g s n) (applyNode g t n) := by
  have hargs := map_store_eq h hins
  intro tid htid
  unfold applyNode
  rw [hargs]
  exact storeSet_scoped_congr excluded s t _ h tid htid

private theorem faithful_step_scoped_congr (excluded : List Tid) (g : GraphDecl)
    (s t : Store) (n : NodeDecl) (h : ScopedEq excluded s t)
    (hunshuffle : n.op ≠ "OpName.FW_maybe_unshuffle")
    (hins : ∀ tid ∈ n.ins, tid ∉ excluded)
    (hget : ∀ i < 5, n.ins.getD i 0 ∉ excluded)
    (hbuddy : ∀ m ∈ g.replicaBuddies n, ∀ i < 5,
      m.ins.getD i 0 ∉ excluded) :
    ScopedEq excluded (applyNodeDistributedFaithful g s n)
      (applyNodeDistributedFaithful g t n) := by
  unfold applyNodeDistributedFaithful
  by_cases hshuffle : n.op = "OpName.FW_maybe_shuffle"
  · rw [if_pos hshuffle, if_pos hshuffle]
    have hv : applyNodeFaithfulShuffleValue g s n =
        applyNodeFaithfulShuffleValue g t n := by
      unfold applyNodeFaithfulShuffleValue
      dsimp only
      rw [buddy_map_store_eq excluded g n s t h 0
            (fun m hm => hbuddy m hm 0 (by decide)),
        h _ (hget 1 (by decide))]
    rw [hv]
    exact storeSet_scoped_congr excluded s t _ h
  · rw [if_neg hshuffle, if_neg hshuffle, if_neg hunshuffle, if_neg hunshuffle]
    by_cases hattn : n.op = "OpName.FW_attn_zigzag"
    · rw [if_pos hattn, if_pos hattn]
      have hv : applyNodeFaithfulZigzagAttnValue g s n =
          applyNodeFaithfulZigzagAttnValue g t n := by
        unfold applyNodeFaithfulZigzagAttnValue
        dsimp only
        have hq := buddy_map_store_eq excluded g n s t h 0
          (fun m hm => hbuddy m hm 0 (by decide))
        have hk := buddy_map_store_eq excluded g n s t h 1
          (fun m hm => hbuddy m hm 1 (by decide))
        have hv := buddy_map_store_eq excluded g n s t h 2
          (fun m hm => hbuddy m hm 2 (by decide))
        have hk' : ((g.replicaBuddies n).map (fun m => m.ins.getD 1 0)).map s =
            ((g.replicaBuddies n).map (fun m => m.ins.getD 1 0)).map t := by
          simpa only [List.map_map, Function.comp_def] using hk
        have hv' : ((g.replicaBuddies n).map (fun m => m.ins.getD 2 0)).map s =
            ((g.replicaBuddies n).map (fun m => m.ins.getD 2 0)).map t := by
          simpa only [List.map_map, Function.comp_def] using hv
        by_cases hz : zigzagAttnUsesReplicatedKV g n = true
        · rw [if_pos hz, if_pos hz, hq,
            h _ (hget 1 (by decide)), h _ (hget 2 (by decide)),
            h _ (hget 3 (by decide)), h _ (hget 4 (by decide))]
        · rw [if_neg hz, if_neg hz, hq, hk', hv',
            h _ (hget 3 (by decide)), h _ (hget 4 (by decide))]
      rw [hv]
      exact storeSet_scoped_congr excluded s t _ h
    · rw [if_neg hattn, if_neg hattn]
      unfold applyNodeDistributed
      by_cases hmoe : n.op = "OpName.FW_all2all_moe_gmm"
      · rw [if_pos hmoe, if_pos hmoe]
        have hv : applyNodeFullExpertMoE_value g s n =
            applyNodeFullExpertMoE_value g t n := by
          unfold applyNodeFullExpertMoE_value
          dsimp only
          rw [h _ (hget 0 (by decide)), h _ (hget 1 (by decide)),
            h _ (hget 2 (by decide)),
            buddy_map_store_eq excluded g n s t h 3
              (fun m hm => hbuddy m hm 3 (by decide)),
            buddy_map_store_eq excluded g n s t h 4
              (fun m hm => hbuddy m hm 4 (by decide))]
        rw [hv]
        exact storeSet_scoped_congr excluded s t _ h
      · rw [if_neg hmoe, if_neg hmoe]
        unfold applyNodeRingAttn
        rw [if_neg hattn, if_neg hattn]
        by_cases hwindow : n.op = "OpName.FW_attn_sliding_window"
        · rw [if_pos hwindow, if_pos hwindow]
          have hv : applyNodeRingAttn_sliding_window g s n =
              applyNodeRingAttn_sliding_window g t n := by
            unfold applyNodeRingAttn_sliding_window ringAttnBuddies
            dsimp only
            rw [buddy_map_store_eq excluded g n s t h 0
                  (fun m hm => hbuddy m hm 0 (by decide)),
              buddy_map_store_eq excluded g n s t h 1
                  (fun m hm => hbuddy m hm 1 (by decide)),
              buddy_map_store_eq excluded g n s t h 2
                  (fun m hm => hbuddy m hm 2 (by decide)),
              h _ (hget 3 (by decide)), h _ (hget 4 (by decide))]
          rw [hv]
          exact storeSet_scoped_congr excluded s t _ h
        · rw [if_neg hwindow, if_neg hwindow]
          exact applyNode_scoped_congr excluded g s t n h hins

private theorem faithful_step_graph_eq (g₁ g₂ : GraphDecl) (s : Store)
    (n : NodeDecl) (hranks : g₁.numRanks = g₂.numRanks)
    (hbuddies : g₁.replicaBuddies n = g₂.replicaBuddies n) :
    applyNodeDistributedFaithful g₁ s n = applyNodeDistributedFaithful g₂ s n := by
  unfold applyNodeDistributedFaithful
  by_cases hshuffle : n.op = "OpName.FW_maybe_shuffle"
  · rw [if_pos hshuffle, if_pos hshuffle]
    unfold applyNodeFaithfulShuffleValue
    rw [hbuddies]
  · rw [if_neg hshuffle, if_neg hshuffle]
    by_cases hunshuffle : n.op = "OpName.FW_maybe_unshuffle"
    · rw [if_pos hunshuffle, if_pos hunshuffle]
      unfold applyNodeFaithfulUnshuffleValue
      rw [hbuddies]
    · rw [if_neg hunshuffle, if_neg hunshuffle]
      by_cases hattn : n.op = "OpName.FW_attn_zigzag"
      · rw [if_pos hattn, if_pos hattn]
        unfold applyNodeFaithfulZigzagAttnValue zigzagAttnUsesReplicatedKV
        rw [hbuddies, hranks]
      · rw [if_neg hattn, if_neg hattn]
        unfold applyNodeDistributed
        by_cases hmoe : n.op = "OpName.FW_all2all_moe_gmm"
        · rw [if_pos hmoe, if_pos hmoe]
          unfold applyNodeFullExpertMoE_value
          rw [hbuddies]
        · rw [if_neg hmoe, if_neg hmoe]
          unfold applyNodeRingAttn
          rw [if_neg hattn, if_neg hattn]
          by_cases hwindow : n.op = "OpName.FW_attn_sliding_window"
          · rw [if_pos hwindow, if_pos hwindow]
            unfold applyNodeRingAttn_sliding_window ringAttnBuddies
            rw [hbuddies]
          · rw [if_neg hwindow, if_neg hwindow]
            rw [applyNode_congr_numRanks g₁ g₂ hranks]

private theorem fold_filter_scoped
    (excluded : List Tid) (gFull gRef : GraphDecl) (nodes : List NodeDecl)
    (hranks : gFull.numRanks = gRef.numRanks)
    (hfacts : ∀ n ∈ nodes,
      (n.op = "OpName.FW_maybe_unshuffle" →
        n.outs ≠ [] ∧ ∀ tid ∈ n.outs, tid ∈ excluded) ∧
      (n.op ≠ "OpName.FW_maybe_unshuffle" →
        gFull.replicaBuddies n = gRef.replicaBuddies n ∧
        (∀ tid ∈ n.ins, tid ∉ excluded) ∧
        (∀ i < 5, n.ins.getD i 0 ∉ excluded) ∧
        (∀ m ∈ gRef.replicaBuddies n, ∀ i < 5,
          m.ins.getD i 0 ∉ excluded)))
    (s t : Store) (hst : ScopedEq excluded s t) :
    ScopedEq excluded
      (nodes.foldl (applyNodeDistributedFaithful gFull) s)
      ((nodes.filter skipUnshuffle).foldl
        (applyNodeDistributedFaithful gRef) t) := by
  induction nodes generalizing s t with
  | nil => exact hst
  | cons n rest ih =>
      simp only [List.foldl, List.filter_cons]
      by_cases hu : n.op = "OpName.FW_maybe_unshuffle"
      · have hskip : skipUnshuffle n = false := by
          unfold skipUnshuffle
          simp [hu]
        rw [hskip]
        apply ih
        · intro m hm
          exact hfacts m (List.mem_cons_of_mem n hm)
        · intro tid htid
          rw [applyNodeDistributedFaithful_eq_of_not_mem_outs gFull s n tid
            ((hfacts n List.mem_cons_self).1 hu).1 (by
              intro hmem
              exact htid (((hfacts n List.mem_cons_self).1 hu).2 tid hmem))]
          exact hst tid htid
      · have hkeep : skipUnshuffle n = true := by
          unfold skipUnshuffle
          simp [hu]
        rw [hkeep]
        have hn := (hfacts n List.mem_cons_self).2 hu
        have hgraph := faithful_step_graph_eq gFull gRef s n hranks hn.1
        have hscope := faithful_step_scoped_congr excluded gRef s t n hst hu
          hn.2.1 hn.2.2.1 hn.2.2.2
        apply ih
        · intro m hm
          exact hfacts m (List.mem_cons_of_mem n hm)
        · intro tid htid
          rw [hgraph]
          exact hscope tid htid

private theorem goal3_sm_filter_facts :
    (sm.nodes.take 939).filter skipUnshuffle = sm_goal_1.nodes.take 915 ∧
    sm.numRanks = sm_goal_1.numRanks ∧
    (∀ n ∈ sm.nodes.take 939,
      (n.op = "OpName.FW_maybe_unshuffle" →
        n.outs ≠ [] ∧ ∀ tid ∈ n.outs, tid ∈ goal3SmExcludedTids) ∧
      (n.op ≠ "OpName.FW_maybe_unshuffle" →
        sm.replicaBuddies n = sm_goal_1.replicaBuddies n ∧
        (∀ tid ∈ n.ins, tid ∉ goal3SmExcludedTids) ∧
        (∀ i < 5, n.ins.getD i 0 ∉ goal3SmExcludedTids) ∧
        (∀ m ∈ sm_goal_1.replicaBuddies n, ∀ i < 5,
          m.ins.getD i 0 ∉ goal3SmExcludedTids))) := by
  native_decide

private theorem goal3_pm_filter_facts :
    (pm.nodes.take 2055).filter skipUnshuffle = pm_goal_1.nodes.take 2007 ∧
    pm.numRanks = pm_goal_1.numRanks ∧
    (∀ n ∈ pm.nodes.take 2055,
      (n.op = "OpName.FW_maybe_unshuffle" →
        n.outs ≠ [] ∧ ∀ tid ∈ n.outs, tid ∈ goal3PmExcludedTids) ∧
      (n.op ≠ "OpName.FW_maybe_unshuffle" →
        pm.replicaBuddies n = pm_goal_1.replicaBuddies n ∧
        (∀ tid ∈ n.ins, tid ∉ goal3PmExcludedTids) ∧
        (∀ i < 5, n.ins.getD i 0 ∉ goal3PmExcludedTids) ∧
        (∀ m ∈ pm_goal_1.replicaBuddies n, ∀ i < 5,
          m.ins.getD i 0 ∉ goal3PmExcludedTids))) := by
  native_decide

private theorem goal3_sm_prefix_scoped (init : Store) :
    ScopedEq goal3SmExcludedTids
      ((sm.nodes.take 939).foldl (applyNodeDistributedFaithful sm) init)
      ((sm_goal_1.nodes.take 915).foldl
        (applyNodeDistributedFaithful sm_goal_1) init) := by
  rw [← goal3_sm_filter_facts.1]
  exact fold_filter_scoped goal3SmExcludedTids sm sm_goal_1 (sm.nodes.take 939)
    goal3_sm_filter_facts.2.1 goal3_sm_filter_facts.2.2 init init
    (fun _ _ => rfl)

private theorem goal3_pm_prefix_scoped (init : Store) :
    ScopedEq goal3PmExcludedTids
      ((pm.nodes.take 2055).foldl (applyNodeDistributedFaithful pm) init)
      ((pm_goal_1.nodes.take 2007).foldl
        (applyNodeDistributedFaithful pm_goal_1) init) := by
  rw [← goal3_pm_filter_facts.1]
  exact fold_filter_scoped goal3PmExcludedTids pm pm_goal_1 (pm.nodes.take 2055)
    goal3_pm_filter_facts.2.1 goal3_pm_filter_facts.2.2 init init
    (fun _ _ => rfl)

private def goal3LateSmPreUnshuffleTids : List Tid :=
  [5627, 5681, 5735, 5789, 5843, 5897, 5951, 6005, 6059, 6113, 6167, 6221]

private def goal3LatePmPreUnshuffleTids : List Tid :=
  [9830, 9831, 9984, 9985, 10138, 10139, 10292, 10293,
   10446, 10447, 10600, 10601, 10754, 10755, 10908, 10909,
   11062, 11063, 11216, 11217, 11370, 11371, 11524, 11525,
   5654, 5708, 5762, 5816, 5870, 5924, 5978, 6032, 6086, 6140, 6194, 6248]

private theorem goal3_sm_pre_unshuffle_transport (init : Store) (tid : Tid)
    (htid : tid ∈ goal3LateSmPreUnshuffleTids) :
    denoteGraphDistributedFaithful sm init tid =
      denoteGraphDistributedFaithful sm_goal_1 init tid := by
  unfold goal3LateSmPreUnshuffleTids at htid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at htid
  rcases htid with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;>
    rw [← denoteGraphDistributedFaithful_prefix_read sm init 939 _
          (by native_decide) (by native_decide),
        ← denoteGraphDistributedFaithful_prefix_read sm_goal_1 init 915 _
          (by native_decide) (by native_decide)] <;>
    exact goal3_sm_prefix_scoped init _ (by native_decide)

private theorem goal3_pm_pre_unshuffle_transport (init : Store) (tid : Tid)
    (htid : tid ∈ goal3LatePmPreUnshuffleTids) :
    denoteGraphDistributedFaithful pm init tid =
      denoteGraphDistributedFaithful pm_goal_1 init tid := by
  unfold goal3LatePmPreUnshuffleTids at htid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at htid
  rcases htid with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [← denoteGraphDistributedFaithful_prefix_read pm init 2055 _
          (by native_decide) (by native_decide),
        ← denoteGraphDistributedFaithful_prefix_read pm_goal_1 init 2007 _
          (by native_decide) (by native_decide)] <;>
    exact goal3_pm_prefix_scoped init _ (by native_decide)

private def goal1LateCuAliasTids : List Tid :=
  [5654, 5708, 5762, 5816, 5870, 5924, 5978, 6032, 6086, 6140, 6194, 6248,
   5772, 5826, 5880, 5934, 5988, 6042, 6096, 6150]

private theorem goal1_late_cu_alias (initPM : Store)
    (hClasses : InputValueClassesHold pmInputValueClasses initPM)
    (tid : Tid) (htid : tid ∈ goal1LateCuAliasTids) :
    denoteGraphDistributedFaithful pm_goal_1 initPM tid =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252 := by
  have hleaf (t : Tid) (hw : ∀ n ∈ pm_goal_1.nodes, t ∉ n.outs) :
      denoteGraphDistributedFaithful pm_goal_1 initPM t = initPM t := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM t (by native_decide) hw
  unfold goal1LateCuAliasTids at htid
  simp only [List.mem_cons, List.not_mem_nil, or_false] at htid
  rcases htid with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [hleaf _ (by native_decide), hleaf _ (by native_decide)] <;>
    exact hClasses.eq_of_mem (c := pmInputValueClasses[1]'(by native_decide))
      (by native_decide) (by native_decide) (by native_decide)

private theorem goal3_late_cu_transport (initPM : Store)
    (hClasses : InputValueClassesHold pmInputValueClasses initPM)
    (tid : Tid)
    (htid : tid ∈ [5654, 5708, 5762, 5816, 5870, 5924,
      5978, 6032, 6086, 6140, 6194, 6248]) :
    denoteGraphDistributedFaithful pm initPM tid =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6252 := by
  exact (goal3_pm_pre_unshuffle_transport initPM tid (by
    unfold goal3LatePmPreUnshuffleTids
    simp only [List.mem_cons, List.not_mem_nil, or_false] at htid ⊢
    rcases htid with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> decide)).trans
    (goal1_late_cu_alias initPM hClasses tid (by
      unfold goal1LateCuAliasTids
      simp only [List.mem_cons, List.not_mem_nil, or_false] at htid ⊢
      rcases htid with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> decide))

private theorem zigzag_transport
    {full full' rank0 rank0' rank1 rank1' cu cu' : Tensor}
    {fullShape shardShape : Shape}
    (h : Zigzag2Rel full' rank0' rank1' cu' fullShape shardShape)
    (hf : full = full') (h0 : rank0 = rank0') (h1 : rank1 = rank1')
    (hcu : cu = cu') : Zigzag2Rel full rank0 rank1 cu fullShape shardShape := by
  rw [hf, h0, h1, hcu]
  exact h

/-- The late routing ancestry is not a caller premise: it is reconstructed in
Goal 1, then transported across the exact skip-unshuffle graph isomorphism. -/
theorem goal3_routing_late_ancestry_of_external
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv)
    (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hContract : Goal3FullExternalInputs initSM initPM) :
    Goal3RoutingLateAncestry initSM initPM := by
  have hSM1 : StoreShapesHold initSM sm_goal_1InitEnv := by
    apply storeShapesHold_weaken (small := sm_goal_1InitShapes) (big := smInitShapes)
    · native_decide
    · exact hSM
  have hPM1 : StoreShapesHold initPM pm_goal_1InitEnv := by
    apply storeShapesHold_weaken (small := pm_goal_1InitShapes) (big := pmInitShapes)
    · native_decide
    · exact hPM
  have h6252 : initPM 6252 = initPM 6248 :=
    hContract.2.1.eq_of_mem (c := pmInputValueClasses[1]'(by native_decide))
      (by native_decide) (by native_decide) (by native_decide)
  have hPacked6252 : PackedCuSeqlensWF (initPM 6252) 4096 2 := by
    rw [h6252]
    exact hContract.2.2
  have hCore : Goal1AncestryInputContract initSM initPM :=
    ⟨hContract.1, hContract.2.1, hPacked6252⟩
  have hCache := goal1_external_to_cache_faithful_composition
    initSM initPM hSM1 hPM1 hInit
  have hA12 := goal1_external_to_l12_attention_residual
    initSM initPM hSM1 hPM1 hInit hCore
  have hR12 := (l12_zigzag_moe_router_from_attention_output
    initSM initPM hPM1 hInit hA12).2
  have hO12 := l12_zigzag_moe_output_from_attention_output
    initSM initPM hSM1 hPM1 hInit hA12
  have hA12b2 := canonical_l12b2_attention_residual_from_incoming_and_cache
    initSM initPM hPM1 hInit hO12 hCache hCore
  have hR12b2 := (l12b2_zigzag_moe_router_from_attention_output
    initSM initPM hPM1 hInit hA12b2).2
  have hO12b2 := l12b2_zigzag_moe_output_from_attention_output
    initSM initPM hSM1 hPM1 hInit hA12b2
  have hA12b3 := goal1_l12_block3_attention_residual_from_stream_cache
    initSM initPM hPM1 hInit hCore hO12b2 hCache
  have hR12b3 := (goal1_l12_block3_moe_router_from_attention_output
    initSM initPM hPM1 hInit hA12b3).2
  have hO12b3 := goal1_l12_block3_moe_output_from_attention_output
    initSM initPM hSM1 hPM1 hInit hA12b3
  have hDecoded : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252) = [0, 4096] := by
    have hleaf : denoteGraphDistributedFaithful pm_goal_1 initPM 6252 = initPM 6252 := by
      unfold denoteGraphDistributedFaithful
      exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
        initPM 6252 (by native_decide) (by native_decide)
    rw [hleaf]
    exact hPacked6252.decoded_single
  have hA13 := canonical_l13_attention_residual_from_incoming_and_cache
    initSM initPM hPM1 hInit hO12b3 hCache
      (goal1_late_cu_alias initPM hContract.2.1 5772 (by decide)) hDecoded
  have hR13 := (l13_zigzag_moe_router_from_attention_output
    initSM initPM hPM1 hInit hA13).2
  have hO13 := l13_zigzag_moe_output_from_attention_output
    initSM initPM hSM1 hPM1 hInit hA13
  have hA14 := canonical_l14_attention_residual_from_incoming_and_cache
    initSM initPM hPM1 hInit hO13 hCache
      (goal1_late_cu_alias initPM hContract.2.1 5826 (by decide)) hDecoded
  have hR14 := (l14_zigzag_moe_router_from_attention_output
    initSM initPM hPM1 hInit hA14).2
  have hO14 := l14_zigzag_moe_output_from_attention_output
    initSM initPM hSM1 hPM1 hInit hA14
  have hA15 := canonical_l15_attention_residual_from_incoming_and_cache
    initSM initPM hPM1 hInit hO14 hCache
      (goal1_late_cu_alias initPM hContract.2.1 5880 (by decide)) hDecoded
  have hR15 := (l15_zigzag_moe_router_from_attention_output
    initSM initPM hPM1 hInit hA15).2
  have hO15 := l15_zigzag_moe_output_from_attention_output
    initSM initPM hSM1 hPM1 hInit hA15
  have hA16 := canonical_l16_attention_residual_from_incoming_and_cache
    initSM initPM hPM1 hInit hO15 hCache
      (goal1_late_cu_alias initPM hContract.2.1 5934 (by decide)) hDecoded
  have hR16 := (l16_zigzag_moe_router_from_attention_output
    initSM initPM hPM1 hInit hA16).2
  have hO16 := l16_zigzag_moe_output_from_attention_output
    initSM initPM hSM1 hPM1 hInit hA16
  have hA17 := canonical_l17_attention_residual_from_incoming_and_cache
    initSM initPM hPM1 hInit hO16 hCache
      (goal1_late_cu_alias initPM hContract.2.1 5988 (by decide)) hDecoded
  have hR17 := (l17_zigzag_moe_router_from_attention_output
    initSM initPM hPM1 hInit hA17).2
  have hO17 := l17_zigzag_moe_output_from_attention_output
    initSM initPM hSM1 hPM1 hInit hA17
  have hA18 := canonical_l18_attention_residual_from_incoming_and_cache
    initSM initPM hPM1 hInit hO17 hCache
      (goal1_late_cu_alias initPM hContract.2.1 6042 (by decide)) hDecoded
  have hR18 := (l18_zigzag_moe_router_from_attention_output
    initSM initPM hPM1 hInit hA18).2
  have hO18 := l18_zigzag_moe_output_from_attention_output
    initSM initPM hSM1 hPM1 hInit hA18
  have hA19 := canonical_l19_attention_residual_from_incoming_and_cache
    initSM initPM hPM1 hInit hO18 hCache
      (goal1_late_cu_alias initPM hContract.2.1 6096 (by decide)) hDecoded
  have hR19 := (l19_zigzag_moe_router_from_attention_output
    initSM initPM hPM1 hInit hA19).2
  have hO19 := l19_zigzag_moe_output_from_attention_output
    initSM initPM hSM1 hPM1 hInit hA19
  have hO20 := canonical_l20_output_from_l19_and_cache
    initSM initPM hPM1 hInit hO19 hCache
      (goal1_late_cu_alias initPM hContract.2.1 6150 (by decide)) hDecoded
  have hR21 := (canonical_l21_router_from_layer20_output
    initSM initPM hPM1 hInit hO20).2
  have hO21 := canonical_l21_output_from_layer20_output
    initSM initPM hSM1 hPM1 hInit hO20
  have hQ := canonical_l22_q_relation_from_l21 initSM initPM hPM1 hInit hO21
  have hK := canonical_l22_k_ordinary_relation initSM initPM hPM1 hInit hCache
  have hV := canonical_l22_v_ordinary_relation initSM initPM hPM1 hInit hCache
  have hA22 := canonical_l22_attention_from_qkv initSM initPM hInit
    hContract.2.1 hPacked6252 hQ hK hV
  have hResidual22 := canonical_l22_residual_from_layer21_output initSM initPM hO21
  have hwEq : denoteGraphDistributedFaithful sm_goal_1 initSM 6210 =
      denoteGraphDistributedFaithful pm_goal_1 initPM 6210 := by
    have hi := (hInit initGoal_6210 (by native_decide)).2.2
    rw [show pm.numRanks = pm_goal_1.numRanks by native_decide] at hi
    rw [reconstructForGoal_of_not_replicated initGoal_6210 pm_goal_1.numRanks _ rfl,
      show initGoal_6210.tps = [{rank := 0, tid := 6210}] from rfl,
      show initGoal_6210.ts = 6210 from rfl,
      show initGoal_6210.gatherDim = 0 from rfl] at hi
    simp only [List.map, reconstructWithDim] at hi
    unfold denoteGraphDistributedFaithful
    rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_1 sm_goal_1.nodes
        initSM 6210 (by native_decide) (by native_decide),
      foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
        initPM 6210 (by native_decide) (by native_decide)]
    exact hi
  have hwShape : (denoteGraphDistributedFaithful pm_goal_1 initPM 6210).shape =
      [1024, 1024] := by
    unfold denoteGraphDistributedFaithful
    rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_1 pm_goal_1.nodes
      initPM 6210 (by native_decide) (by native_decide)]
    exact hPM1 6210 [1024, 1024] (by native_decide)
  have hO22 := canonical_l22_output_from_inputs initSM initPM
    hResidual22 hA22 hwEq hwShape
  have hNorm23 := canonical_l23_norm_from_l22_inputs initSM initPM hInit
    hResidual22 hA22 hwEq hwShape
  have hR23 := (canonical_l23_router_from_norm_input
    initSM initPM hPM1 hInit hNorm23).2
  exact {
    l12 := zigzag_transport hR12
      (goal3_sm_pre_unshuffle_transport initSM 5627 (by decide))
      (goal3_pm_pre_unshuffle_transport initPM 9830 (by decide))
      (goal3_pm_pre_unshuffle_transport initPM 9831 (by decide))
      (goal3_late_cu_transport initPM hContract.2.1 5654 (by decide))
    l13 := zigzag_transport hR12b2
      (goal3_sm_pre_unshuffle_transport initSM 5681 (by decide))
      (goal3_pm_pre_unshuffle_transport initPM 9984 (by decide))
      (goal3_pm_pre_unshuffle_transport initPM 9985 (by decide))
      (goal3_late_cu_transport initPM hContract.2.1 5708 (by decide))
    l14 := zigzag_transport hR12b3
      (goal3_sm_pre_unshuffle_transport initSM 5735 (by decide))
      (goal3_pm_pre_unshuffle_transport initPM 10138 (by decide))
      (goal3_pm_pre_unshuffle_transport initPM 10139 (by decide))
      (goal3_late_cu_transport initPM hContract.2.1 5762 (by decide))
    l15 := zigzag_transport hR13
      (goal3_sm_pre_unshuffle_transport initSM 5789 (by decide))
      (goal3_pm_pre_unshuffle_transport initPM 10292 (by decide))
      (goal3_pm_pre_unshuffle_transport initPM 10293 (by decide))
      (goal3_late_cu_transport initPM hContract.2.1 5816 (by decide))
    l16 := zigzag_transport hR14
      (goal3_sm_pre_unshuffle_transport initSM 5843 (by decide))
      (goal3_pm_pre_unshuffle_transport initPM 10446 (by decide))
      (goal3_pm_pre_unshuffle_transport initPM 10447 (by decide))
      (goal3_late_cu_transport initPM hContract.2.1 5870 (by decide))
    l17 := zigzag_transport hR15
      (goal3_sm_pre_unshuffle_transport initSM 5897 (by decide))
      (goal3_pm_pre_unshuffle_transport initPM 10600 (by decide))
      (goal3_pm_pre_unshuffle_transport initPM 10601 (by decide))
      (goal3_late_cu_transport initPM hContract.2.1 5924 (by decide))
    l18 := zigzag_transport hR16
      (goal3_sm_pre_unshuffle_transport initSM 5951 (by decide))
      (goal3_pm_pre_unshuffle_transport initPM 10754 (by decide))
      (goal3_pm_pre_unshuffle_transport initPM 10755 (by decide))
      (goal3_late_cu_transport initPM hContract.2.1 5978 (by decide))
    l19 := zigzag_transport hR17
      (goal3_sm_pre_unshuffle_transport initSM 6005 (by decide))
      (goal3_pm_pre_unshuffle_transport initPM 10908 (by decide))
      (goal3_pm_pre_unshuffle_transport initPM 10909 (by decide))
      (goal3_late_cu_transport initPM hContract.2.1 6032 (by decide))
    l20 := zigzag_transport hR18
      (goal3_sm_pre_unshuffle_transport initSM 6059 (by decide))
      (goal3_pm_pre_unshuffle_transport initPM 11062 (by decide))
      (goal3_pm_pre_unshuffle_transport initPM 11063 (by decide))
      (goal3_late_cu_transport initPM hContract.2.1 6086 (by decide))
    l21 := zigzag_transport hR19
      (goal3_sm_pre_unshuffle_transport initSM 6113 (by decide))
      (goal3_pm_pre_unshuffle_transport initPM 11216 (by decide))
      (goal3_pm_pre_unshuffle_transport initPM 11217 (by decide))
      (goal3_late_cu_transport initPM hContract.2.1 6140 (by decide))
    l22 := zigzag_transport hR21
      (goal3_sm_pre_unshuffle_transport initSM 6167 (by decide))
      (goal3_pm_pre_unshuffle_transport initPM 11370 (by decide))
      (goal3_pm_pre_unshuffle_transport initPM 11371 (by decide))
      (goal3_late_cu_transport initPM hContract.2.1 6194 (by decide))
    l23 := zigzag_transport hR23
      (goal3_sm_pre_unshuffle_transport initSM 6221 (by decide))
      (goal3_pm_pre_unshuffle_transport initPM 11524 (by decide))
      (goal3_pm_pre_unshuffle_transport initPM 11525 (by decide))
      (goal3_late_cu_transport initPM hContract.2.1 6248 (by decide))
  }

/-- Public faithful full Goal 3 theorem.  Late ancestry is reconstructed from
external inputs, transported across the 48 skipped unshuffle nodes, and then
consumed by the existing routing certificates and generated stack tail. -/
theorem prove_goal_3_full : goal_3_stmt_full := by
  intro initSM initPM hSM hPM hInit hContract
  exact canonical_goal_3_from_late_ancestry initSM initPM hSM hPM hInit hContract
    (goal3_routing_late_ancestry_of_external initSM initPM hSM hPM hInit hContract)

end
end TrainVerify.Denote.GeneratedPatterns
