/- Auto-generated pattern proof file.
   Pattern: 19
   Hash: 079c368d91506bb2
   Goals: 23, 26, 51, 53, 106

   Structural argument:
     Each SM graph is a single `FW_linear` node producing
       y_SM :: [B, S, full_o]  from  x :: [B, S, i]  and  w :: [full_o, i].
     Each PM graph has four `FW_linear` nodes, one per rank, producing per-rank
       y_PM_r :: [B, S, shard_o].

       x_SM       = x_PM_r for every r          (singleton prereq)
       w_SM       = allGatherPrimDimN 0 4 0 [w_PM_0..3]   (initGoal)
       y_SM       = allGatherPrimDimN 2 4 0 [y_PM_0..3]   (this goal)

     We bridge via `fw_linear_3d_allGatherPrimDimN0_w_comm`:
       fw_linear x (allGather W on dim 0) = allGather (per-rank fw_linear) on dim 2
-/
import denote.gpt_ly4_segments.GeneratedData
import denote.gpt_ly4_segments.Pattern_18
import denote.gpt_ly4_segments.Pattern_21
import denote.gpt_ly4_segments.Pattern_35

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_19_goalIds : List Nat := [23, 26, 51, 53, 106]
inductive pattern_19_target : Prop → Prop
  | goal_23 : pattern_19_target goal_23_stmt
  | goal_26 : pattern_19_target goal_26_stmt
  | goal_51 : pattern_19_target goal_51_stmt
  | goal_53 : pattern_19_target goal_53_stmt
  | goal_106 : pattern_19_target goal_106_stmt

def pattern_19_stmt : Prop :=
  ∀ {target : Prop}, pattern_19_target target → target

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000000

/-! ## Generic graph-evaluation helpers. -/

private theorem denote_init_tid (g : GraphDecl) (init : Store) (tid : Tid)
    (hno : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraph g init tid = init tid := by
  have h := denoteGraph_tid_eq_of_suffix_no_writes g init tid
    [] g.nodes (by simp) hno
  rw [h]
  have heq : ({ g with nodes := [] } : GraphDecl) =
      { numRanks := g.numRanks, nodes := [] } := by cases g; rfl
  rw [heq, denoteGraph_nodes_nil]

private theorem pm_eval_fw_linear_at
    (g : GraphDecl) (initPM : Store) (K : Nat) (rk : Nat)
    (xTid wTid outTid : Tid)
    (node : NodeDecl)
    (hnode : node = { rank := rk, op := "OpName.FW_linear",
                        ins := [xTid, wTid], outs := [outTid] })
    (hKlt : K < g.nodes.length)
    (hidx : g.nodes[K]'hKlt = node)
    (hsuf_o : ∀ n ∈ g.nodes.drop (K + 1), outTid ∉ n.outs)
    (hsuf_x : ∀ n ∈ g.nodes.drop K, xTid ∉ n.outs)
    (hsuf_w : ∀ n ∈ g.nodes.drop K, wTid ∉ n.outs) :
    denoteGraph g initPM outTid =
      fw_linear (denoteGraph g initPM xTid) (denoteGraph g initPM wTid) := by
  have h1 : denoteGraph g initPM outTid =
      denoteGraph { g with nodes := g.nodes.take (K + 1) } initPM outTid :=
    denoteGraph_tid_eq_of_suffix_no_writes g initPM outTid
      (g.nodes.take (K + 1)) (g.nodes.drop (K + 1))
      (List.take_append_drop (K + 1) _).symm hsuf_o
  rw [h1]
  have htake : g.nodes.take (K + 1) = g.nodes.take K ++ [node] := by
    rw [list_take_succ_eq_take_append_get g.nodes K hKlt, hidx]
  have hg_eq : ({ g with nodes := g.nodes.take (K + 1) } : GraphDecl) =
      { g with nodes := g.nodes.take K ++ [node] } := by
    cases g; congr 1
  rw [hg_eq, denoteGraph_nodes_append]
  have hsing : ({ g with nodes := [node] } : GraphDecl) =
      { numRanks := g.numRanks, nodes := node :: [] } := by cases g; rfl
  rw [hsing, denoteGraph_cons_eq g node []]
  change applyNode g (denoteGraph { g with nodes := g.nodes.take K } initPM) node outTid = _
  rw [hnode]
  rw [applyNode_fw_linear_out g _ rk xTid wTid outTid]
  have hpre_x : (denoteGraph { g with nodes := g.nodes.take K } initPM) xTid =
      denoteGraph g initPM xTid :=
    (denoteGraph_tid_eq_of_suffix_no_writes g initPM xTid
      (g.nodes.take K) (g.nodes.drop K)
      (List.take_append_drop K _).symm hsuf_x).symm
  have hpre_w : (denoteGraph { g with nodes := g.nodes.take K } initPM) wTid =
      denoteGraph g initPM wTid :=
    (denoteGraph_tid_eq_of_suffix_no_writes g initPM wTid
      (g.nodes.take K) (g.nodes.drop K)
      (List.take_append_drop K _).symm hsuf_w).symm
  rw [hpre_x, hpre_w]

/-! ## Bridge specialization to `numParts = 4` (literal 4-element lists). -/

private theorem bridge_fw_w_4
    (b s i shard : Nat)
    (x w0 w1 w2 w3 : Tensor)
    (hx : x.shape = [b, s, i])
    (hw0 : w0.shape = [shard, i]) (hw1 : w1.shape = [shard, i])
    (hw2 : w2.shape = [shard, i]) (hw3 : w3.shape = [shard, i])
    (hb : 0 < b) (hs : 0 < s) (hi : 0 < i) (hshard : 0 < shard) :
    fw_linear x (allGatherPrimDimN 0 4 0 [w0, w1, w2, w3]) =
      allGatherPrimDimN 2 4 0
        [fw_linear x w0, fw_linear x w1, fw_linear x w2, fw_linear x w3] := by
  have hws_shapes : ∀ w ∈ ([w0, w1, w2, w3] : List Tensor), w.shape = [shard, i] := by
    intro w hw
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
    rcases hw with h | h | h | h
    · rw [h]; exact hw0
    · rw [h]; exact hw1
    · rw [h]; exact hw2
    · rw [h]; exact hw3
  have hws_head : (([w0, w1, w2, w3] : List Tensor).head?.map (fun t => t.shape)).getD []
      = [shard, i] := by
    simp [hw0]
  have h := fw_linear_3d_allGatherPrimDimN0_w_comm 4 b s i shard x [w0, w1, w2, w3]
    hx hws_head hws_shapes rfl (by decide) hb hs hi hshard
  rw [h]
  rfl

/-! ## Per-goal SM and PM node literals. -/

@[reducible] private def sm_n23 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [590, 591], outs := [592] }
@[reducible] private def pm_n23_0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [590, 1473], outs := [1477] }
@[reducible] private def pm_n23_1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_linear", ins := [590, 1474], outs := [1478] }
@[reducible] private def pm_n23_2 : NodeDecl :=
  { rank := 2, op := "OpName.FW_linear", ins := [590, 1475], outs := [1479] }
@[reducible] private def pm_n23_3 : NodeDecl :=
  { rank := 3, op := "OpName.FW_linear", ins := [590, 1476], outs := [1480] }

@[reducible] private def sm_n26 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [596, 597], outs := [598] }
@[reducible] private def pm_n26_0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [596, 1557], outs := [1561] }
@[reducible] private def pm_n26_1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_linear", ins := [596, 1558], outs := [1562] }
@[reducible] private def pm_n26_2 : NodeDecl :=
  { rank := 2, op := "OpName.FW_linear", ins := [596, 1559], outs := [1563] }
@[reducible] private def pm_n26_3 : NodeDecl :=
  { rank := 3, op := "OpName.FW_linear", ins := [596, 1560], outs := [1564] }

@[reducible] private def sm_n51 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [631, 632], outs := [633] }
@[reducible] private def pm_n51_0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [631, 2113], outs := [2117] }
@[reducible] private def pm_n51_1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_linear", ins := [631, 2114], outs := [2118] }
@[reducible] private def pm_n51_2 : NodeDecl :=
  { rank := 2, op := "OpName.FW_linear", ins := [631, 2115], outs := [2119] }
@[reducible] private def pm_n51_3 : NodeDecl :=
  { rank := 3, op := "OpName.FW_linear", ins := [631, 2116], outs := [2120] }

@[reducible] private def sm_n53 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [634, 635], outs := [636] }
@[reducible] private def pm_n53_0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [634, 2165], outs := [2169] }
@[reducible] private def pm_n53_1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_linear", ins := [634, 2166], outs := [2170] }
@[reducible] private def pm_n53_2 : NodeDecl :=
  { rank := 2, op := "OpName.FW_linear", ins := [634, 2167], outs := [2171] }
@[reducible] private def pm_n53_3 : NodeDecl :=
  { rank := 3, op := "OpName.FW_linear", ins := [634, 2168], outs := [2172] }

@[reducible] private def sm_n106 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [710, 711], outs := [712] }
@[reducible] private def pm_n106_0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_linear", ins := [710, 3369], outs := [3373] }
@[reducible] private def pm_n106_1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_linear", ins := [710, 3370], outs := [3374] }
@[reducible] private def pm_n106_2 : NodeDecl :=
  { rank := 2, op := "OpName.FW_linear", ins := [710, 3371], outs := [3375] }
@[reducible] private def pm_n106_3 : NodeDecl :=
  { rank := 3, op := "OpName.FW_linear", ins := [710, 3372], outs := [3376] }

/-! ## SM evaluation helpers. -/

private theorem sm_eval_592 (initSM : Store) :
    denoteGraph sm initSM 592 =
      fw_linear (denoteGraph sm initSM 590) (denoteGraph sm initSM 591) :=
  pm_eval_fw_linear_at sm initSM 23 0 590 591 592 sm_n23 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

private theorem sm_eval_598 (initSM : Store) :
    denoteGraph sm initSM 598 =
      fw_linear (denoteGraph sm initSM 596) (denoteGraph sm initSM 597) :=
  pm_eval_fw_linear_at sm initSM 27 0 596 597 598 sm_n26 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

private theorem sm_eval_633 (initSM : Store) :
    denoteGraph sm initSM 633 =
      fw_linear (denoteGraph sm initSM 631) (denoteGraph sm initSM 632) :=
  pm_eval_fw_linear_at sm initSM 55 0 631 632 633 sm_n51 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

private theorem sm_eval_636 (initSM : Store) :
    denoteGraph sm initSM 636 =
      fw_linear (denoteGraph sm initSM 634) (denoteGraph sm initSM 635) :=
  pm_eval_fw_linear_at sm initSM 57 0 634 635 636 sm_n53 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

private theorem sm_eval_712 (initSM : Store) :
    denoteGraph sm initSM 712 =
      fw_linear (denoteGraph sm initSM 710) (denoteGraph sm initSM 711) :=
  pm_eval_fw_linear_at sm initSM 116 0 710 711 712 sm_n106 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

/-! ## PM evaluation helpers (one per shard per goal). -/

private theorem pm_eval_1477 (initPM : Store) :
    denoteGraph pm initPM 1477 =
      fw_linear (denoteGraph pm initPM 590) (denoteGraph pm initPM 1473) :=
  pm_eval_fw_linear_at pm initPM 144 0 590 1473 1477 pm_n23_0 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

private theorem pm_eval_1478 (initPM : Store) :
    denoteGraph pm initPM 1478 =
      fw_linear (denoteGraph pm initPM 590) (denoteGraph pm initPM 1474) :=
  pm_eval_fw_linear_at pm initPM 145 1 590 1474 1478 pm_n23_1 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

private theorem pm_eval_1479 (initPM : Store) :
    denoteGraph pm initPM 1479 =
      fw_linear (denoteGraph pm initPM 590) (denoteGraph pm initPM 1475) :=
  pm_eval_fw_linear_at pm initPM 146 2 590 1475 1479 pm_n23_2 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

private theorem pm_eval_1480 (initPM : Store) :
    denoteGraph pm initPM 1480 =
      fw_linear (denoteGraph pm initPM 590) (denoteGraph pm initPM 1476) :=
  pm_eval_fw_linear_at pm initPM 147 3 590 1476 1480 pm_n23_3 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

private theorem pm_eval_1561 (initPM : Store) :
    denoteGraph pm initPM 1561 =
      fw_linear (denoteGraph pm initPM 596) (denoteGraph pm initPM 1557) :=
  pm_eval_fw_linear_at pm initPM 165 0 596 1557 1561 pm_n26_0 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

private theorem pm_eval_1562 (initPM : Store) :
    denoteGraph pm initPM 1562 =
      fw_linear (denoteGraph pm initPM 596) (denoteGraph pm initPM 1558) :=
  pm_eval_fw_linear_at pm initPM 166 1 596 1558 1562 pm_n26_1 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

private theorem pm_eval_1563 (initPM : Store) :
    denoteGraph pm initPM 1563 =
      fw_linear (denoteGraph pm initPM 596) (denoteGraph pm initPM 1559) :=
  pm_eval_fw_linear_at pm initPM 167 2 596 1559 1563 pm_n26_2 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

private theorem pm_eval_1564 (initPM : Store) :
    denoteGraph pm initPM 1564 =
      fw_linear (denoteGraph pm initPM 596) (denoteGraph pm initPM 1560) :=
  pm_eval_fw_linear_at pm initPM 168 3 596 1560 1564 pm_n26_3 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

private theorem pm_eval_2117 (initPM : Store) :
    denoteGraph pm initPM 2117 =
      fw_linear (denoteGraph pm initPM 631) (denoteGraph pm initPM 2113) :=
  pm_eval_fw_linear_at pm initPM 363 0 631 2113 2117 pm_n51_0 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

private theorem pm_eval_2118 (initPM : Store) :
    denoteGraph pm initPM 2118 =
      fw_linear (denoteGraph pm initPM 631) (denoteGraph pm initPM 2114) :=
  pm_eval_fw_linear_at pm initPM 364 1 631 2114 2118 pm_n51_1 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

private theorem pm_eval_2119 (initPM : Store) :
    denoteGraph pm initPM 2119 =
      fw_linear (denoteGraph pm initPM 631) (denoteGraph pm initPM 2115) :=
  pm_eval_fw_linear_at pm initPM 365 2 631 2115 2119 pm_n51_2 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

private theorem pm_eval_2120 (initPM : Store) :
    denoteGraph pm initPM 2120 =
      fw_linear (denoteGraph pm initPM 631) (denoteGraph pm initPM 2116) :=
  pm_eval_fw_linear_at pm initPM 366 3 631 2116 2120 pm_n51_3 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

private theorem pm_eval_2169 (initPM : Store) :
    denoteGraph pm initPM 2169 =
      fw_linear (denoteGraph pm initPM 634) (denoteGraph pm initPM 2165) :=
  pm_eval_fw_linear_at pm initPM 376 0 634 2165 2169 pm_n53_0 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

private theorem pm_eval_2170 (initPM : Store) :
    denoteGraph pm initPM 2170 =
      fw_linear (denoteGraph pm initPM 634) (denoteGraph pm initPM 2166) :=
  pm_eval_fw_linear_at pm initPM 377 1 634 2166 2170 pm_n53_1 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

private theorem pm_eval_2171 (initPM : Store) :
    denoteGraph pm initPM 2171 =
      fw_linear (denoteGraph pm initPM 634) (denoteGraph pm initPM 2167) :=
  pm_eval_fw_linear_at pm initPM 378 2 634 2167 2171 pm_n53_2 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

private theorem pm_eval_2172 (initPM : Store) :
    denoteGraph pm initPM 2172 =
      fw_linear (denoteGraph pm initPM 634) (denoteGraph pm initPM 2168) :=
  pm_eval_fw_linear_at pm initPM 379 3 634 2168 2172 pm_n53_3 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

private theorem pm_eval_3373 (initPM : Store) :
    denoteGraph pm initPM 3373 =
      fw_linear (denoteGraph pm initPM 710) (denoteGraph pm initPM 3369) :=
  pm_eval_fw_linear_at pm initPM 767 0 710 3369 3373 pm_n106_0 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

private theorem pm_eval_3374 (initPM : Store) :
    denoteGraph pm initPM 3374 =
      fw_linear (denoteGraph pm initPM 710) (denoteGraph pm initPM 3370) :=
  pm_eval_fw_linear_at pm initPM 768 1 710 3370 3374 pm_n106_1 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

private theorem pm_eval_3375 (initPM : Store) :
    denoteGraph pm initPM 3375 =
      fw_linear (denoteGraph pm initPM 710) (denoteGraph pm initPM 3371) :=
  pm_eval_fw_linear_at pm initPM 769 2 710 3371 3375 pm_n106_2 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

private theorem pm_eval_3376 (initPM : Store) :
    denoteGraph pm initPM 3376 =
      fw_linear (denoteGraph pm initPM 710) (denoteGraph pm initPM 3372) :=
  pm_eval_fw_linear_at pm initPM 770 3 710 3372 3376 pm_n106_3 rfl
    (by decide) rfl (by decide) (by decide) (by decide)

/-! ## Per-goal proofs for `pattern_19`. -/

private theorem prove_goal_23 :
    ∀ (initSM initPM : Store),
      StoreShapesHold initSM smInitEnv → StoreShapesHold initPM pmInitEnv →
      InitGoalsHold pm.numRanks initGoals initSM initPM →
      let smStore := denoteGraph sm initSM
      let pmStore := denoteGraph pm initPM
      (smStore goal_23.ts).shape = goal_23.tsShape ∧
        ((goal_23.tps.map (fun p => pmStore p.tid)).map (·.shape)) = goal_23.tpShapes ∧
        smStore goal_23.ts =
          reconstructWithDim goal_23.gatherDim pm.numRanks 0
            (goal_23.tps.map (fun p => pmStore p.tid)) := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- x prereq (goal_22 ↦ Pattern_18, singleton)
  have h22 := prove_pattern_18 (target := goal_22_stmt) pattern_18_target.goal_22
    initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h590_sh, _, h590_rec⟩ := h22
  simp only [goal_22, List.map_cons, List.map_nil, reconstructWithDim_singleton] at h590_rec
  have h590_sh' : (denoteGraph sm initSM 590).shape = [1, 8, 32] := by
    have := h590_sh; simp only [goal_22] at this; exact this
  -- weight initGoal_591
  have h591_init := hInitGoals initGoal_591 (by simp [initGoals])
  obtain ⟨h591_sh, hw_sh, h591_rec⟩ := h591_init
  simp only [initGoal_591, List.map_cons, List.map_nil] at h591_rec hw_sh
  have hwr0_sh : (initPM 1473).shape = [8, 32] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.1
  have hwr1_sh : (initPM 1474).shape = [8, 32] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.1
  have hwr2_sh : (initPM 1475).shape = [8, 32] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.1
  have hwr3_sh : (initPM 1476).shape = [8, 32] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  have h591_dimN : initSM 591 = allGatherPrimDimN 0 pm.numRanks 0
      [initPM 1473, initPM 1474, initPM 1475, initPM 1476] := by
    rw [h591_rec]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [hwr0_sh]; intro hc; cases hc
  -- Lift 591 / 1473-1476 / 590 from init store to denoteGraph.
  have hsm591 : denoteGraph sm initSM 591 = initSM 591 :=
    denote_init_tid sm initSM 591 (by decide)
  have hpm1473 : denoteGraph pm initPM 1473 = initPM 1473 :=
    denote_init_tid pm initPM 1473 (by decide)
  have hpm1474 : denoteGraph pm initPM 1474 = initPM 1474 :=
    denote_init_tid pm initPM 1474 (by decide)
  have hpm1475 : denoteGraph pm initPM 1475 = initPM 1475 :=
    denote_init_tid pm initPM 1475 (by decide)
  have hpm1476 : denoteGraph pm initPM 1476 = initPM 1476 :=
    denote_init_tid pm initPM 1476 (by decide)
  -- sm / pm evaluations
  have hS := sm_eval_592 initSM
  have hP0 := pm_eval_1477 initPM
  have hP1 := pm_eval_1478 initPM
  have hP2 := pm_eval_1479 initPM
  have hP3 := pm_eval_1480 initPM
  -- weight shapes lifted to denoteGraph
  have h591_sh' : (denoteGraph sm initSM 591).shape = [32, 32] := by
    rw [hsm591]
    have := h591_sh; simp only [initGoal_591] at this; exact this
  have hwr0_pm_sh : (denoteGraph pm initPM 1473).shape = [8, 32] := by
    rw [hpm1473]; exact hwr0_sh
  have hwr1_pm_sh : (denoteGraph pm initPM 1474).shape = [8, 32] := by
    rw [hpm1474]; exact hwr1_sh
  have hwr2_pm_sh : (denoteGraph pm initPM 1475).shape = [8, 32] := by
    rw [hpm1475]; exact hwr2_sh
  have hwr3_pm_sh : (denoteGraph pm initPM 1476).shape = [8, 32] := by
    rw [hpm1476]; exact hwr3_sh
  -- x shape on pm side (singleton ⇒ pm 590 has same value/shape as sm 590)
  have h590_pm_sh : (denoteGraph pm initPM 590).shape = [1, 8, 32] := by
    rw [← h590_rec]; exact h590_sh'
  -- bridge_fw_w_4 application: full_o = 8 * 4 = 32
  have hbridge := bridge_fw_w_4 1 8 32 8
      (denoteGraph pm initPM 590)
      (denoteGraph pm initPM 1473) (denoteGraph pm initPM 1474)
      (denoteGraph pm initPM 1475) (denoteGraph pm initPM 1476)
      h590_pm_sh hwr0_pm_sh hwr1_pm_sh hwr2_pm_sh hwr3_pm_sh
      (by decide) (by decide) (by decide) (by decide)
  -- LHS shape: fw_linear (sm 590) (sm 591) of shapes [1,8,32] and [32,32] → [1,8,32]
  have hLHS_sh : (denoteGraph sm initSM 592).shape = [1, 8, 32] := by
    rw [hS]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h590_sh', h591_sh']
    rfl
  have hP0_sh : (denoteGraph pm initPM 1477).shape = [1, 8, 8] := by
    rw [hP0]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h590_pm_sh, hwr0_pm_sh]
    rfl
  have hP1_sh : (denoteGraph pm initPM 1478).shape = [1, 8, 8] := by
    rw [hP1]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h590_pm_sh, hwr1_pm_sh]
    rfl
  have hP2_sh : (denoteGraph pm initPM 1479).shape = [1, 8, 8] := by
    rw [hP2]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h590_pm_sh, hwr2_pm_sh]
    rfl
  have hP3_sh : (denoteGraph pm initPM 1480).shape = [1, 8, 8] := by
    rw [hP3]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h590_pm_sh, hwr3_pm_sh]
    rfl
  have hnr : pm.numRanks = 4 := rfl
  -- denoteGraph sm 591 = allGatherPrimDimN 0 4 0 [pm 1473..1476]
  have hsm591_dimN4 : denoteGraph sm initSM 591 = allGatherPrimDimN 0 4 0
      [denoteGraph pm initPM 1473, denoteGraph pm initPM 1474,
       denoteGraph pm initPM 1475, denoteGraph pm initPM 1476] := by
    rw [hsm591, h591_dimN, hnr, hpm1473, hpm1474, hpm1475, hpm1476]
  -- The final reconstruction equation
  have hreco : denoteGraph sm initSM 592 = allGatherPrimDimN 2 4 0
      [denoteGraph pm initPM 1477, denoteGraph pm initPM 1478,
       denoteGraph pm initPM 1479, denoteGraph pm initPM 1480] := by
    rw [hS, h590_rec, hsm591_dimN4, hbridge, ← hP0, ← hP1, ← hP2, ← hP3]
  refine ⟨?_, ?_, ?_⟩
  · show (denoteGraph sm initSM 592).shape = [1, 8, 32]; exact hLHS_sh
  · show List.map (fun t => Tensor.shape t)
        ([({ rank := 0, tid := 1477 } : Piece),
          ({ rank := 1, tid := 1478 } : Piece),
          ({ rank := 2, tid := 1479 } : Piece),
          ({ rank := 3, tid := 1480 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) =
        [[1, 8, 8], [1, 8, 8], [1, 8, 8], [1, 8, 8]]
    simp only [List.map_cons, List.map_nil]
    rw [hP0_sh, hP1_sh, hP2_sh, hP3_sh]
  · show denoteGraph sm initSM 592 =
        reconstructWithDim 2 pm.numRanks 0
          ([({ rank := 0, tid := 1477 } : Piece),
            ({ rank := 1, tid := 1478 } : Piece),
            ({ rank := 2, tid := 1479 } : Piece),
            ({ rank := 3, tid := 1480 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
    simp only [List.map_cons, List.map_nil]
    rw [hnr]
    rw [reconstructWithDim_cons_cons_nonscalar 2 4 0 _ _ _
        (by rw [hP0_sh]; intro hc; cases hc)]
    exact hreco

private theorem prove_goal_26 :
    ∀ (initSM initPM : Store),
      StoreShapesHold initSM smInitEnv → StoreShapesHold initPM pmInitEnv →
      InitGoalsHold pm.numRanks initGoals initSM initPM →
      let smStore := denoteGraph sm initSM
      let pmStore := denoteGraph pm initPM
      (smStore goal_26.ts).shape = goal_26.tsShape ∧
        ((goal_26.tps.map (fun p => pmStore p.tid)).map (·.shape)) = goal_26.tpShapes ∧
        smStore goal_26.ts =
          reconstructWithDim goal_26.gatherDim pm.numRanks 0
            (goal_26.tps.map (fun p => pmStore p.tid)) := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- x prereq (goal_25 ↦ Pattern_21, singleton)
  have h25 := prove_pattern_21 (target := goal_25_stmt) pattern_21_target.goal_25
    initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h596_sh, _, h596_rec⟩ := h25
  simp only [goal_25, List.map_cons, List.map_nil, reconstructWithDim_singleton] at h596_rec
  have h596_sh' : (denoteGraph sm initSM 596).shape = [1, 8, 32] := by
    have := h596_sh; simp only [goal_25] at this; exact this
  -- weight initGoal_597
  have h597_init := hInitGoals initGoal_597 (by simp [initGoals])
  obtain ⟨h597_sh, hw_sh, h597_rec⟩ := h597_init
  simp only [initGoal_597, List.map_cons, List.map_nil] at h597_rec hw_sh
  have hwr0_sh : (initPM 1557).shape = [32, 32] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.1
  have hwr1_sh : (initPM 1558).shape = [32, 32] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.1
  have hwr2_sh : (initPM 1559).shape = [32, 32] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.1
  have hwr3_sh : (initPM 1560).shape = [32, 32] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  have h597_dimN : initSM 597 = allGatherPrimDimN 0 pm.numRanks 0
      [initPM 1557, initPM 1558, initPM 1559, initPM 1560] := by
    rw [h597_rec]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [hwr0_sh]; intro hc; cases hc
  have hsm597 : denoteGraph sm initSM 597 = initSM 597 :=
    denote_init_tid sm initSM 597 (by decide)
  have hpm1557 : denoteGraph pm initPM 1557 = initPM 1557 :=
    denote_init_tid pm initPM 1557 (by decide)
  have hpm1558 : denoteGraph pm initPM 1558 = initPM 1558 :=
    denote_init_tid pm initPM 1558 (by decide)
  have hpm1559 : denoteGraph pm initPM 1559 = initPM 1559 :=
    denote_init_tid pm initPM 1559 (by decide)
  have hpm1560 : denoteGraph pm initPM 1560 = initPM 1560 :=
    denote_init_tid pm initPM 1560 (by decide)
  have hS := sm_eval_598 initSM
  have hP0 := pm_eval_1561 initPM
  have hP1 := pm_eval_1562 initPM
  have hP2 := pm_eval_1563 initPM
  have hP3 := pm_eval_1564 initPM
  have h597_sh' : (denoteGraph sm initSM 597).shape = [128, 32] := by
    rw [hsm597]
    have := h597_sh; simp only [initGoal_597] at this; exact this
  have hwr0_pm_sh : (denoteGraph pm initPM 1557).shape = [32, 32] := by
    rw [hpm1557]; exact hwr0_sh
  have hwr1_pm_sh : (denoteGraph pm initPM 1558).shape = [32, 32] := by
    rw [hpm1558]; exact hwr1_sh
  have hwr2_pm_sh : (denoteGraph pm initPM 1559).shape = [32, 32] := by
    rw [hpm1559]; exact hwr2_sh
  have hwr3_pm_sh : (denoteGraph pm initPM 1560).shape = [32, 32] := by
    rw [hpm1560]; exact hwr3_sh
  have h596_pm_sh : (denoteGraph pm initPM 596).shape = [1, 8, 32] := by
    rw [← h596_rec]; exact h596_sh'
  have hbridge := bridge_fw_w_4 1 8 32 32
      (denoteGraph pm initPM 596)
      (denoteGraph pm initPM 1557) (denoteGraph pm initPM 1558)
      (denoteGraph pm initPM 1559) (denoteGraph pm initPM 1560)
      h596_pm_sh hwr0_pm_sh hwr1_pm_sh hwr2_pm_sh hwr3_pm_sh
      (by decide) (by decide) (by decide) (by decide)
  have hLHS_sh : (denoteGraph sm initSM 598).shape = [1, 8, 128] := by
    rw [hS]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h596_sh', h597_sh']
    rfl
  have hP0_sh : (denoteGraph pm initPM 1561).shape = [1, 8, 32] := by
    rw [hP0]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h596_pm_sh, hwr0_pm_sh]
    rfl
  have hP1_sh : (denoteGraph pm initPM 1562).shape = [1, 8, 32] := by
    rw [hP1]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h596_pm_sh, hwr1_pm_sh]
    rfl
  have hP2_sh : (denoteGraph pm initPM 1563).shape = [1, 8, 32] := by
    rw [hP2]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h596_pm_sh, hwr2_pm_sh]
    rfl
  have hP3_sh : (denoteGraph pm initPM 1564).shape = [1, 8, 32] := by
    rw [hP3]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h596_pm_sh, hwr3_pm_sh]
    rfl
  have hnr : pm.numRanks = 4 := rfl
  have hsm597_dimN4 : denoteGraph sm initSM 597 = allGatherPrimDimN 0 4 0
      [denoteGraph pm initPM 1557, denoteGraph pm initPM 1558,
       denoteGraph pm initPM 1559, denoteGraph pm initPM 1560] := by
    rw [hsm597, h597_dimN, hnr, hpm1557, hpm1558, hpm1559, hpm1560]
  have hreco : denoteGraph sm initSM 598 = allGatherPrimDimN 2 4 0
      [denoteGraph pm initPM 1561, denoteGraph pm initPM 1562,
       denoteGraph pm initPM 1563, denoteGraph pm initPM 1564] := by
    rw [hS, h596_rec, hsm597_dimN4, hbridge, ← hP0, ← hP1, ← hP2, ← hP3]
  refine ⟨?_, ?_, ?_⟩
  · show (denoteGraph sm initSM 598).shape = [1, 8, 128]; exact hLHS_sh
  · show List.map (fun t => Tensor.shape t)
        ([({ rank := 0, tid := 1561 } : Piece),
          ({ rank := 1, tid := 1562 } : Piece),
          ({ rank := 2, tid := 1563 } : Piece),
          ({ rank := 3, tid := 1564 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) =
        [[1, 8, 32], [1, 8, 32], [1, 8, 32], [1, 8, 32]]
    simp only [List.map_cons, List.map_nil]
    rw [hP0_sh, hP1_sh, hP2_sh, hP3_sh]
  · show denoteGraph sm initSM 598 =
        reconstructWithDim 2 pm.numRanks 0
          ([({ rank := 0, tid := 1561 } : Piece),
            ({ rank := 1, tid := 1562 } : Piece),
            ({ rank := 2, tid := 1563 } : Piece),
            ({ rank := 3, tid := 1564 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
    simp only [List.map_cons, List.map_nil]
    rw [hnr]
    rw [reconstructWithDim_cons_cons_nonscalar 2 4 0 _ _ _
        (by rw [hP0_sh]; intro hc; cases hc)]
    exact hreco

private theorem prove_goal_51 :
    ∀ (initSM initPM : Store),
      StoreShapesHold initSM smInitEnv → StoreShapesHold initPM pmInitEnv →
      InitGoalsHold pm.numRanks initGoals initSM initPM →
      let smStore := denoteGraph sm initSM
      let pmStore := denoteGraph pm initPM
      (smStore goal_51.ts).shape = goal_51.tsShape ∧
        ((goal_51.tps.map (fun p => pmStore p.tid)).map (·.shape)) = goal_51.tpShapes ∧
        smStore goal_51.ts =
          reconstructWithDim goal_51.gatherDim pm.numRanks 0
            (goal_51.tps.map (fun p => pmStore p.tid)) := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- x prereq (goal_50 ↦ Pattern_21, singleton)
  have h50 := prove_pattern_21 (target := goal_50_stmt) pattern_21_target.goal_50
    initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h631_sh, _, h631_rec⟩ := h50
  simp only [goal_50, List.map_cons, List.map_nil, reconstructWithDim_singleton] at h631_rec
  have h631_sh' : (denoteGraph sm initSM 631).shape = [1, 8, 32] := by
    have := h631_sh; simp only [goal_50] at this; exact this
  -- weight initGoal_632
  have h632_init := hInitGoals initGoal_632 (by simp [initGoals])
  obtain ⟨h632_sh, hw_sh, h632_rec⟩ := h632_init
  simp only [initGoal_632, List.map_cons, List.map_nil] at h632_rec hw_sh
  have hwr0_sh : (initPM 2113).shape = [32, 32] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.1
  have hwr1_sh : (initPM 2114).shape = [32, 32] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.1
  have hwr2_sh : (initPM 2115).shape = [32, 32] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.1
  have hwr3_sh : (initPM 2116).shape = [32, 32] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  have h632_dimN : initSM 632 = allGatherPrimDimN 0 pm.numRanks 0
      [initPM 2113, initPM 2114, initPM 2115, initPM 2116] := by
    rw [h632_rec]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [hwr0_sh]; intro hc; cases hc
  have hsm632 : denoteGraph sm initSM 632 = initSM 632 :=
    denote_init_tid sm initSM 632 (by decide)
  have hpm2113 : denoteGraph pm initPM 2113 = initPM 2113 :=
    denote_init_tid pm initPM 2113 (by decide)
  have hpm2114 : denoteGraph pm initPM 2114 = initPM 2114 :=
    denote_init_tid pm initPM 2114 (by decide)
  have hpm2115 : denoteGraph pm initPM 2115 = initPM 2115 :=
    denote_init_tid pm initPM 2115 (by decide)
  have hpm2116 : denoteGraph pm initPM 2116 = initPM 2116 :=
    denote_init_tid pm initPM 2116 (by decide)
  have hS := sm_eval_633 initSM
  have hP0 := pm_eval_2117 initPM
  have hP1 := pm_eval_2118 initPM
  have hP2 := pm_eval_2119 initPM
  have hP3 := pm_eval_2120 initPM
  have h632_sh' : (denoteGraph sm initSM 632).shape = [128, 32] := by
    rw [hsm632]
    have := h632_sh; simp only [initGoal_632] at this; exact this
  have hwr0_pm_sh : (denoteGraph pm initPM 2113).shape = [32, 32] := by
    rw [hpm2113]; exact hwr0_sh
  have hwr1_pm_sh : (denoteGraph pm initPM 2114).shape = [32, 32] := by
    rw [hpm2114]; exact hwr1_sh
  have hwr2_pm_sh : (denoteGraph pm initPM 2115).shape = [32, 32] := by
    rw [hpm2115]; exact hwr2_sh
  have hwr3_pm_sh : (denoteGraph pm initPM 2116).shape = [32, 32] := by
    rw [hpm2116]; exact hwr3_sh
  have h631_pm_sh : (denoteGraph pm initPM 631).shape = [1, 8, 32] := by
    rw [← h631_rec]; exact h631_sh'
  have hbridge := bridge_fw_w_4 1 8 32 32
      (denoteGraph pm initPM 631)
      (denoteGraph pm initPM 2113) (denoteGraph pm initPM 2114)
      (denoteGraph pm initPM 2115) (denoteGraph pm initPM 2116)
      h631_pm_sh hwr0_pm_sh hwr1_pm_sh hwr2_pm_sh hwr3_pm_sh
      (by decide) (by decide) (by decide) (by decide)
  have hLHS_sh : (denoteGraph sm initSM 633).shape = [1, 8, 128] := by
    rw [hS]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h631_sh', h632_sh']
    rfl
  have hP0_sh : (denoteGraph pm initPM 2117).shape = [1, 8, 32] := by
    rw [hP0]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h631_pm_sh, hwr0_pm_sh]
    rfl
  have hP1_sh : (denoteGraph pm initPM 2118).shape = [1, 8, 32] := by
    rw [hP1]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h631_pm_sh, hwr1_pm_sh]
    rfl
  have hP2_sh : (denoteGraph pm initPM 2119).shape = [1, 8, 32] := by
    rw [hP2]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h631_pm_sh, hwr2_pm_sh]
    rfl
  have hP3_sh : (denoteGraph pm initPM 2120).shape = [1, 8, 32] := by
    rw [hP3]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h631_pm_sh, hwr3_pm_sh]
    rfl
  have hnr : pm.numRanks = 4 := rfl
  have hsm632_dimN4 : denoteGraph sm initSM 632 = allGatherPrimDimN 0 4 0
      [denoteGraph pm initPM 2113, denoteGraph pm initPM 2114,
       denoteGraph pm initPM 2115, denoteGraph pm initPM 2116] := by
    rw [hsm632, h632_dimN, hnr, hpm2113, hpm2114, hpm2115, hpm2116]
  have hreco : denoteGraph sm initSM 633 = allGatherPrimDimN 2 4 0
      [denoteGraph pm initPM 2117, denoteGraph pm initPM 2118,
       denoteGraph pm initPM 2119, denoteGraph pm initPM 2120] := by
    rw [hS, h631_rec, hsm632_dimN4, hbridge, ← hP0, ← hP1, ← hP2, ← hP3]
  refine ⟨?_, ?_, ?_⟩
  · show (denoteGraph sm initSM 633).shape = [1, 8, 128]; exact hLHS_sh
  · show List.map (fun t => Tensor.shape t)
        ([({ rank := 0, tid := 2117 } : Piece),
          ({ rank := 1, tid := 2118 } : Piece),
          ({ rank := 2, tid := 2119 } : Piece),
          ({ rank := 3, tid := 2120 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) =
        [[1, 8, 32], [1, 8, 32], [1, 8, 32], [1, 8, 32]]
    simp only [List.map_cons, List.map_nil]
    rw [hP0_sh, hP1_sh, hP2_sh, hP3_sh]
  · show denoteGraph sm initSM 633 =
        reconstructWithDim 2 pm.numRanks 0
          ([({ rank := 0, tid := 2117 } : Piece),
            ({ rank := 1, tid := 2118 } : Piece),
            ({ rank := 2, tid := 2119 } : Piece),
            ({ rank := 3, tid := 2120 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
    simp only [List.map_cons, List.map_nil]
    rw [hnr]
    rw [reconstructWithDim_cons_cons_nonscalar 2 4 0 _ _ _
        (by rw [hP0_sh]; intro hc; cases hc)]
    exact hreco

private theorem prove_goal_53 :
    ∀ (initSM initPM : Store),
      StoreShapesHold initSM smInitEnv → StoreShapesHold initPM pmInitEnv →
      InitGoalsHold pm.numRanks initGoals initSM initPM →
      let smStore := denoteGraph sm initSM
      let pmStore := denoteGraph pm initPM
      (smStore goal_53.ts).shape = goal_53.tsShape ∧
        ((goal_53.tps.map (fun p => pmStore p.tid)).map (·.shape)) = goal_53.tpShapes ∧
        smStore goal_53.ts =
          reconstructWithDim goal_53.gatherDim pm.numRanks 0
            (goal_53.tps.map (fun p => pmStore p.tid)) := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- x prereq (goal_52 ↦ Pattern_35, singleton)
  have h52 := prove_pattern_35 (target := goal_52_stmt) pattern_35_target.goal_52
    initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h634_sh, _, h634_rec⟩ := h52
  simp only [goal_52, List.map_cons, List.map_nil, reconstructWithDim_singleton] at h634_rec
  have h634_sh' : (denoteGraph sm initSM 634).shape = [1, 8, 128] := by
    have := h634_sh; simp only [goal_52] at this; exact this
  -- weight initGoal_635
  have h635_init := hInitGoals initGoal_635 (by simp [initGoals])
  obtain ⟨h635_sh, hw_sh, h635_rec⟩ := h635_init
  simp only [initGoal_635, List.map_cons, List.map_nil] at h635_rec hw_sh
  have hwr0_sh : (initPM 2165).shape = [8, 128] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.1
  have hwr1_sh : (initPM 2166).shape = [8, 128] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.1
  have hwr2_sh : (initPM 2167).shape = [8, 128] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.1
  have hwr3_sh : (initPM 2168).shape = [8, 128] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  have h635_dimN : initSM 635 = allGatherPrimDimN 0 pm.numRanks 0
      [initPM 2165, initPM 2166, initPM 2167, initPM 2168] := by
    rw [h635_rec]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [hwr0_sh]; intro hc; cases hc
  have hsm635 : denoteGraph sm initSM 635 = initSM 635 :=
    denote_init_tid sm initSM 635 (by decide)
  have hpm2165 : denoteGraph pm initPM 2165 = initPM 2165 :=
    denote_init_tid pm initPM 2165 (by decide)
  have hpm2166 : denoteGraph pm initPM 2166 = initPM 2166 :=
    denote_init_tid pm initPM 2166 (by decide)
  have hpm2167 : denoteGraph pm initPM 2167 = initPM 2167 :=
    denote_init_tid pm initPM 2167 (by decide)
  have hpm2168 : denoteGraph pm initPM 2168 = initPM 2168 :=
    denote_init_tid pm initPM 2168 (by decide)
  have hS := sm_eval_636 initSM
  have hP0 := pm_eval_2169 initPM
  have hP1 := pm_eval_2170 initPM
  have hP2 := pm_eval_2171 initPM
  have hP3 := pm_eval_2172 initPM
  have h635_sh' : (denoteGraph sm initSM 635).shape = [32, 128] := by
    rw [hsm635]
    have := h635_sh; simp only [initGoal_635] at this; exact this
  have hwr0_pm_sh : (denoteGraph pm initPM 2165).shape = [8, 128] := by
    rw [hpm2165]; exact hwr0_sh
  have hwr1_pm_sh : (denoteGraph pm initPM 2166).shape = [8, 128] := by
    rw [hpm2166]; exact hwr1_sh
  have hwr2_pm_sh : (denoteGraph pm initPM 2167).shape = [8, 128] := by
    rw [hpm2167]; exact hwr2_sh
  have hwr3_pm_sh : (denoteGraph pm initPM 2168).shape = [8, 128] := by
    rw [hpm2168]; exact hwr3_sh
  have h634_pm_sh : (denoteGraph pm initPM 634).shape = [1, 8, 128] := by
    rw [← h634_rec]; exact h634_sh'
  have hbridge := bridge_fw_w_4 1 8 128 8
      (denoteGraph pm initPM 634)
      (denoteGraph pm initPM 2165) (denoteGraph pm initPM 2166)
      (denoteGraph pm initPM 2167) (denoteGraph pm initPM 2168)
      h634_pm_sh hwr0_pm_sh hwr1_pm_sh hwr2_pm_sh hwr3_pm_sh
      (by decide) (by decide) (by decide) (by decide)
  have hLHS_sh : (denoteGraph sm initSM 636).shape = [1, 8, 32] := by
    rw [hS]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h634_sh', h635_sh']
    rfl
  have hP0_sh : (denoteGraph pm initPM 2169).shape = [1, 8, 8] := by
    rw [hP0]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h634_pm_sh, hwr0_pm_sh]
    rfl
  have hP1_sh : (denoteGraph pm initPM 2170).shape = [1, 8, 8] := by
    rw [hP1]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h634_pm_sh, hwr1_pm_sh]
    rfl
  have hP2_sh : (denoteGraph pm initPM 2171).shape = [1, 8, 8] := by
    rw [hP2]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h634_pm_sh, hwr2_pm_sh]
    rfl
  have hP3_sh : (denoteGraph pm initPM 2172).shape = [1, 8, 8] := by
    rw [hP3]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h634_pm_sh, hwr3_pm_sh]
    rfl
  have hnr : pm.numRanks = 4 := rfl
  have hsm635_dimN4 : denoteGraph sm initSM 635 = allGatherPrimDimN 0 4 0
      [denoteGraph pm initPM 2165, denoteGraph pm initPM 2166,
       denoteGraph pm initPM 2167, denoteGraph pm initPM 2168] := by
    rw [hsm635, h635_dimN, hnr, hpm2165, hpm2166, hpm2167, hpm2168]
  have hreco : denoteGraph sm initSM 636 = allGatherPrimDimN 2 4 0
      [denoteGraph pm initPM 2169, denoteGraph pm initPM 2170,
       denoteGraph pm initPM 2171, denoteGraph pm initPM 2172] := by
    rw [hS, h634_rec, hsm635_dimN4, hbridge, ← hP0, ← hP1, ← hP2, ← hP3]
  refine ⟨?_, ?_, ?_⟩
  · show (denoteGraph sm initSM 636).shape = [1, 8, 32]; exact hLHS_sh
  · show List.map (fun t => Tensor.shape t)
        ([({ rank := 0, tid := 2169 } : Piece),
          ({ rank := 1, tid := 2170 } : Piece),
          ({ rank := 2, tid := 2171 } : Piece),
          ({ rank := 3, tid := 2172 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) =
        [[1, 8, 8], [1, 8, 8], [1, 8, 8], [1, 8, 8]]
    simp only [List.map_cons, List.map_nil]
    rw [hP0_sh, hP1_sh, hP2_sh, hP3_sh]
  · show denoteGraph sm initSM 636 =
        reconstructWithDim 2 pm.numRanks 0
          ([({ rank := 0, tid := 2169 } : Piece),
            ({ rank := 1, tid := 2170 } : Piece),
            ({ rank := 2, tid := 2171 } : Piece),
            ({ rank := 3, tid := 2172 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
    simp only [List.map_cons, List.map_nil]
    rw [hnr]
    rw [reconstructWithDim_cons_cons_nonscalar 2 4 0 _ _ _
        (by rw [hP0_sh]; intro hc; cases hc)]
    exact hreco

private theorem prove_goal_106 :
    ∀ (initSM initPM : Store),
      StoreShapesHold initSM smInitEnv → StoreShapesHold initPM pmInitEnv →
      InitGoalsHold pm.numRanks initGoals initSM initPM →
      let smStore := denoteGraph sm initSM
      let pmStore := denoteGraph pm initPM
      (smStore goal_106.ts).shape = goal_106.tsShape ∧
        ((goal_106.tps.map (fun p => pmStore p.tid)).map (·.shape)) = goal_106.tpShapes ∧
        smStore goal_106.ts =
          reconstructWithDim goal_106.gatherDim pm.numRanks 0
            (goal_106.tps.map (fun p => pmStore p.tid)) := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- x prereq (goal_105 ↦ Pattern_21, singleton)
  have h105 := prove_pattern_21 (target := goal_105_stmt) pattern_21_target.goal_105
    initSM initPM hSmInit hPmInit hInitGoals
  obtain ⟨h710_sh, _, h710_rec⟩ := h105
  simp only [goal_105, List.map_cons, List.map_nil, reconstructWithDim_singleton] at h710_rec
  have h710_sh' : (denoteGraph sm initSM 710).shape = [1, 8, 32] := by
    have := h710_sh; simp only [goal_105] at this; exact this
  -- weight initGoal_711
  have h711_init := hInitGoals initGoal_711 (by simp [initGoals])
  obtain ⟨h711_sh, hw_sh, h711_rec⟩ := h711_init
  simp only [initGoal_711, List.map_cons, List.map_nil] at h711_rec hw_sh
  have hwr0_sh : (initPM 3369).shape = [32, 32] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.1
  have hwr1_sh : (initPM 3370).shape = [32, 32] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.1
  have hwr2_sh : (initPM 3371).shape = [32, 32] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.1
  have hwr3_sh : (initPM 3372).shape = [32, 32] := by
    have := hw_sh; simp only [List.cons.injEq] at this; exact this.2.2.2.1
  have h711_dimN : initSM 711 = allGatherPrimDimN 0 pm.numRanks 0
      [initPM 3369, initPM 3370, initPM 3371, initPM 3372] := by
    rw [h711_rec]
    apply reconstructWithDim_cons_cons_nonscalar
    rw [hwr0_sh]; intro hc; cases hc
  have hsm711 : denoteGraph sm initSM 711 = initSM 711 :=
    denote_init_tid sm initSM 711 (by decide)
  have hpm3369 : denoteGraph pm initPM 3369 = initPM 3369 :=
    denote_init_tid pm initPM 3369 (by decide)
  have hpm3370 : denoteGraph pm initPM 3370 = initPM 3370 :=
    denote_init_tid pm initPM 3370 (by decide)
  have hpm3371 : denoteGraph pm initPM 3371 = initPM 3371 :=
    denote_init_tid pm initPM 3371 (by decide)
  have hpm3372 : denoteGraph pm initPM 3372 = initPM 3372 :=
    denote_init_tid pm initPM 3372 (by decide)
  have hS := sm_eval_712 initSM
  have hP0 := pm_eval_3373 initPM
  have hP1 := pm_eval_3374 initPM
  have hP2 := pm_eval_3375 initPM
  have hP3 := pm_eval_3376 initPM
  have h711_sh' : (denoteGraph sm initSM 711).shape = [128, 32] := by
    rw [hsm711]
    have := h711_sh; simp only [initGoal_711] at this; exact this
  have hwr0_pm_sh : (denoteGraph pm initPM 3369).shape = [32, 32] := by
    rw [hpm3369]; exact hwr0_sh
  have hwr1_pm_sh : (denoteGraph pm initPM 3370).shape = [32, 32] := by
    rw [hpm3370]; exact hwr1_sh
  have hwr2_pm_sh : (denoteGraph pm initPM 3371).shape = [32, 32] := by
    rw [hpm3371]; exact hwr2_sh
  have hwr3_pm_sh : (denoteGraph pm initPM 3372).shape = [32, 32] := by
    rw [hpm3372]; exact hwr3_sh
  have h710_pm_sh : (denoteGraph pm initPM 710).shape = [1, 8, 32] := by
    rw [← h710_rec]; exact h710_sh'
  have hbridge := bridge_fw_w_4 1 8 32 32
      (denoteGraph pm initPM 710)
      (denoteGraph pm initPM 3369) (denoteGraph pm initPM 3370)
      (denoteGraph pm initPM 3371) (denoteGraph pm initPM 3372)
      h710_pm_sh hwr0_pm_sh hwr1_pm_sh hwr2_pm_sh hwr3_pm_sh
      (by decide) (by decide) (by decide) (by decide)
  have hLHS_sh : (denoteGraph sm initSM 712).shape = [1, 8, 128] := by
    rw [hS]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h710_sh', h711_sh']
    rfl
  have hP0_sh : (denoteGraph pm initPM 3373).shape = [1, 8, 32] := by
    rw [hP0]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h710_pm_sh, hwr0_pm_sh]
    rfl
  have hP1_sh : (denoteGraph pm initPM 3374).shape = [1, 8, 32] := by
    rw [hP1]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h710_pm_sh, hwr1_pm_sh]
    rfl
  have hP2_sh : (denoteGraph pm initPM 3375).shape = [1, 8, 32] := by
    rw [hP2]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h710_pm_sh, hwr2_pm_sh]
    rfl
  have hP3_sh : (denoteGraph pm initPM 3376).shape = [1, 8, 32] := by
    rw [hP3]; show (fw_linear _ _).shape = _
    unfold fw_linear
    rw [h710_pm_sh, hwr3_pm_sh]
    rfl
  have hnr : pm.numRanks = 4 := rfl
  have hsm711_dimN4 : denoteGraph sm initSM 711 = allGatherPrimDimN 0 4 0
      [denoteGraph pm initPM 3369, denoteGraph pm initPM 3370,
       denoteGraph pm initPM 3371, denoteGraph pm initPM 3372] := by
    rw [hsm711, h711_dimN, hnr, hpm3369, hpm3370, hpm3371, hpm3372]
  have hreco : denoteGraph sm initSM 712 = allGatherPrimDimN 2 4 0
      [denoteGraph pm initPM 3373, denoteGraph pm initPM 3374,
       denoteGraph pm initPM 3375, denoteGraph pm initPM 3376] := by
    rw [hS, h710_rec, hsm711_dimN4, hbridge, ← hP0, ← hP1, ← hP2, ← hP3]
  refine ⟨?_, ?_, ?_⟩
  · show (denoteGraph sm initSM 712).shape = [1, 8, 128]; exact hLHS_sh
  · show List.map (fun t => Tensor.shape t)
        ([({ rank := 0, tid := 3373 } : Piece),
          ({ rank := 1, tid := 3374 } : Piece),
          ({ rank := 2, tid := 3375 } : Piece),
          ({ rank := 3, tid := 3376 } : Piece)].map
            (fun p => denoteGraph pm initPM p.tid)) =
        [[1, 8, 32], [1, 8, 32], [1, 8, 32], [1, 8, 32]]
    simp only [List.map_cons, List.map_nil]
    rw [hP0_sh, hP1_sh, hP2_sh, hP3_sh]
  · show denoteGraph sm initSM 712 =
        reconstructWithDim 2 pm.numRanks 0
          ([({ rank := 0, tid := 3373 } : Piece),
            ({ rank := 1, tid := 3374 } : Piece),
            ({ rank := 2, tid := 3375 } : Piece),
            ({ rank := 3, tid := 3376 } : Piece)].map
              (fun p => denoteGraph pm initPM p.tid))
    simp only [List.map_cons, List.map_nil]
    rw [hnr]
    rw [reconstructWithDim_cons_cons_nonscalar 2 4 0 _ _ _
        (by rw [hP0_sh]; intro hc; cases hc)]
    exact hreco

theorem prove_pattern_19 : pattern_19_stmt := by
  intro target h
  cases h with
  | goal_23 => exact prove_goal_23
  | goal_26 => exact prove_goal_26
  | goal_51 => exact prove_goal_51
  | goal_53 => exact prove_goal_53
  | goal_106 => exact prove_goal_106

end TrainVerify.Denote.GeneratedPatterns
