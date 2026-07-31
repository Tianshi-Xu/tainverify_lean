/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.YOCOStructuralFacts
import denote.yoco_goals.BridgeKit

/-!
# Replay a shuffle-free post-ring suffix

After the last ring-attention node, `applyNodeRingAttn` equals ordinary
`applyNode`. This module factors the full ring denotation into a ring prefix and
an ordinary tail, allowing the existing verified slice fixed-point theorem to
lift non-base cut graphs that live entirely in that tail.
-/

set_option linter.style.longLine false
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedStructuralFacts

noncomputable section

/-- First SM node after the last ring-attention operator. -/
def smPostRingStart : Nat := 891
/-- First PM node after the last ring-attention operator. -/
def pmPostRingStart : Nat := 1844

def smPostRing : GraphDecl := { sm with nodes := sm.nodes.drop smPostRingStart }
def pmPostRing : GraphDecl := { pm with nodes := pm.nodes.drop pmPostRingStart }

def smRingPrefixStore (initSM : Store) : Store :=
  (sm.nodes.take smPostRingStart).foldl (applyNodeRingAttn sm) initSM

def pmRingPrefixStore (initPM : Store) : Store :=
  (pm.nodes.take pmPostRingStart).foldl (applyNodeRingAttn pm) initPM

private theorem foldl_ring_eq_plain_of_no_ring
    (g : GraphDecl) (nodes : List NodeDecl) (s : Store)
    (hno : ∀ n ∈ nodes,
      n.op ≠ "OpName.FW_attn_zigzag" ∧
      n.op ≠ "OpName.FW_attn_sliding_window") :
    nodes.foldl (applyNodeRingAttn g) s = nodes.foldl (applyNode g) s := by
  induction nodes generalizing s with
  | nil => rfl
  | cons n ns ih =>
      have hn := hno n (by simp)
      rw [List.foldl_cons, List.foldl_cons,
        applyNodeRingAttn_eq_applyNode_of_not_ring g s n hn.1 hn.2]
      apply ih
      intro m hm
      exact hno m (by simp [hm])

private theorem sm_post_no_ring : ∀ n ∈ smPostRing.nodes,
    n.op ≠ "OpName.FW_attn_zigzag" ∧
    n.op ≠ "OpName.FW_attn_sliding_window" := by native_decide

private theorem pm_post_no_ring : ∀ n ∈ pmPostRing.nodes,
    n.op ≠ "OpName.FW_attn_zigzag" ∧
    n.op ≠ "OpName.FW_attn_sliding_window" := by native_decide

private theorem applyNode_smPostRing_eq : applyNode smPostRing = applyNode sm :=
  applyNode_congr_numRanks _ _ rfl

private theorem applyNode_pmPostRing_eq : applyNode pmPostRing = applyNode pm :=
  applyNode_congr_numRanks _ _ rfl

/-- Full SM ring denotation is ordinary evaluation of the post-ring suffix from
its ring-aware prefix store. -/
theorem sm_ring_eq_post (initSM : Store) :
    denoteGraph_ringAttn sm initSM = denoteGraph smPostRing (smRingPrefixStore initSM) := by
  unfold denoteGraph_ringAttn denoteGraph smRingPrefixStore smPostRing smPostRingStart
  rw [show sm.nodes = sm.nodes.take 891 ++ sm.nodes.drop 891 from
    (List.take_append_drop 891 sm.nodes).symm, List.foldl_append]
  exact foldl_ring_eq_plain_of_no_ring sm (sm.nodes.drop 891)
    ((sm.nodes.take 891).foldl (applyNodeRingAttn sm) initSM) sm_post_no_ring

/-- PM analog of `sm_ring_eq_post`. -/
theorem pm_ring_eq_post (initPM : Store) :
    denoteGraph_ringAttn pm initPM = denoteGraph pmPostRing (pmRingPrefixStore initPM) := by
  unfold denoteGraph_ringAttn denoteGraph pmRingPrefixStore pmPostRing pmPostRingStart
  rw [show pm.nodes = pm.nodes.take 1844 ++ pm.nodes.drop 1844 from
    (List.take_append_drop 1844 pm.nodes).symm, List.foldl_append]
  exact foldl_ring_eq_plain_of_no_ring pm (pm.nodes.drop 1844)
    ((pm.nodes.take 1844).foldl (applyNodeRingAttn pm) initPM) pm_post_no_ring

/-- Structural facts required by `denoteGraph_slice_self_agrees`. -/
theorem smPostRing_wellFormed : IsWellFormedGraph smPostRing := by
  intro n hn
  exact sm_wellFormed n (List.mem_of_mem_drop hn)

theorem pmPostRing_wellFormed : IsWellFormedGraph pmPostRing := by
  intro n hn
  exact pm_wellFormed n (List.mem_of_mem_drop hn)

theorem smPostRing_topoSorted : IsTopoSorted smPostRing.nodes := by
  apply isTopoSorted_of_bool
  native_decide

theorem pmPostRing_topoSorted : IsTopoSorted pmPostRing.nodes := by
  apply isTopoSorted_of_bool
  native_decide

theorem smPostRing_nodup : smPostRing.nodes.Nodup := by native_decide
theorem pmPostRing_nodup : pmPostRing.nodes.Nodup := by native_decide

private theorem sm_nodes_outs_nonempty : ∀ n ∈ sm.nodes, n.outs ≠ [] := by native_decide
private theorem pm_nodes_outs_nonempty : ∀ n ∈ pm.nodes, n.outs ≠ [] := by native_decide

/-- Initial lineage contracts are preserved by the ring-aware full denotation. -/
theorem initGoals_preserved_ringAttn (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalsHold pm.numRanks initGoals
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  intro g hg
  have hg0 := hInit g hg
  have hts : denoteGraph_ringAttn sm initSM g.ts = initSM g.ts := by
    unfold denoteGraph_ringAttn
    exact foldl_applyNodeRingAttn_at_not_written sm sm.nodes initSM g.ts
      sm_nodes_outs_nonempty (all_initGoal_ts_not_written g hg)
  have htps : ∀ tp ∈ g.tps,
      denoteGraph_ringAttn pm initPM tp.tid = initPM tp.tid := by
    intro tp htp
    unfold denoteGraph_ringAttn
    exact foldl_applyNodeRingAttn_at_not_written pm pm.nodes initPM tp.tid
      pm_nodes_outs_nonempty (all_initGoal_tps_not_written g hg tp htp)
  unfold InitGoalHolds at hg0 ⊢
  simp only [hts]
  rw [List.map_congr_left (g := fun p => initPM p.tid)]
  · exact hg0
  · intro tp htp
    exact htps tp htp

end
end TrainVerify.Denote.GeneratedPatterns
