/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L12FaithfulReplicatedBoundary
import denote.yoco_goals.L12FaithfulMaybeShuffle
import denote.yoco_goals.YOCInputValueClasses

/-!
# Entry-segment multiref exits `8015` and `8143`

Two remaining mechanical pieces of the entry segment (SM nodes 473 / 474):

* `recon_intermediateGoal_8015_faithful` — the *first* output of the 2-way
  `FW_multiref [5332] → [8015, 8019]` (SM node 473); on the PM side the two
  replicated copies are `15741` (rank 0, node 1011) and `15749` (rank 1, node
  1012).  The generated goal is `replicated := true`, so reconstruction picks
  the rank-0 head.
* `recon_zigzagGoal_8143_faithful` — the *second* output of the 2-way
  `FW_multiref [5338] → [8139, 8143]` (SM node 474); on the PM side `15973`
  (rank 0, node 1006) and `15981` (rank 1, node 1009).  Since `5338` is a
  zigzag-shuffled tensor, the statement is the faithful `Zigzag2Rel` inherited
  verbatim from `recon_zigzagGoal_5338_distributed`.

No new axioms, no new hypotheses.
-/

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option linter.unusedVariables false

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private theorem l2mr_nonempty_sm (k : Nat) : ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l2mr_nonempty_pm (k : Nat) : ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l2mr_sm_facts :
    sm.nodes[473]'(by native_decide) =
      { rank := 0, op := "OpName.FW_multiref", ins := [5332], outs := [8015, 8019], params := [2] } ∧
    sm.nodes[474]'(by native_decide) =
      { rank := 0, op := "OpName.FW_multiref", ins := [5338], outs := [8139, 8143], params := [2] } := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l2mr_pm_facts :
    pm.nodes[1011]'(by native_decide) =
      { rank := 0, op := "OpName.FW_multiref", ins := [5332], outs := [15741, 15745], params := [2] } ∧
    pm.nodes[1012]'(by native_decide) =
      { rank := 1, op := "OpName.FW_multiref", ins := [5332], outs := [15749, 15753], params := [2] } ∧
    pm.nodes[1006]'(by native_decide) =
      { rank := 0, op := "OpName.FW_multiref", ins := [9655], outs := [15969, 15973], params := [2] } ∧
    pm.nodes[1009]'(by native_decide) =
      { rank := 1, op := "OpName.FW_multiref", ins := [9656], outs := [15977, 15981], params := [2] } := by
  native_decide

private def l2mrSmPairs : List (Nat × Nat) :=
  [(474, 8015), (473, 5332), (475, 8143), (474, 5338)]

private def l2mrPmPairs : List (Nat × Nat) :=
  [(1012, 15741), (1011, 5332), (1013, 15749), (1012, 5332),
   (1007, 15973), (1006, 9655), (1010, 15981), (1009, 9656)]

set_option maxRecDepth 1000000 in
private theorem l2mr_sm_not_written_all :
    ∀ p ∈ l2mrSmPairs, ∀ n ∈ sm.nodes.drop p.1, p.2 ∉ n.outs := by
  native_decide

private theorem l2mr_sm_not_written (k tid : Nat) (h : (k, tid) ∈ l2mrSmPairs) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs :=
  l2mr_sm_not_written_all (k, tid) h

set_option maxRecDepth 1000000 in
private theorem l2mr_pm_not_written_all :
    ∀ p ∈ l2mrPmPairs, ∀ n ∈ pm.nodes.drop p.1, p.2 ∉ n.outs := by
  native_decide

private theorem l2mr_pm_not_written (k tid : Nat) (h : (k, tid) ∈ l2mrPmPairs) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs :=
  l2mr_pm_not_written_all (k, tid) h

/-- Wrap a `replicated := true` dual-tp goal for the faithful denotations:
reconstruction picks the rank-0 head. -/
private theorem l2mr_wrap_replicated_dual (smS pmS : Store) (g : LineageGoal)
    (T p0 p1 : Tid) (sh : Shape)
    (htp : g.tps = [{ rank := 0, tid := p0 }, { rank := 1, tid := p1 }])
    (hrep : g.replicated = true) (hts : g.ts = T) (htsShape : g.tsShape = sh)
    (htpShapes : g.tpShapes = [sh, sh])
    (hval : smS T = pmS p0)
    (hshape0 : (smS T).shape = sh)
    (hshapeP0 : (pmS p0).shape = sh)
    (hshapeP1 : (pmS p1).shape = sh) :
    InitGoalHolds pm.numRanks g smS pmS := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hts, htsShape]; exact hshape0
  · rw [htp, htpShapes]; simp only [List.map]; rw [hshapeP0, hshapeP1]
  · unfold reconstructForGoal
    rw [hrep]
    simp only [if_true, htp, hts, List.map, List.headD]
    exact hval

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 12000000 in
/-- Faithful reconstruction of the replicated boundary multiref exit `8015`. -/
theorem recon_intermediateGoal_8015_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    InitGoalHolds pm.numRanks intermediateGoal_8015
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM) := by
  have h32 := recon_intermediateGoal_5332_faithful initSM initPM hSM hPM hInit
  have hv32 := oneTp_valeq intermediateGoal_5332 _ _ 5332 rfl rfl rfl rfl h32
  have hs32 : (denoteGraphDistributedFaithful sm initSM 5332).shape = [4096, 1024] := by
    have h := h32.1
    simpa [intermediateGoal_5332] using h
  rcases l2mr_sm_facts with ⟨sn473, _⟩
  rcases l2mr_pm_facts with ⟨pn1011, pn1012, _, _⟩
  have sred : denoteGraphDistributedFaithful sm initSM 8015 =
      denoteGraphDistributedFaithful sm initSM 5332 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 473 _ 5332 8015 (fun x => x)
      (by native_decide) sn473 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_multiref2_first_out sm s 0 5332 8015 8019)
      (l2mr_nonempty_sm 474) (l2mr_sm_not_written 474 8015 (by decide))
      (l2mr_nonempty_sm 473) (l2mr_sm_not_written 473 5332 (by decide))
  have pred0 : denoteGraphDistributedFaithful pm initPM 15741 =
      denoteGraphDistributedFaithful pm initPM 5332 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1011 _ 5332 15741 (fun x => x)
      (by native_decide) pn1011 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_multiref2_first_out pm s 0 5332 15741 15745)
      (l2mr_nonempty_pm 1012) (l2mr_pm_not_written 1012 15741 (by decide))
      (l2mr_nonempty_pm 1011) (l2mr_pm_not_written 1011 5332 (by decide))
  have pred1 : denoteGraphDistributedFaithful pm initPM 15749 =
      denoteGraphDistributedFaithful pm initPM 5332 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1012 _ 5332 15749 (fun x => x)
      (by native_decide) pn1012 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_multiref2_first_out pm s 1 5332 15749 15753)
      (l2mr_nonempty_pm 1013) (l2mr_pm_not_written 1013 15749 (by decide))
      (l2mr_nonempty_pm 1012) (l2mr_pm_not_written 1012 5332 (by decide))
  refine l2mr_wrap_replicated_dual _ _ intermediateGoal_8015 8015 15741 15749 [4096, 1024]
    rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_
  · rw [sred, pred0]; exact hv32
  · rw [sred]; exact hs32
  · rw [pred0, ← hv32]; exact hs32
  · rw [pred1, ← hv32]; exact hs32

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
/-- Faithful zigzag relation for the residual-bypass multiref exit `8143`. -/
theorem recon_zigzagGoal_8143_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 8143)
      (denoteGraphDistributedFaithful pm initPM 15973)
      (denoteGraphDistributedFaithful pm initPM 15981)
      (denoteGraphDistributedFaithful pm initPM 5337)
      [4096, 1024] [2048, 1024] := by
  have hparent := recon_zigzagGoal_5338_distributed initSM initPM hSM hPM hInit hCu
  rcases l2mr_sm_facts with ⟨_, sn474⟩
  rcases l2mr_pm_facts with ⟨_, _, pn1006, pn1009⟩
  have sred : denoteGraphDistributedFaithful sm initSM 8143 =
      denoteGraphDistributedFaithful sm initSM 5338 := by
    exact denoteGraphDistributedFaithful_reduce1 sm initSM 474 _ 5338 8143 (fun x => x)
      (by native_decide) sn474 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_multiref2_second_out' sm s 0 5338 8139 8143 (by decide))
      (l2mr_nonempty_sm 475) (l2mr_sm_not_written 475 8143 (by decide))
      (l2mr_nonempty_sm 474) (l2mr_sm_not_written 474 5338 (by decide))
  have pred0 : denoteGraphDistributedFaithful pm initPM 15973 =
      denoteGraphDistributedFaithful pm initPM 9655 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1006 _ 9655 15973 (fun x => x)
      (by native_decide) pn1006 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_multiref2_second_out' pm s 0 9655 15969 15973 (by decide))
      (l2mr_nonempty_pm 1007) (l2mr_pm_not_written 1007 15973 (by decide))
      (l2mr_nonempty_pm 1006) (l2mr_pm_not_written 1006 9655 (by decide))
  have pred1 : denoteGraphDistributedFaithful pm initPM 15981 =
      denoteGraphDistributedFaithful pm initPM 9656 := by
    exact denoteGraphDistributedFaithful_reduce1 pm initPM 1009 _ 9656 15981 (fun x => x)
      (by native_decide) pn1009 (by
        intro s
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _ (by decide) (by decide)]
        exact applyNode_fw_multiref2_second_out' pm s 1 9656 15977 15981 (by decide))
      (l2mr_nonempty_pm 1010) (l2mr_pm_not_written 1010 15981 (by decide))
      (l2mr_nonempty_pm 1009) (l2mr_pm_not_written 1009 9656 (by decide))
  rw [sred, pred0, pred1]
  exact hparent

end
end TrainVerify.Denote.GeneratedPatterns
