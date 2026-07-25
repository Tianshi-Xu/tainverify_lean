/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L12FaithfulZigzagAttention
import denote.yoco_goals.ZigzagViewRel

/-!
# Faithful zigzag relation for generated goal 5348 (`FW_reshape` of 5347)

The generated graph reshapes the L12 cross-decoder attention output:

* SM node 506: `FW_reshape [5347] → [5348]` with params `[4096, 1024]`
* PM node 1074: `FW_reshape [9687] → [9689]` with params `[2048, 1024]` (rank 0)
* PM node 1075: `FW_reshape [9688] → [9690]` with params `[2048, 1024]` (rank 1)

`FW_reshape` is *not* one of the three faithful collectives, so each node reduces
through `applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective`
followed by `applyNode_fw_reshape_out`, i.e. plain `fw_view`.

The layout content is then carried by `Zigzag2Rel.view_3d_to_2d` applied to the
already-verified parent `recon_zigzagGoal_5347_faithful`.
-/

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def l12SmReshape : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [5347], outs := [5348],
    params := [4096, 1024] }
private def l12PmReshape0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [9687], outs := [9689],
    params := [2048, 1024] }
private def l12PmReshape1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [9688], outs := [9690],
    params := [2048, 1024] }

set_option maxRecDepth 1000000 in
private theorem l12_view_native_facts :
    sm.nodes[506]'(by native_decide) = l12SmReshape ∧
    pm.nodes[1074]'(by native_decide) = l12PmReshape0 ∧
    pm.nodes[1075]'(by native_decide) = l12PmReshape1 := by
  native_decide

private theorem view_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem view_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l12_view_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(507, 5348), (506, 5347)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l12_view_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1075, 9689), (1076, 9690), (1074, 9687), (1075, 9688)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> native_decide +revert

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
-- Faithful zigzag relation for the reshaped L12 attention output (goal 5348).
theorem recon_zigzagGoal_5348_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5348)
      (denoteGraphDistributedFaithful pm initPM 9689)
      (denoteGraphDistributedFaithful pm initPM 9690)
      (denoteGraphDistributedFaithful pm initPM 5345)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_5347_faithful initSM initPM hSM hPM hInit hValues hCu
  rcases l12_view_native_facts with ⟨sn, pn0, pn1⟩
  have hSMred : denoteGraphDistributedFaithful sm initSM 5348 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm initSM 5347) := by
    refine denoteGraphDistributedFaithful_reduce1 sm initSM 506 l12SmReshape
      5347 5348 (fun x => fw_view [4096, 1024] x)
      (by native_decide) sn ?_
      (view_nonempty_sm 507) (l12_view_sm_not_written 507 5348 (by decide))
      (view_nonempty_sm 506) (l12_view_sm_not_written 506 5347 (by decide))
    intro s
    unfold l12SmReshape
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_reshape_out sm s 0 5347 5348 [4096, 1024]
  have hP0red : denoteGraphDistributedFaithful pm initPM 9689 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 9687) := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1074 l12PmReshape0
      9687 9689 (fun x => fw_view [2048, 1024] x)
      (by native_decide) pn0 ?_
      (view_nonempty_pm 1075) (l12_view_pm_not_written 1075 9689 (by decide))
      (view_nonempty_pm 1074) (l12_view_pm_not_written 1074 9687 (by decide))
    intro s
    unfold l12PmReshape0
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_reshape_out pm s 0 9687 9689 [2048, 1024]
  have hP1red : denoteGraphDistributedFaithful pm initPM 9690 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm initPM 9688) := by
    refine denoteGraphDistributedFaithful_reduce1 pm initPM 1075 l12PmReshape1
      9688 9690 (fun x => fw_view [2048, 1024] x)
      (by native_decide) pn1 ?_
      (view_nonempty_pm 1076) (l12_view_pm_not_written 1076 9690 (by decide))
      (view_nonempty_pm 1075) (l12_view_pm_not_written 1075 9688 (by decide))
    intro s
    unfold l12PmReshape1
    rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
      (by decide) (by decide)]
    exact applyNode_fw_reshape_out pm s 1 9688 9690 [2048, 1024]
  rw [hSMred, hP0red, hP1red]
  exact Zigzag2Rel.view_3d_to_2d 2048 16 64 hparent (by decide) (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
