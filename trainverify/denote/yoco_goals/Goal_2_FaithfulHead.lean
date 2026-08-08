import denote.yoco_goals.Goal_2
import denote.InnerChunkCEShard
import denote.Gather2Rel

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def cSmCE2 : NodeDecl :=
  { rank := 0, op := "OpName.FW_inner_chunk_ce", ins := [6255, 6256, 4931],
    outs := [4926, 4927], params := [1024] }
private def cPmCE20 : NodeDecl :=
  { rank := 0, op := "OpName.FW_inner_chunk_ce", ins := [11712, 6256, 11714],
    outs := [11716, 11718], params := [1024] }
private def cPmCE21 : NodeDecl :=
  { rank := 1, op := "OpName.FW_inner_chunk_ce", ins := [11713, 6256, 11715],
    outs := [11717, 11719], params := [1024] }
private def cPmGather2 : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [11718, 11719],
    outs := [4927], params := [0] }

private theorem csm2_all_nonempty :
    ∀ n ∈ sm_goal_2.nodes, n.outs ≠ [] := by native_decide
private theorem cpm2_all_nonempty :
    ∀ n ∈ pm_goal_2.nodes, n.outs ≠ [] := by native_decide
private theorem csm2_nonempty (k : Nat) :
    ∀ n ∈ sm_goal_2.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact csm2_all_nonempty n (List.mem_of_mem_drop hn)
private theorem cpm2_nonempty (k : Nat) :
    ∀ n ∈ pm_goal_2.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact cpm2_all_nonempty n (List.mem_of_mem_drop hn)

private theorem red_sm4927 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_2 initSM 4927 =
      (fw_inner_chunk_ce (denoteGraphDistributedFaithful sm_goal_2 initSM 6255)
        (denoteGraphDistributedFaithful sm_goal_2 initSM 6256)
        (denoteGraphDistributedFaithful sm_goal_2 initSM 4931)
        (((denoteGraphDistributedFaithful sm_goal_2 initSM 6256).shape.head?).getD 0)
        ((0 : Nat) : Scalar)).snd := by
  refine denoteGraphDistributedFaithful_reduce3 sm_goal_2 initSM 924 cSmCE2
    6255 6256 4931 4927
    (fun x w y => (fw_inner_chunk_ce x w y ((w.shape.head?).getD 0)
      ((0 : Nat) : Scalar)).snd)
    (by native_decide) (by native_decide) ?_
    (csm2_nonempty 925) (by native_decide)
    (csm2_nonempty 924) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cSmCE2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_inner_chunk_ce_snd_out_1p sm_goal_2 s 0 6255 6256 4931
    4926 4927 (by decide) (params := [1024])

private theorem red_pm11718 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_2 initPM 11718 =
      (fw_inner_chunk_ce (denoteGraphDistributedFaithful pm_goal_2 initPM 11712)
        (denoteGraphDistributedFaithful pm_goal_2 initPM 6256)
        (denoteGraphDistributedFaithful pm_goal_2 initPM 11714)
        (((denoteGraphDistributedFaithful pm_goal_2 initPM 6256).shape.head?).getD 0)
        ((0 : Nat) : Scalar)).snd := by
  refine denoteGraphDistributedFaithful_reduce3 pm_goal_2 initPM 2020 cPmCE20
    11712 6256 11714 11718
    (fun x w y => (fw_inner_chunk_ce x w y ((w.shape.head?).getD 0)
      ((0 : Nat) : Scalar)).snd)
    (by native_decide) (by native_decide) ?_
    (cpm2_nonempty 2021) (by native_decide)
    (cpm2_nonempty 2020) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cPmCE20
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_inner_chunk_ce_snd_out_1p pm_goal_2 s 0 11712 6256 11714
    11716 11718 (by decide) (params := [1024])

private theorem red_pm11719 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_2 initPM 11719 =
      (fw_inner_chunk_ce (denoteGraphDistributedFaithful pm_goal_2 initPM 11713)
        (denoteGraphDistributedFaithful pm_goal_2 initPM 6256)
        (denoteGraphDistributedFaithful pm_goal_2 initPM 11715)
        (((denoteGraphDistributedFaithful pm_goal_2 initPM 6256).shape.head?).getD 0)
        ((0 : Nat) : Scalar)).snd := by
  refine denoteGraphDistributedFaithful_reduce3 pm_goal_2 initPM 2021 cPmCE21
    11713 6256 11715 11719
    (fun x w y => (fw_inner_chunk_ce x w y ((w.shape.head?).getD 0)
      ((0 : Nat) : Scalar)).snd)
    (by native_decide) (by native_decide) ?_
    (cpm2_nonempty 2022) (by native_decide)
    (cpm2_nonempty 2021) (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cPmCE21
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_inner_chunk_ce_snd_out_1p pm_goal_2 s 1 11713 6256 11715
    11717 11719 (by decide) (params := [1024])

private theorem red_pm4927 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_2 initPM 4927 =
      allGatherPrimDimN 0 2 0
        [denoteGraphDistributedFaithful pm_goal_2 initPM 11718,
         denoteGraphDistributedFaithful pm_goal_2 initPM 11719] := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_2 initPM 2022 cPmGather2
    11718 11719 4927 (fun a b => allGatherPrimDimN 0 2 0 [a, b])
    (by native_decide) (by native_decide) ?_
    (cpm2_nonempty 2023) (by native_decide)
    (cpm2_nonempty 2022) (by native_decide) (by native_decide)
  intro s
  unfold cPmGather2
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_allGatherPrimDimN_out pm_goal_2 s 0 [11718, 11719] 4927 0

private theorem canonical_input_eq2 (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_2.numRanks initGoals initSM initPM)
    (tid : Tid) (g : LineageGoal) (hg : g ∈ initGoals)
    (htp : g.tps = [{rank := 0, tid := tid}])
    (hgd : g.gatherDim = 0) (hrep : g.replicated = false) (hts : g.ts = tid)
    (hs : ∀ n ∈ sm_goal_2.nodes, tid ∉ n.outs)
    (hp : ∀ n ∈ pm_goal_2.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful sm_goal_2 initSM tid =
      denoteGraphDistributedFaithful pm_goal_2 initPM tid := by
  have hi := (hInit g hg).2.2
  rw [reconstructForGoal_of_not_replicated g pm_goal_2.numRanks _ hrep,
    htp, hts, hgd] at hi
  simp only [List.map, reconstructWithDim] at hi
  unfold denoteGraphDistributedFaithful
  rw [foldl_applyNodeDistributedFaithful_at_not_written sm_goal_2 sm_goal_2.nodes initSM tid
      (by native_decide) hs,
    foldl_applyNodeDistributedFaithful_at_not_written pm_goal_2 pm_goal_2.nodes initPM tid
      (by native_decide) hp]
  exact hi

-- Isolate the z-loss commute from generated-goal normalization.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem canonical_goal_2_value_from_norm (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_2InitEnv)
    (hInit : InitGoalsHold pm_goal_2.numRanks initGoals initSM initPM)
    (hnorm : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_2 initSM 6255)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11712)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11713)
      [4096, 1024] [2048, 1024]) :
    denoteGraphDistributedFaithful sm_goal_2 initSM 4927 =
      denoteGraphDistributedFaithful pm_goal_2 initPM 4927 := by
  have hw : (denoteGraphDistributedFaithful pm_goal_2 initPM 6256).shape =
      [154880, 1024] := by
    unfold denoteGraphDistributedFaithful
    rw [foldl_applyNodeDistributedFaithful_at_not_written pm_goal_2 pm_goal_2.nodes
      initPM 6256 (by native_decide) (by native_decide)]
    exact hPM 6256 [154880, 1024] (by native_decide)
  have hvocab : ((denoteGraphDistributedFaithful pm_goal_2 initPM 6256).shape.head?).getD 0 =
      154880 := by rw [hw]; rfl
  have hweight := canonical_input_eq2 initSM initPM hInit 6256 initGoal_6256
    (by native_decide) rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hlabel := canonical_input_eq2 initSM initPM hInit 4931 initGoal_4931
    (by native_decide) rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hval : denoteGraphDistributedFaithful sm_goal_2 initSM 4927 =
      denoteGraphDistributedFaithful pm_goal_2 initPM 4927 := by
    rw [red_sm4927, red_pm4927, red_pm11718, red_pm11719, hnorm.value,
      hweight, hlabel, hvocab]
    -- `.snd` is independent of labels, so use the same arbitrary tensor on all ranks.
    rw [show (fw_inner_chunk_ce (denoteGraphDistributedFaithful pm_goal_2 initPM 11712)
          (denoteGraphDistributedFaithful pm_goal_2 initPM 6256)
          (denoteGraphDistributedFaithful pm_goal_2 initPM 11714)
          154880 ((0 : Nat) : Scalar)).snd =
        (fw_inner_chunk_ce (denoteGraphDistributedFaithful pm_goal_2 initPM 11712)
          (denoteGraphDistributedFaithful pm_goal_2 initPM 6256)
          (denoteGraphDistributedFaithful pm_goal_2 initPM 4931)
          154880 ((0 : Nat) : Scalar)).snd from by rfl,
      show (fw_inner_chunk_ce (denoteGraphDistributedFaithful pm_goal_2 initPM 11713)
          (denoteGraphDistributedFaithful pm_goal_2 initPM 6256)
          (denoteGraphDistributedFaithful pm_goal_2 initPM 11715)
          154880 ((0 : Nat) : Scalar)).snd =
        (fw_inner_chunk_ce (denoteGraphDistributedFaithful pm_goal_2 initPM 11713)
          (denoteGraphDistributedFaithful pm_goal_2 initPM 6256)
          (denoteGraphDistributedFaithful pm_goal_2 initPM 4931)
          154880 ((0 : Nat) : Scalar)).snd from by rfl]
    have hhead : (([denoteGraphDistributedFaithful pm_goal_2 initPM 11712,
        denoteGraphDistributedFaithful pm_goal_2 initPM 11713] : List Tensor).head?.map
        (fun t => t.shape)).getD [] = [2048, 1024] := by
      simp only [List.head?_cons, Option.map_some, Option.getD_some]
      exact hnorm.shard0_shape
    have hshapes : ∀ r (_ : r < 2),
        (([denoteGraphDistributedFaithful pm_goal_2 initPM 11712,
           denoteGraphDistributedFaithful pm_goal_2 initPM 11713] : List Tensor).getD r
           (zeroTensor [2048, 1024])).shape = [2048, 1024] := by
      intro r hr
      match r, hr with
      | 0, _ => rw [List.getD_cons_zero]; exact hnorm.shard0_shape
      | 1, _ => rw [List.getD_cons_succ, List.getD_cons_zero]; exact hnorm.shard1_shape
    have hofFn : (List.ofFn (n := 2) (fun r : Fin 2 =>
        (fw_inner_chunk_ce
          (([denoteGraphDistributedFaithful pm_goal_2 initPM 11712,
             denoteGraphDistributedFaithful pm_goal_2 initPM 11713] : List Tensor).getD r.val
               (zeroTensor [2048, 1024]))
          (denoteGraphDistributedFaithful pm_goal_2 initPM 6256)
          (denoteGraphDistributedFaithful pm_goal_2 initPM 4931)
          154880 ((0 : Nat) : Scalar)).snd)) =
        [ (fw_inner_chunk_ce (denoteGraphDistributedFaithful pm_goal_2 initPM 11712)
            (denoteGraphDistributedFaithful pm_goal_2 initPM 6256)
            (denoteGraphDistributedFaithful pm_goal_2 initPM 4931)
            154880 ((0 : Nat) : Scalar)).snd,
          (fw_inner_chunk_ce (denoteGraphDistributedFaithful pm_goal_2 initPM 11713)
            (denoteGraphDistributedFaithful pm_goal_2 initPM 6256)
            (denoteGraphDistributedFaithful pm_goal_2 initPM 4931)
            154880 ((0 : Nat) : Scalar)).snd ] := by
      simp only [List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.succ_zero_eq_one,
        Fin.val_one, List.getD_cons_zero, List.getD_cons_succ]
    rw [fw_inner_chunk_ce_snd_allGatherDim0_shards 2 2048 1024 154880
      ((0 : Nat) : Scalar)
      [denoteGraphDistributedFaithful pm_goal_2 initPM 11712,
       denoteGraphDistributedFaithful pm_goal_2 initPM 11713]
      (denoteGraphDistributedFaithful pm_goal_2 initPM 6256)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 4931)
      (by decide) (by decide) (by decide) (by decide)
      hhead hshapes hw, hofFn]
  exact hval

-- Avoid rewrite search through the 3764-line graph when transporting output shape.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem canonical_goal_2_shape_from_norm (initSM initPM : Store)
    (hnorm : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_2 initSM 6255)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11712)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11713)
      [4096, 1024] [2048, 1024]) :
    (denoteGraphDistributedFaithful sm_goal_2 initSM 4927).shape = [4096] := by
  calc
    _ = ((fw_inner_chunk_ce
        (denoteGraphDistributedFaithful sm_goal_2 initSM 6255)
        (denoteGraphDistributedFaithful sm_goal_2 initSM 6256)
        (denoteGraphDistributedFaithful sm_goal_2 initSM 4931)
        (((denoteGraphDistributedFaithful sm_goal_2 initSM 6256).shape.head?).getD 0)
        ((0 : Nat) : Scalar)).snd).shape := congrArg Tensor.shape (red_sm4927 initSM)
    _ = [4096] := fw_inner_chunk_ce_snd_shape _ _ _ _ _ 4096 (by
      rw [hnorm.full_shape]
      rfl)

-- The sole upstream obligation is the actual trailing RMSNorm Gather relation.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Canonical ancestry-closed z-loss head. -/
theorem canonical_goal_2_from_norm (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_2InitEnv)
    (hInit : InitGoalsHold pm_goal_2.numRanks initGoals initSM initPM)
    (hnorm : Gather2Rel
      (denoteGraphDistributedFaithful sm_goal_2 initSM 6255)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11712)
      (denoteGraphDistributedFaithful pm_goal_2 initPM 11713)
      [4096, 1024] [2048, 1024]) :
    InitGoalHolds pm_goal_2.numRanks goal_2
      (denoteGraphDistributedFaithful sm_goal_2 initSM)
      (denoteGraphDistributedFaithful pm_goal_2 initPM) := by
  have hval := canonical_goal_2_value_from_norm initSM initPM hPM hInit hnorm
  have hsmShape := canonical_goal_2_shape_from_norm initSM initPM hnorm
  have hpmShape : (denoteGraphDistributedFaithful pm_goal_2 initPM 4927).shape = [4096] := by
    rw [← hval]
    exact hsmShape
  change (denoteGraphDistributedFaithful sm_goal_2 initSM 4927).shape = [4096] ∧
    [(denoteGraphDistributedFaithful pm_goal_2 initPM 4927).shape] = [[4096]] ∧
    denoteGraphDistributedFaithful sm_goal_2 initSM 4927 =
      denoteGraphDistributedFaithful pm_goal_2 initPM 4927
  exact ⟨hsmShape, congrArg (fun sh => [sh]) hpmShape, hval⟩

end
end TrainVerify.Denote.GeneratedPatterns
