/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L23FaithfulHead

/-!
# The final two top-level goals: `goal_1` (`4673`) and `goal_2` (`4674`)

Both are the outputs of the graph's last `FW_inner_chunk_ce`. `L23FaithfulHead`
supplies the node reductions and the RMSNorm `Gather2Rel` at `5930`; this module
does the two sharding arguments.
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

/-! ### `goal_2` — the z-loss head

`fw_inner_chunk_ce.snd` never reads the labels, so the per-rank label chunk drops
out and no well-formedness contract is needed.
-/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_goal_4674_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2)
    (hx0 : (denoteGraphDistributedFaithful pm initPM 13257).shape.getD 0 0 = 2048) :
    denoteGraphDistributedFaithful sm initSM 4674 =
      denoteGraphDistributedFaithful pm initPM 4674 := by
  have hnorm := recon_goal_5930_faithful_tids initSM initPM hSM hPM hInit hValues hCu hx0
  have hw : (denoteGraphDistributedFaithful pm initPM 5931).shape = [154880, 1024] :=
    l23hd_pm_input_shape initPM hPM 5931 [154880, 1024] (by native_decide)
      (l23hd_pm_input_fixed 5931 (by decide))
  have hvocab : ((denoteGraphDistributedFaithful pm initPM 5931).shape.head?).getD 0 = 154880 := by
    rw [hw]; rfl
  rw [l23hd_red_sm4674 initSM, l23hd_red_pm4674 initPM,
    l23hd_red_pm11839 initPM, l23hd_red_pm11840 initPM,
    l23hd_w5931 initSM initPM hInit, l23hd_w4678 initSM initPM hInit,
    hnorm.value, hvocab]
  -- The labels argument is irrelevant on `.snd`: replace both per-rank chunks
  -- by the full label tensor, so the sharding lemma applies with a shared `y`.
  rw [show (fw_inner_chunk_ce (denoteGraphDistributedFaithful pm initPM 11833)
        (denoteGraphDistributedFaithful pm initPM 5931)
        (denoteGraphDistributedFaithful pm initPM 11835) 154880 ((0 : Nat) : Scalar)).snd =
      (fw_inner_chunk_ce (denoteGraphDistributedFaithful pm initPM 11833)
        (denoteGraphDistributedFaithful pm initPM 5931)
        (denoteGraphDistributedFaithful pm initPM 4678) 154880 ((0 : Nat) : Scalar)).snd from
      l23hd_snd_y_independent _ _ _ _ _ _,
    show (fw_inner_chunk_ce (denoteGraphDistributedFaithful pm initPM 11834)
        (denoteGraphDistributedFaithful pm initPM 5931)
        (denoteGraphDistributedFaithful pm initPM 11836) 154880 ((0 : Nat) : Scalar)).snd =
      (fw_inner_chunk_ce (denoteGraphDistributedFaithful pm initPM 11834)
        (denoteGraphDistributedFaithful pm initPM 5931)
        (denoteGraphDistributedFaithful pm initPM 4678) 154880 ((0 : Nat) : Scalar)).snd from
      l23hd_snd_y_independent _ _ _ _ _ _]
  have hnr : pm.numRanks = 2 := rfl
  have hhead : (([denoteGraphDistributedFaithful pm initPM 11833,
      denoteGraphDistributedFaithful pm initPM 11834] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [2048, 1024] := by
    simp only [List.head?_cons, Option.map_some, Option.getD_some]
    exact hnorm.shard0_shape
  have hshapes : ∀ r (_ : r < 2),
      (([denoteGraphDistributedFaithful pm initPM 11833,
         denoteGraphDistributedFaithful pm initPM 11834] : List Tensor).getD r
         (zeroTensor [2048, 1024])).shape = [2048, 1024] := by
    intro r hr
    match r, hr with
    | 0, _ => rw [List.getD_cons_zero]; exact hnorm.shard0_shape
    | 1, _ => rw [List.getD_cons_succ, List.getD_cons_zero]; exact hnorm.shard1_shape
  have hofFn : (List.ofFn (n := 2) (fun r : Fin 2 =>
      (fw_inner_chunk_ce
        (([denoteGraphDistributedFaithful pm initPM 11833,
           denoteGraphDistributedFaithful pm initPM 11834] : List Tensor).getD r.val
             (zeroTensor [2048, 1024]))
        (denoteGraphDistributedFaithful pm initPM 5931)
        (denoteGraphDistributedFaithful pm initPM 4678) 154880
        ((0 : Nat) : Scalar)).snd)) =
      [ (fw_inner_chunk_ce (denoteGraphDistributedFaithful pm initPM 11833)
          (denoteGraphDistributedFaithful pm initPM 5931)
          (denoteGraphDistributedFaithful pm initPM 4678) 154880
          ((0 : Nat) : Scalar)).snd,
        (fw_inner_chunk_ce (denoteGraphDistributedFaithful pm initPM 11834)
          (denoteGraphDistributedFaithful pm initPM 5931)
          (denoteGraphDistributedFaithful pm initPM 4678) 154880
          ((0 : Nat) : Scalar)).snd ] := by
    simp only [List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.succ_zero_eq_one,
      Fin.val_one, List.getD_cons_zero, List.getD_cons_succ]
  rw [hnr, fw_inner_chunk_ce_snd_allGatherDim0_shards 2 2048 1024 154880
    ((0 : Nat) : Scalar)
    [denoteGraphDistributedFaithful pm initPM 11833,
     denoteGraphDistributedFaithful pm initPM 11834]
    (denoteGraphDistributedFaithful pm initPM 5931)
    (denoteGraphDistributedFaithful pm initPM 4678)
    (by decide) (by decide) (by decide) (by decide) hhead hshapes hw, hofFn]

/-! ### `goal_1` — the loss head

`fw_inner_chunk_ce.fst` reads `logits[l, y[l]]`, so this one carries the
caller-side label bound, exactly as `Pattern_1` does on the cut graph.
-/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_goal_4673_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2)
    (hx0 : (denoteGraphDistributedFaithful pm initPM 13257).shape.getD 0 0 = 2048)
    (hlabels : ∀ l < 2048 * 2,
      scalarToNat (valAt (denoteGraphDistributedFaithful pm initPM 4678) l) < 154880) :
    denoteGraphDistributedFaithful sm initSM 4673 =
      denoteGraphDistributedFaithful pm initPM 4673 := by
  have hnorm := recon_goal_5930_faithful_tids initSM initPM hSM hPM hInit hValues hCu hx0
  have hw : (denoteGraphDistributedFaithful pm initPM 5931).shape = [154880, 1024] :=
    l23hd_pm_input_shape initPM hPM 5931 [154880, 1024] (by native_decide)
      (l23hd_pm_input_fixed 5931 (by decide))
  have hy : (denoteGraphDistributedFaithful pm initPM 4678).shape = [2048 * 2] :=
    l23hd_pm_input_shape initPM hPM 4678 [4096] (by native_decide)
      (l23hd_pm_input_fixed 4678 (by decide))
  have hvocab : ((denoteGraphDistributedFaithful pm initPM 5931).shape.head?).getD 0 = 154880 := by
    rw [hw]; rfl
  have hnr : pm.numRanks = 2 := rfl
  rw [l23hd_red_sm4673 initSM, l23hd_red_pm4673 initPM,
    l23hd_red_pm11837 initPM, l23hd_red_pm11838 initPM,
    l23hd_red_pm11835 initPM, l23hd_red_pm11836 initPM,
    l23hd_w5931 initSM initPM hInit, l23hd_w4678 initSM initPM hInit,
    hnorm.value, hvocab, hnr]
  exact fw_inner_chunk_ce_fst_allGather0_commute_2_of
    (denoteGraphDistributedFaithful pm initPM 11833)
    (denoteGraphDistributedFaithful pm initPM 11834)
    (denoteGraphDistributedFaithful pm initPM 5931)
    (denoteGraphDistributedFaithful pm initPM 4678)
    2048 1024 154880 (by decide) (by decide) (by decide)
    hnorm.shard0_shape hnorm.shard1_shape hw hy hlabels ((0 : Nat) : Scalar)

end

end TrainVerify.Denote.GeneratedPatterns
