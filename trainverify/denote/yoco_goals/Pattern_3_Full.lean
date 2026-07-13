/- Pattern_3_Full.lean — aggregates the 12 zigzag-band spike proofs alongside Pattern_3.
   Downstream of Pattern_3 (imports it) and every Pattern_3_L{k}_spike.
   Enables sm_pm_router_commute_layer to reference sm_pm_router_commute_L{k}_full for k=12..23.
   Contains no new mathematical content — just import composition.
-/

import denote.yoco_goals.Pattern_3
import denote.yoco_goals.Pattern_3_L12_spike
import denote.yoco_goals.Pattern_3_L13_spike
import denote.yoco_goals.Pattern_3_L14_spike
import denote.yoco_goals.Pattern_3_L15_spike
import denote.yoco_goals.Pattern_3_L16_spike
import denote.yoco_goals.Pattern_3_L17_spike
import denote.yoco_goals.Pattern_3_L18_spike
import denote.yoco_goals.Pattern_3_L19_spike
import denote.yoco_goals.Pattern_3_L20_spike
import denote.yoco_goals.Pattern_3_L21_spike
import denote.yoco_goals.Pattern_3_L22_spike
import denote.yoco_goals.Pattern_3_L23_spike

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-! ## 24-way case split — the layer commute theorem body.

    Located here (not in Pattern_3.lean) because cases i=12..23 dispatch to
    `sm_pm_router_commute_L{k}_full` which live in the spike files.

    Named `_full` to avoid clashing with the still-`sorry` version at
    `Pattern_3.lean:8127`. Downstream (`Instances.lean`) will switch to
    `prove_pattern_3_full` once we're done. -/

set_option maxHeartbeats 8000000 in
theorem sm_pm_router_commute_layer_full
    (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hp5346 : initPM 5346 = cu_pin_value)
    (hp5395 : initPM 5395 = cu_pin_value)
    (hp5444 : initPM 5444 = cu_pin_value)
    (hp5493 : initPM 5493 = cu_pin_value)
    (hp5542 : initPM 5542 = cu_pin_value)
    (hp5591 : initPM 5591 = cu_pin_value)
    (hp5640 : initPM 5640 = cu_pin_value)
    (hp5689 : initPM 5689 = cu_pin_value)
    (hp5738 : initPM 5738 = cu_pin_value)
    (hp5787 : initPM 5787 = cu_pin_value)
    (hp5836 : initPM 5836 = cu_pin_value)
    (hp5885 : initPM 5885 = cu_pin_value) :
    ∀ i (_ : i < 24),
      (sm_goal_3_routers initSM).getD i (zeroTensor [2 * 2048, 64]) =
        allGatherPrimDimN 0 2 0
          [(pm_goal_3_routers_r0 initPM).getD i (zeroTensor [2048, 64]),
           (pm_goal_3_routers_r1 initPM).getD i (zeroTensor [2048, 64])] := by
  intro i hi
  interval_cases i
  · exact sm_pm_router_commute_L0 initSM initPM hSM hPM hInit
  · exact sm_pm_router_commute_L1 initSM initPM hSM hPM hInit
  · exact sm_pm_router_commute_L2 initSM initPM hSM hPM hInit
  · exact sm_pm_router_commute_L3 initSM initPM hSM hPM hInit
  · exact sm_pm_router_commute_L4 initSM initPM hSM hPM hInit
  · exact sm_pm_router_commute_L5 initSM initPM hSM hPM hInit
  · exact sm_pm_router_commute_L6 initSM initPM hSM hPM hInit
  · exact sm_pm_router_commute_L7 initSM initPM hSM hPM hInit
  · exact sm_pm_router_commute_L8 initSM initPM hSM hPM hInit
  · exact sm_pm_router_commute_L9 initSM initPM hSM hPM hInit
  · exact sm_pm_router_commute_L10 initSM initPM hSM hPM hInit
  · exact sm_pm_router_commute_L11 initSM initPM hSM hPM hInit
  · -- L12: h_bound only, no hcarry
    simp only [sm_goal_3_routers, pm_goal_3_routers_r0, pm_goal_3_routers_r1,
      List.getD_cons_succ, List.getD_cons_zero]
    have hbnd : ∀ t, (decodeCuSeqlens (initPM 5346)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5346
    exact sm_pm_router_commute_L12_full initSM initPM hSM hPM hInit hbnd
  · -- L13: h_bound(5395) + hcarry5387 + h9829/h9830 shape
    simp only [sm_goal_3_routers, pm_goal_3_routers_r0, pm_goal_3_routers_r1,
      List.getD_cons_succ, List.getD_cons_zero]
    have hbnd : ∀ t, (decodeCuSeqlens (initPM 5395)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5395
    have hcarry5387 := sm_pm_carry_5387_commute initSM initPM hSM hPM hInit hp5346
    have h9829 : (denoteGraph_ringAttn pm_goal_3 initPM 9829).shape = [2048, 1024] :=
      pm_goal_3_9829_shape initPM hPM
    have h9830 : (denoteGraph_ringAttn pm_goal_3 initPM 9830).shape = [2048, 1024] :=
      pm_goal_3_9830_shape initPM hPM
    exact sm_pm_router_commute_L13_full initSM initPM hSM hPM hInit hbnd hcarry5387 h9829 h9830
  · -- L14: h_bound(5444) + hcarry5436 + h10001/h10002 shape
    simp only [sm_goal_3_routers, pm_goal_3_routers_r0, pm_goal_3_routers_r1,
      List.getD_cons_succ, List.getD_cons_zero]
    have hbnd : ∀ t, (decodeCuSeqlens (initPM 5444)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5444
    have hcarry5436 := sm_pm_carry_5436_commute initSM initPM hSM hPM hInit hp5346 hp5395
    have h10001 : (denoteGraph_ringAttn pm_goal_3 initPM 10001).shape = [2048, 1024] :=
      pm_goal_3_10001_shape initPM hPM
    have h10002 : (denoteGraph_ringAttn pm_goal_3 initPM 10002).shape = [2048, 1024] :=
      pm_goal_3_10002_shape initPM hPM
    exact sm_pm_router_commute_L14_full initSM initPM hSM hPM hInit hcarry5436 h10001 h10002 hbnd
  · -- L15: hcarry5485 + h10173/h10174 shape + h_bound(5493)
    simp only [sm_goal_3_routers, pm_goal_3_routers_r0, pm_goal_3_routers_r1,
      List.getD_cons_succ, List.getD_cons_zero]
    have hbnd : ∀ t, (decodeCuSeqlens (initPM 5493)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5493
    have hcarry5485 := sm_pm_carry_5485_commute initSM initPM hSM hPM hInit hp5346 hp5395 hp5444
    have h10173 : (denoteGraph_ringAttn pm_goal_3 initPM 10173).shape = [2048, 1024] :=
      pm_goal_3_10173_shape initPM hPM
    have h10174 : (denoteGraph_ringAttn pm_goal_3 initPM 10174).shape = [2048, 1024] :=
      pm_goal_3_10174_shape initPM hPM
    exact sm_pm_router_commute_L15_full initSM initPM hSM hPM hInit hcarry5485 h10173 h10174 hbnd
  · -- L16: h_bound(5542) + hcarry5534 + h10345/h10346 shape
    simp only [sm_goal_3_routers, pm_goal_3_routers_r0, pm_goal_3_routers_r1,
      List.getD_cons_succ, List.getD_cons_zero]
    have hbnd : ∀ t, (decodeCuSeqlens (initPM 5542)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5542
    have hcarry5534 := sm_pm_carry_5534_commute initSM initPM hSM hPM hInit hp5346 hp5395 hp5444 hp5493
    have h10345 : (denoteGraph_ringAttn pm_goal_3 initPM 10345).shape = [2048, 1024] :=
      pm_goal_3_10345_shape initPM hPM
    have h10346 : (denoteGraph_ringAttn pm_goal_3 initPM 10346).shape = [2048, 1024] :=
      pm_goal_3_10346_shape initPM hPM
    exact sm_pm_router_commute_L16_full initSM initPM hSM hPM hInit hbnd hcarry5534 h10345 h10346
  · -- L17: h_bound(5591) + hcarry5583 (built from hcarry5534) + h10517/h10518 shape
    simp only [sm_goal_3_routers, pm_goal_3_routers_r0, pm_goal_3_routers_r1,
      List.getD_cons_succ, List.getD_cons_zero]
    have hbnd : ∀ t, (decodeCuSeqlens (initPM 5591)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5591
    have hbnd_prev : ∀ t, (decodeCuSeqlens (initPM 5542)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5542
    have hcarry5534 := sm_pm_carry_5534_commute initSM initPM hSM hPM hInit hp5346 hp5395 hp5444 hp5493
    have h10345 : (denoteGraph_ringAttn pm_goal_3 initPM 10345).shape = [2048, 1024] :=
      pm_goal_3_10345_shape initPM hPM
    have h10346 : (denoteGraph_ringAttn pm_goal_3 initPM 10346).shape = [2048, 1024] :=
      pm_goal_3_10346_shape initPM hPM
    have hcarry5583 := sm_pm_carry_5583_commute initSM initPM hSM hPM hInit
      hbnd_prev hcarry5534 h10345 h10346
    have h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10517).shape = [2048, 1024] :=
      pm_goal_3_10517_shape initPM hPM h10345
    have h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10518).shape = [2048, 1024] :=
      pm_goal_3_10518_shape initPM hPM h10346
    exact sm_pm_router_commute_L17_full initSM initPM hSM hPM hInit hbnd hcarry5583 h10517 h10518
  · -- L18: h_bound(5640) + hcarry5632 (built from hcarry5583) + h10689/h10690 shape
    simp only [sm_goal_3_routers, pm_goal_3_routers_r0, pm_goal_3_routers_r1,
      List.getD_cons_succ, List.getD_cons_zero]
    have hbnd : ∀ t, (decodeCuSeqlens (initPM 5640)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5640
    have hbnd_prev_prev : ∀ t, (decodeCuSeqlens (initPM 5542)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5542
    have hbnd_prev : ∀ t, (decodeCuSeqlens (initPM 5591)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5591
    have hcarry5534 := sm_pm_carry_5534_commute initSM initPM hSM hPM hInit hp5346 hp5395 hp5444 hp5493
    have h10345 : (denoteGraph_ringAttn pm_goal_3 initPM 10345).shape = [2048, 1024] :=
      pm_goal_3_10345_shape initPM hPM
    have h10346 : (denoteGraph_ringAttn pm_goal_3 initPM 10346).shape = [2048, 1024] :=
      pm_goal_3_10346_shape initPM hPM
    have hcarry5583 := sm_pm_carry_5583_commute initSM initPM hSM hPM hInit
      hbnd_prev_prev hcarry5534 h10345 h10346
    have h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10517).shape = [2048, 1024] :=
      pm_goal_3_10517_shape initPM hPM h10345
    have h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10518).shape = [2048, 1024] :=
      pm_goal_3_10518_shape initPM hPM h10346
    have hcarry5632 := sm_pm_carry_5632_commute initSM initPM hSM hPM hInit
      hbnd_prev hcarry5583 h10517 h10518
    have h10689 : (denoteGraph_ringAttn pm_goal_3 initPM 10689).shape = [2048, 1024] :=
      pm_goal_3_10689_shape initPM hPM h10517
    have h10690 : (denoteGraph_ringAttn pm_goal_3 initPM 10690).shape = [2048, 1024] :=
      pm_goal_3_10690_shape initPM hPM h10518
    exact sm_pm_router_commute_L18_full initSM initPM hSM hPM hInit hbnd hcarry5632 h10689 h10690
  · -- L19: h_bound(5689) + hcarry5681 (chain built from hcarry5534) + h10861/h10862 shape
    simp only [sm_goal_3_routers, pm_goal_3_routers_r0, pm_goal_3_routers_r1,
      List.getD_cons_succ, List.getD_cons_zero]
    have hbnd : ∀ t, (decodeCuSeqlens (initPM 5689)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5689
    have hbnd_5542 : ∀ t, (decodeCuSeqlens (initPM 5542)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5542
    have hbnd_5591 : ∀ t, (decodeCuSeqlens (initPM 5591)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5591
    have hbnd_5640 : ∀ t, (decodeCuSeqlens (initPM 5640)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5640
    have hcarry5534 := sm_pm_carry_5534_commute initSM initPM hSM hPM hInit hp5346 hp5395 hp5444 hp5493
    have h10345 : (denoteGraph_ringAttn pm_goal_3 initPM 10345).shape = [2048, 1024] :=
      pm_goal_3_10345_shape initPM hPM
    have h10346 : (denoteGraph_ringAttn pm_goal_3 initPM 10346).shape = [2048, 1024] :=
      pm_goal_3_10346_shape initPM hPM
    have hcarry5583 := sm_pm_carry_5583_commute initSM initPM hSM hPM hInit
      hbnd_5542 hcarry5534 h10345 h10346
    have h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10517).shape = [2048, 1024] :=
      pm_goal_3_10517_shape initPM hPM h10345
    have h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10518).shape = [2048, 1024] :=
      pm_goal_3_10518_shape initPM hPM h10346
    have hcarry5632 := sm_pm_carry_5632_commute initSM initPM hSM hPM hInit
      hbnd_5591 hcarry5583 h10517 h10518
    have h10689 : (denoteGraph_ringAttn pm_goal_3 initPM 10689).shape = [2048, 1024] :=
      pm_goal_3_10689_shape initPM hPM h10517
    have h10690 : (denoteGraph_ringAttn pm_goal_3 initPM 10690).shape = [2048, 1024] :=
      pm_goal_3_10690_shape initPM hPM h10518
    have hcarry5681 := sm_pm_carry_5681_commute initSM initPM hSM hPM hInit
      hbnd_5640 hcarry5632 h10689 h10690
    have h10861 : (denoteGraph_ringAttn pm_goal_3 initPM 10861).shape = [2048, 1024] :=
      pm_goal_3_10861_shape initPM hPM h10689
    have h10862 : (denoteGraph_ringAttn pm_goal_3 initPM 10862).shape = [2048, 1024] :=
      pm_goal_3_10862_shape initPM hPM h10690
    exact sm_pm_router_commute_L19_full initSM initPM hSM hPM hInit hbnd hcarry5681 h10861 h10862
  · -- L20: h_bound(5738) + hcarry5730 (chain) + h11033/h11034 shape
    simp only [sm_goal_3_routers, pm_goal_3_routers_r0, pm_goal_3_routers_r1,
      List.getD_cons_succ, List.getD_cons_zero]
    have hbnd : ∀ t, (decodeCuSeqlens (initPM 5738)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5738
    have hbnd_5542 : ∀ t, (decodeCuSeqlens (initPM 5542)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5542
    have hbnd_5591 : ∀ t, (decodeCuSeqlens (initPM 5591)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5591
    have hbnd_5640 : ∀ t, (decodeCuSeqlens (initPM 5640)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5640
    have hbnd_5689 : ∀ t, (decodeCuSeqlens (initPM 5689)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5689
    have hcarry5534 := sm_pm_carry_5534_commute initSM initPM hSM hPM hInit hp5346 hp5395 hp5444 hp5493
    have h10345 : (denoteGraph_ringAttn pm_goal_3 initPM 10345).shape = [2048, 1024] :=
      pm_goal_3_10345_shape initPM hPM
    have h10346 : (denoteGraph_ringAttn pm_goal_3 initPM 10346).shape = [2048, 1024] :=
      pm_goal_3_10346_shape initPM hPM
    have hcarry5583 := sm_pm_carry_5583_commute initSM initPM hSM hPM hInit
      hbnd_5542 hcarry5534 h10345 h10346
    have h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10517).shape = [2048, 1024] :=
      pm_goal_3_10517_shape initPM hPM h10345
    have h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10518).shape = [2048, 1024] :=
      pm_goal_3_10518_shape initPM hPM h10346
    have hcarry5632 := sm_pm_carry_5632_commute initSM initPM hSM hPM hInit
      hbnd_5591 hcarry5583 h10517 h10518
    have h10689 : (denoteGraph_ringAttn pm_goal_3 initPM 10689).shape = [2048, 1024] :=
      pm_goal_3_10689_shape initPM hPM h10517
    have h10690 : (denoteGraph_ringAttn pm_goal_3 initPM 10690).shape = [2048, 1024] :=
      pm_goal_3_10690_shape initPM hPM h10518
    have hcarry5681 := sm_pm_carry_5681_commute initSM initPM hSM hPM hInit
      hbnd_5640 hcarry5632 h10689 h10690
    have h10861 : (denoteGraph_ringAttn pm_goal_3 initPM 10861).shape = [2048, 1024] :=
      pm_goal_3_10861_shape initPM hPM h10689
    have h10862 : (denoteGraph_ringAttn pm_goal_3 initPM 10862).shape = [2048, 1024] :=
      pm_goal_3_10862_shape initPM hPM h10690
    have hcarry5730 := sm_pm_carry_5730_commute initSM initPM hSM hPM hInit
      hbnd_5689 hcarry5681 h10861 h10862
    have h11033 : (denoteGraph_ringAttn pm_goal_3 initPM 11033).shape = [2048, 1024] :=
      pm_goal_3_11033_shape initPM hPM h10861
    have h11034 : (denoteGraph_ringAttn pm_goal_3 initPM 11034).shape = [2048, 1024] :=
      pm_goal_3_11034_shape initPM hPM h10862
    exact sm_pm_router_commute_L20_full initSM initPM hSM hPM hInit hbnd hcarry5730 h11033 h11034
  · -- L21: h_bound(5787) + hcarry5779 (chain) + h11205/h11206 shape
    simp only [sm_goal_3_routers, pm_goal_3_routers_r0, pm_goal_3_routers_r1,
      List.getD_cons_succ, List.getD_cons_zero]
    have hbnd : ∀ t, (decodeCuSeqlens (initPM 5787)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5787
    have hbnd_5542 : ∀ t, (decodeCuSeqlens (initPM 5542)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5542
    have hbnd_5591 : ∀ t, (decodeCuSeqlens (initPM 5591)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5591
    have hbnd_5640 : ∀ t, (decodeCuSeqlens (initPM 5640)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5640
    have hbnd_5689 : ∀ t, (decodeCuSeqlens (initPM 5689)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5689
    have hbnd_5738 : ∀ t, (decodeCuSeqlens (initPM 5738)).getD (t+1) 0 ≤ 4096 :=
      cu_bound_of_value_pin _ hp5738
    have hcarry5534 := sm_pm_carry_5534_commute initSM initPM hSM hPM hInit hp5346 hp5395 hp5444 hp5493
    have h10345 : (denoteGraph_ringAttn pm_goal_3 initPM 10345).shape = [2048, 1024] :=
      pm_goal_3_10345_shape initPM hPM
    have h10346 : (denoteGraph_ringAttn pm_goal_3 initPM 10346).shape = [2048, 1024] :=
      pm_goal_3_10346_shape initPM hPM
    have hcarry5583 := sm_pm_carry_5583_commute initSM initPM hSM hPM hInit
      hbnd_5542 hcarry5534 h10345 h10346
    have h10517 : (denoteGraph_ringAttn pm_goal_3 initPM 10517).shape = [2048, 1024] :=
      pm_goal_3_10517_shape initPM hPM h10345
    have h10518 : (denoteGraph_ringAttn pm_goal_3 initPM 10518).shape = [2048, 1024] :=
      pm_goal_3_10518_shape initPM hPM h10346
    have hcarry5632 := sm_pm_carry_5632_commute initSM initPM hSM hPM hInit
      hbnd_5591 hcarry5583 h10517 h10518
    have h10689 : (denoteGraph_ringAttn pm_goal_3 initPM 10689).shape = [2048, 1024] :=
      pm_goal_3_10689_shape initPM hPM h10517
    have h10690 : (denoteGraph_ringAttn pm_goal_3 initPM 10690).shape = [2048, 1024] :=
      pm_goal_3_10690_shape initPM hPM h10518
    have hcarry5681 := sm_pm_carry_5681_commute initSM initPM hSM hPM hInit
      hbnd_5640 hcarry5632 h10689 h10690
    have h10861 : (denoteGraph_ringAttn pm_goal_3 initPM 10861).shape = [2048, 1024] :=
      pm_goal_3_10861_shape initPM hPM h10689
    have h10862 : (denoteGraph_ringAttn pm_goal_3 initPM 10862).shape = [2048, 1024] :=
      pm_goal_3_10862_shape initPM hPM h10690
    have hcarry5730 := sm_pm_carry_5730_commute initSM initPM hSM hPM hInit
      hbnd_5689 hcarry5681 h10861 h10862
    have h11033 : (denoteGraph_ringAttn pm_goal_3 initPM 11033).shape = [2048, 1024] :=
      pm_goal_3_11033_shape initPM hPM h10861
    have h11034 : (denoteGraph_ringAttn pm_goal_3 initPM 11034).shape = [2048, 1024] :=
      pm_goal_3_11034_shape initPM hPM h10862
    have hcarry5779 := sm_pm_carry_5779_commute initSM initPM hSM hPM hInit
      hbnd_5738 hcarry5730 h11033 h11034
    have h11205 : (denoteGraph_ringAttn pm_goal_3 initPM 11205).shape = [2048, 1024] :=
      pm_goal_3_11205_shape initPM hPM h11033
    have h11206 : (denoteGraph_ringAttn pm_goal_3 initPM 11206).shape = [2048, 1024] :=
      pm_goal_3_11206_shape initPM hPM h11034
    exact sm_pm_router_commute_L21_full initSM initPM hSM hPM hInit hbnd hcarry5779 h11205 h11206
  all_goals sorry

end TrainVerify.Denote.GeneratedPatterns
