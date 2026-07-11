#!/usr/bin/env python3
"""
Generate L12 theorem skeleton from mk_attention macro template.

This script generates a starting point for the L12 attention commute theorem
by applying the tid mappings we've discovered to the mk_attention macro structure.
"""

import re

# TID mapping table (from STATUS.md)
tid_map_sm = {
    4844: 5330,  # carry
    4846: 5332,  # rms_out (main)
    # Note: 4852-4858 have non-uniform offsets, map individually:
    4852: 5344,  # v_in
    4854: 5342,  # q_in
    4855: 5343,  # k_in
    4856: 5345,  # cu_q
    4857: 5346,  # cu_k
    4858: 5347,  # attn_out
}

tid_map_pm = {
    7995: 9687,  # attn_out_r0
    7996: 9688,  # attn_out_r1
    7991: 9659,  # q_in_r0 (needs verification)
    7992: 9660,  # q_in_r1 (needs verification)
}

print("""
/-
  L12 Zigzag Attention Commute — SKELETON GENERATED FROM mk_attention TEMPLATE
  
  This is a STARTING POINT. You MUST:
  1. Fill in all the (???) placeholders with correct tids from Goal_3.lean
  2. Verify every tid substitution against the graph
  3. Add missing helper theorems (qproj_L12, kproj_L12, vproj_L12, etc.)
  4. Replace ALL _sliding_window_ lemmas with _zigzag_ equivalents
  5. Change params [16, 4, 64, 64, 1, 512] → [16, 4, 64, 64, 1, 0]
  6. Fix all type errors
  
  DO NOT blindly copy-paste. This is a GUIDE, not a working proof.
-/

theorem sm_pm_attention_L12_commute
    (initSM initPM : Store)
    (h_ss_sm : StoreShapesHold initSM sm_goal_3InitEnv)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM) :
    denoteGraph_ringAttn sm_goal_3 initSM 5347  -- ← L12 SM attention output
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 9687,  -- ← L12 PM rank0 output
           denoteGraph_ringAttn pm_goal_3 initPM 9688] := by  -- ← L12 PM rank1 output
  -- Weight equalities (cu_seqlens)
  have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
    fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
  have hb : ∀ g : LineageGoal, g ∈ initGoals → g.tps = [{ rank := 0, tid := g.ts }] →
      initSM g.ts = initPM g.ts := by
    intro g hg hshape
    have hgh := hII g hg
    unfold InitGoalHolds at hgh
    obtain ⟨_, _, hval⟩ := hgh
    rw [hshape] at hval
    simpa [List.map, reconstructWithDim_singleton] using hval
  have h5345 : initSM 5345 = initPM 5345 := hb initGoal_5345 (by decide) rfl
  have h5346 : initSM 5346 = initPM 5346 := hb initGoal_5346 (by decide) rfl
  
  -- Projection commutes (YOU MUST PROVE THESE FIRST!)
  have qproj := sm_pm_qproj_L12_commute initSM initPM h_ss_sm h_ss_pm hInit
  have kproj := sm_pm_kproj_L12_commute initSM initPM h_ss_sm h_ss_pm hInit
  have vproj := sm_pm_vproj_L12_commute initSM initPM h_ss_sm h_ss_pm hInit
  
  -- Store <-> prefix-fold bridges for SM inputs
  -- ??? = take count (find by grepping Goal_3.lean for node index)
  have bSM5342 : (sm_goal_3.nodes.take ???).foldl (applyNodeRingAttn sm_goal_3) initSM 5342
      = denoteGraph_ringAttn sm_goal_3 initSM 5342 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5342 ??? (by decide) (by decide)).symm
  have bSM5343 : (sm_goal_3.nodes.take ???).foldl (applyNodeRingAttn sm_goal_3) initSM 5343
      = denoteGraph_ringAttn sm_goal_3 initSM 5343 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5343 ??? (by decide) (by decide)).symm
  have bSM5344 : (sm_goal_3.nodes.take ???).foldl (applyNodeRingAttn sm_goal_3) initSM 5344
      = denoteGraph_ringAttn sm_goal_3 initSM 5344 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5344 ??? (by decide) (by decide)).symm
  
  -- PM bridges (??? = PM take count)
  have bPM9659_r0 : (pm_goal_3.nodes.take ???).foldl (applyNodeRingAttn pm_goal_3) initPM 9659
      = denoteGraph_ringAttn pm_goal_3 initPM 9659 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9659 ??? (by decide) (by decide)).symm
  have bPM9660_r1 : (pm_goal_3.nodes.take ???).foldl (applyNodeRingAttn pm_goal_3) initPM 9660
      = denoteGraph_ringAttn pm_goal_3 initPM 9660 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9660 ??? (by decide) (by decide)).symm
  -- ... (add more PM bridges for k/v as needed)
  
  -- Store-level q/k/v full hypotheses (from qproj/kproj/vproj commutes)
  have hq_full : (sm_goal_3.nodes.take ???).foldl (applyNodeRingAttn sm_goal_3) initSM 5342
      = allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take ???).foldl (applyNodeRingAttn pm_goal_3) initPM 9659,  -- ← q_r0
           (pm_goal_3.nodes.take ???).foldl (applyNodeRingAttn pm_goal_3) initPM 9660] := by  -- ← q_r1
    rw [bSM5342, bPM9659_r0, bPM9660_r1]; exact qproj
  -- ... (similar for hk_full, hv_full)
  
  -- Attention output shape (for fw_attn_varlen shape proof)
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take ???).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_12.ins.getD 0 0),
                                  (pm_goal_3.nodes.take ???).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_12.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take ???).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_12.ins.getD 1 0),
                                  (pm_goal_3.nodes.take ???).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_12.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [(pm_goal_3.nodes.take ???).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_12.ins.getD 2 0),
                                  (pm_goal_3.nodes.take ???).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_12.ins.getD 2 0)])
        ((pm_goal_3.nodes.take ???).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_12.ins.getD 3 0))
        ((pm_goal_3.nodes.take ???).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_12.ins.getD 4 0))
        (nR0_12.params.getD 0 1) (nR0_12.params.getD 1 1) (nR0_12.params.getD 2 1) (nR0_12.params.getD 3 1)
        (decide (nR0_12.params.getD 4 0 ≠ 0)) (nR0_12.params.getD 5 0)).shape
      = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    -- ... (fill in shape proof)
    sorry
  
  -- *** KEY CHANGE: Use _zigzag_ instead of _sliding_window_ ***
  have hrec := applyNodeRingAttn_zigzag_reconstruction_2_of_buddy_pair  -- ← _zigzag_ here!
    sm_goal_3 pm_goal_3
    ((sm_goal_3.nodes.take ???).foldl (applyNodeRingAttn sm_goal_3) initSM)
    ((pm_goal_3.nodes.take ???).foldl (applyNodeRingAttn pm_goal_3) initPM)
    nSM_12 nR0_12 nR1_12  -- ← Use L12 node defs
    2048 16 64 (by omega) (by omega) (by omega)
    buddy_sm_12 buddy_r0_12 buddy_r1_12  -- ← L12 buddy proofs
    (by decide) (by decide)
    hq_sm hk_sm hv_sm hq_full hk_full hv_full
    hcuQ_sm_pm hcuK_sm_pm rfl rfl rfl rfl hfull_shape
  
  -- Denote <-> applyNode bridges
  -- *** CHANGE params [16, 4, 64, 64, 1, 512] → [16, 4, 64, 64, 1, 0] ***
  have hbridge_sm : denoteGraph_ringAttn sm_goal_3 initSM 5347
      = applyNodeRingAttn_zigzag sm_goal_3  -- ← _zigzag_ here!
          ((sm_goal_3.nodes.take ???).foldl (applyNodeRingAttn sm_goal_3) initSM) nSM_12 := by
    rw [show denoteGraph_ringAttn sm_goal_3 initSM 5347
        = (sm_goal_3.nodes.take ???).foldl (applyNodeRingAttn sm_goal_3) initSM 5347 from
        foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5347 ??? (by decide) (by decide)]
    rw [show sm_goal_3.nodes.take ??? = sm_goal_3.nodes.take ??? ++ [nSM_12] from rfl,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact applyNodeRingAttn_zigzag_out sm_goal_3 _ 0 5342 5343 5344 5345 5346 5347 [16, 4, 64, 64, 1, 0]  -- ← params!
  
  -- ... (similar for hbridge_r0, hbridge_r1)
  
  rw [hbridge_sm, hrec, (bridge_r1 : _), hbridge_r0, hbridge_r1_denote]
""")

print("\n" + "="*80)
print("NEXT STEPS:")
print("="*80)
print("""
1. Find the 'take' counts by grepping Goal_3.lean:
   - For SM: Count nodes up to line 539 (should be ~504-505)
   - For PM: Count nodes up to line 2010 (should be ~1970-1971)

2. Fill in ALL the ??? placeholders

3. Prove the helper theorems FIRST:
   - mk_qproj 12 (or hand-write if macro fails)
   - mk_kproj 12
   - mk_vproj 12
   - mk_carry_a 12

4. Complete the shape proofs (hSM???sh, hfull_shape, etc.)

5. Add the bridge_r1 proof (similar to L3)

6. Test build and fix type errors iteratively

7. Once working, copy buddy proofs from Pattern_3_L12_spike.lean
""")
