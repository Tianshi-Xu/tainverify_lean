/- Goal_145 proof. The per-node lemmas live in Goal_145_<name>.lean; see the note
   in any of them for why v4.31 needs them in separate modules.
   Proof body is the v4.27-verified proof from commit c4f01699. -/
import denote.gpt_ly4_regen.Goal_145_hbw0
import denote.gpt_ly4_regen.Goal_145_hbw1
import denote.gpt_ly4_regen.Goal_145_hbw2
import denote.gpt_ly4_regen.Goal_145_hbw3
import denote.gpt_ly4_regen.Goal_145_hpm0base
import denote.gpt_ly4_regen.Goal_145_hpm1base
import denote.gpt_ly4_regen.Goal_145_hpm2base
import denote.gpt_ly4_regen.Goal_145_hpm3base

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem prove_goal_145_cut : goal_145_stmt_cut := by
  intro initSM initPM hSmInit hPmInit hInitGoals
  -- goal_146: tensor 764 (= g) is the dim-2 gather of shards 1651/1654/1657/1660
  have hInit146 : InitGoalHolds pm_goal_145.numRanks goal_146 initSM initPM := by
    apply hInitGoals
    simp only [goal_145_cut_initGoals, goal_145_prereqs]
    decide
  have h764_shape : (initSM 764).shape = [1, 8, 32] := hInit146.1
  have hs764 := hInit146.2.1
  simp only [goal_146, List.map, List.cons.injEq, and_true] at hs764
  obtain ⟨h1651_shape, h1654_shape, h1657_shape, h1660_shape⟩ := hs764
  have h764_gather : initSM 764 = allGatherPrimDimN 2 4 0
      [initPM 1651, initPM 1654, initPM 1657, initPM 1660] := by
    have hrec := hInit146.2.2
    simp only [goal_146, pm_goal_145, List.map] at hrec
    rw [hrec]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
    exact reconstructWithDim_cons_cons_nonscalar 2 4 0 _ _ _ (by rw [h1651_shape]; decide)
  -- shapes of the first AllToAll inputs (1605..1608) and y=601
  have h601_shape : (initSM 601).shape = [1, 8, 32] := hSmInit 601 [1, 8, 32] (by decide)
  have h1605_shape : (initPM 1605).shape = [1, 2, 32] := hPmInit 1605 [1, 2, 32] (by decide)
  -- SM store: 763 = dY = bw_add2 .2, which equals the gradient (g.shape = y.shape)
  have hsm : (denoteGraph sm_goal_145 initSM) 763 =
      (bw_add2 (initSM 764) (initSM 938) (initSM 601)).2 := by
    simp only [sm_goal_145, denoteGraph, List.foldl]
    rw [applyNode_bw_add2_snd_out_g145 _ _ 0 764 938 601 939 763 (by decide)]
  have hdy_sm : (bw_add2 (initSM 764) (initSM 938) (initSM 601)).2 = initSM 764 :=
    bw_add2_snd_same_shape_g145 _ _ _ (by rw [h764_shape, h601_shape])
  -- shape of the per-rank inner AllToAll (dims 1→2) producing the BW_add y input
  have hata0_shape : (allToAllPrimWithDims 4 0
      [initPM 1605, initPM 1606, initPM 1607, initPM 1608] 1 2).shape = [1, 8, 8] := by
    rw [allToAllPrimWithDims_shape 4 0 _ 1 2 [1, 2, 32] (by simp [h1605_shape]) (by omega)]
    simp [List.set, List.getD]
  -- PM: per-rank BW_add second outputs in terms of init shards
  have hbw0 := hbw0_145 initPM
  have hbw1 := hbw1_145 initPM
  have hbw2 := hbw2_145 initPM
  have hbw3 := hbw3_145 initPM
  -- the inner AllToAll has the same shape across ranks; each BW_add .2 = local g-shard
  have hata_shape : ∀ r, (allToAllPrimWithDims 4 r
      [initPM 1605, initPM 1606, initPM 1607, initPM 1608] 1 2).shape = [1, 8, 8] := by
    intro r
    rw [allToAllPrimWithDims_shape 4 r _ 1 2 [1, 2, 32] (by simp [h1605_shape]) (by omega)]
    simp [List.set, List.getD]
  have hbw0val : (denoteGraph pm_goal_145 initPM) 1650 = initPM 1651 := by
    rw [hbw0, bw_add2_snd_same_shape_g145 _ _ _ (by rw [h1651_shape, hata_shape 0])]
  have hbw1val : (denoteGraph pm_goal_145 initPM) 1653 = initPM 1654 := by
    rw [hbw1, bw_add2_snd_same_shape_g145 _ _ _ (by rw [h1654_shape, hata_shape 1])]
  have hbw2val : (denoteGraph pm_goal_145 initPM) 1656 = initPM 1657 := by
    rw [hbw2, bw_add2_snd_same_shape_g145 _ _ _ (by rw [h1657_shape, hata_shape 2])]
  have hbw3val : (denoteGraph pm_goal_145 initPM) 1659 = initPM 1660 := by
    rw [hbw3, bw_add2_snd_same_shape_g145 _ _ _ (by rw [h1660_shape, hata_shape 3])]
  -- Final AllToAll (dims 2→1): re-chunk the BW outputs along dim 1
  have hpm0base := hpm0base_145 initPM
  have hpm1base := hpm1base_145 initPM
  have hpm2base := hpm2base_145 initPM
  have hpm3base := hpm3base_145 initPM
  -- AllToAll (dims 2→1) of the local g-shards = dim-1 chunk of initSM 764
  have hatap : ∀ r, allToAllPrimWithDims 4 r
      [initPM 1651, initPM 1654, initPM 1657, initPM 1660] 2 1 =
      chunkPrimDimN 1 4 r (initSM 764) := by
    intro r
    rw [h764_gather]
    simp only [allToAllPrimWithDims]
  have hpm0 : (denoteGraph pm_goal_145 initPM) 1619 = chunkPrimDimN 1 4 0 (initSM 764) := by
    rw [hpm0base, hbw0val, hbw1val, hbw2val, hbw3val, hatap 0]
  have hpm1 : (denoteGraph pm_goal_145 initPM) 1622 = chunkPrimDimN 1 4 1 (initSM 764) := by
    rw [hpm1base, hbw0val, hbw1val, hbw2val, hbw3val, hatap 1]
  have hpm2 : (denoteGraph pm_goal_145 initPM) 1625 = chunkPrimDimN 1 4 2 (initSM 764) := by
    rw [hpm2base, hbw0val, hbw1val, hbw2val, hbw3val, hatap 2]
  have hpm3 : (denoteGraph pm_goal_145 initPM) 1628 = chunkPrimDimN 1 4 3 (initSM 764) := by
    rw [hpm3base, hbw0val, hbw1val, hbw2val, hbw3val, hatap 3]
  -- chunk shapes
  have hchunkV : ∀ r, (chunkPrimDimN 1 4 r (initSM 764)).shape = [1, 2, 32] := by
    intro r
    rw [chunkPrimDimN_shape 1 4 r _ _ h764_shape (by omega)]
    simp [List.set, List.getD]
  -- Discharge the three conjuncts
  simp only [goal_145, LineageGoal.tsShape, LineageGoal.tps, LineageGoal.tpShapes,
    LineageGoal.gatherDim, List.map, Piece.tid]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsm, hdy_sm]; exact h764_shape
  · rw [hpm0, hpm1, hpm2, hpm3, hchunkV 0, hchunkV 1, hchunkV 2, hchunkV 3]
  · rw [hsm, hdy_sm, hpm0, hpm1, hpm2, hpm3]
    rw [show pm_goal_145.numRanks = 4 from rfl]
    rw [reconstructForGoal_of_not_replicated _ _ _ (by rfl)]
    rw [reconstructWithDim_cons_cons_nonscalar 1 4 0 _ _ _ (by rw [hchunkV 0]; decide)]
    exact (allGather_chunkPrimDimN_roundtrip_dim1_4_1_8_32_g145 _ h764_shape).symm

end TrainVerify.Denote.GeneratedGoals
