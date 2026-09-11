import TrainVerifyRuntimeWorldData
import TrainVerifyRuntimePrefix0000
import denote.SourceBWSumRead
import denote.SourceParameterFrame
namespace TrainVerify.Denote.RuntimeWorld
noncomputable section
set_option maxHeartbeats 500000
theorem backwardSeed_sm_63_read (s t : Store) (h : smDenoteWithInputs s = some t) :
    t 1375 = bw_sum (t 1320) (t 1319) := by
  apply SourceBWSumRead.bw_sum_value_of_split smGraph smScope smPeers smGraph.nodes
    smInputRequests (smInputRequests.take 63) (smInputRequests.drop 64) smNode_63
    0 1320 1319 1375 s t rfl ?_ rfl ?_ ?_ h
  · calc
      smInputRequests = smInputRequests.take 63 ++ smInputRequests.drop 63 := (List.take_append_drop 63 smInputRequests).symm
      _ = _ := rfl
  · change ∀ row ∈ smInputRequests.drop 63, 1320 ∉ row.1.outs
    decide
  · change ∀ row ∈ smInputRequests.drop 63, 1319 ∉ row.1.outs
    decide
#print axioms backwardSeed_sm_63_read
theorem backwardSeed_sm_63_seed (s t : Store) (h : smSeededDenoteWithInputs s = some t) :
    t 1320 = unitSeed := by
  have hf := SourceParameterFrame.runWithInputs_frame smGraph smScope smPeers
    smGraph.nodes smInputRequests (smInitialWithSeeds s) t 1320 (by decide) h
  exact hf.trans (smInitialWithSeeds_seed_0 s)
#print axioms backwardSeed_sm_63_seed
theorem backwardSeed_sm_63_broadcast (s t : Store) (h : smSeededDenoteWithInputs s = some t) :
    t 1375 = Tensor.mkShape (t 1319).shape (fun _ => 1) := by
  rw [backwardSeed_sm_63_read (smInitialWithSeeds s) t h, backwardSeed_sm_63_seed s t h]
  exact unitSeed_bw_sum (t 1319)
#print axioms backwardSeed_sm_63_broadcast
theorem backwardSeed_pm_107_read (s t : Store) (h : pmDenoteWithInputs s = some t) :
    t 282 = bw_sum (t 81) (t 280) := by
  apply SourceBWSumRead.bw_sum_value_of_split pmGraph pmScope pmPeers pmGraph.nodes
    pmInputRequests (pmInputRequests.take 213) (pmInputRequests.drop 214) pmNode_107
    0 81 280 282 s t rfl ?_ rfl ?_ ?_ h
  · calc
      pmInputRequests = pmInputRequests.take 213 ++ pmInputRequests.drop 213 := (List.take_append_drop 213 pmInputRequests).symm
      _ = _ := rfl
  · change ∀ row ∈ pmInputRequests.drop 213, 81 ∉ row.1.outs
    decide
  · change ∀ row ∈ pmInputRequests.drop 213, 280 ∉ row.1.outs
    decide
#print axioms backwardSeed_pm_107_read
theorem backwardSeed_pm_107_seed (s t : Store) (h : pmSeededDenoteWithInputs s = some t) :
    t 81 = unitSeed := by
  have hf := SourceParameterFrame.runWithInputs_frame pmGraph pmScope pmPeers
    pmGraph.nodes pmInputRequests (pmInitialWithSeeds s) t 81 (by decide) h
  exact hf.trans (pmInitialWithSeeds_seed_0 s)
#print axioms backwardSeed_pm_107_seed
theorem backwardSeed_pm_107_broadcast (s t : Store) (h : pmSeededDenoteWithInputs s = some t) :
    t 282 = Tensor.mkShape (t 280).shape (fun _ => 1) := by
  rw [backwardSeed_pm_107_read (pmInitialWithSeeds s) t h, backwardSeed_pm_107_seed s t h]
  exact unitSeed_bw_sum (t 280)
#print axioms backwardSeed_pm_107_broadcast
theorem backwardSeed_pm_343_read (s t : Store) (h : pmDenoteWithInputs s = some t) :
    t 585 = bw_sum (t 384) (t 583) := by
  apply SourceBWSumRead.bw_sum_value_of_split pmGraph pmScope pmPeers pmGraph.nodes
    pmInputRequests (pmInputRequests.take 215) (pmInputRequests.drop 216) pmNode_343
    1 384 583 585 s t rfl ?_ rfl ?_ ?_ h
  · calc
      pmInputRequests = pmInputRequests.take 215 ++ pmInputRequests.drop 215 := (List.take_append_drop 215 pmInputRequests).symm
      _ = _ := rfl
  · change ∀ row ∈ pmInputRequests.drop 215, 384 ∉ row.1.outs
    decide
  · change ∀ row ∈ pmInputRequests.drop 215, 583 ∉ row.1.outs
    decide
#print axioms backwardSeed_pm_343_read
theorem backwardSeed_pm_343_seed (s t : Store) (h : pmSeededDenoteWithInputs s = some t) :
    t 384 = unitSeed := by
  have hf := SourceParameterFrame.runWithInputs_frame pmGraph pmScope pmPeers
    pmGraph.nodes pmInputRequests (pmInitialWithSeeds s) t 384 (by decide) h
  exact hf.trans (pmInitialWithSeeds_seed_1 s)
#print axioms backwardSeed_pm_343_seed
theorem backwardSeed_pm_343_broadcast (s t : Store) (h : pmSeededDenoteWithInputs s = some t) :
    t 585 = Tensor.mkShape (t 583).shape (fun _ => 1) := by
  rw [backwardSeed_pm_343_read (pmInitialWithSeeds s) t h, backwardSeed_pm_343_seed s t h]
  exact unitSeed_bw_sum (t 583)
#print axioms backwardSeed_pm_343_broadcast
theorem backwardSeed_pm_579_read (s t : Store) (h : pmDenoteWithInputs s = some t) :
    t 888 = bw_sum (t 687) (t 886) := by
  apply SourceBWSumRead.bw_sum_value_of_split pmGraph pmScope pmPeers pmGraph.nodes
    pmInputRequests (pmInputRequests.take 635) (pmInputRequests.drop 636) pmNode_579
    2 687 886 888 s t rfl ?_ rfl ?_ ?_ h
  · calc
      pmInputRequests = pmInputRequests.take 635 ++ pmInputRequests.drop 635 := (List.take_append_drop 635 pmInputRequests).symm
      _ = _ := rfl
  · change ∀ row ∈ pmInputRequests.drop 635, 687 ∉ row.1.outs
    decide
  · change ∀ row ∈ pmInputRequests.drop 635, 886 ∉ row.1.outs
    decide
#print axioms backwardSeed_pm_579_read
theorem backwardSeed_pm_579_seed (s t : Store) (h : pmSeededDenoteWithInputs s = some t) :
    t 687 = unitSeed := by
  have hf := SourceParameterFrame.runWithInputs_frame pmGraph pmScope pmPeers
    pmGraph.nodes pmInputRequests (pmInitialWithSeeds s) t 687 (by decide) h
  exact hf.trans (pmInitialWithSeeds_seed_2 s)
#print axioms backwardSeed_pm_579_seed
theorem backwardSeed_pm_579_broadcast (s t : Store) (h : pmSeededDenoteWithInputs s = some t) :
    t 888 = Tensor.mkShape (t 886).shape (fun _ => 1) := by
  rw [backwardSeed_pm_579_read (pmInitialWithSeeds s) t h, backwardSeed_pm_579_seed s t h]
  exact unitSeed_bw_sum (t 886)
#print axioms backwardSeed_pm_579_broadcast
theorem backwardSeed_pm_815_read (s t : Store) (h : pmDenoteWithInputs s = some t) :
    t 1191 = bw_sum (t 990) (t 1189) := by
  apply SourceBWSumRead.bw_sum_value_of_split pmGraph pmScope pmPeers pmGraph.nodes
    pmInputRequests (pmInputRequests.take 637) (pmInputRequests.drop 638) pmNode_815
    3 990 1189 1191 s t rfl ?_ rfl ?_ ?_ h
  · calc
      pmInputRequests = pmInputRequests.take 637 ++ pmInputRequests.drop 637 := (List.take_append_drop 637 pmInputRequests).symm
      _ = _ := rfl
  · change ∀ row ∈ pmInputRequests.drop 637, 990 ∉ row.1.outs
    decide
  · change ∀ row ∈ pmInputRequests.drop 637, 1189 ∉ row.1.outs
    decide
#print axioms backwardSeed_pm_815_read
theorem backwardSeed_pm_815_seed (s t : Store) (h : pmSeededDenoteWithInputs s = some t) :
    t 990 = unitSeed := by
  have hf := SourceParameterFrame.runWithInputs_frame pmGraph pmScope pmPeers
    pmGraph.nodes pmInputRequests (pmInitialWithSeeds s) t 990 (by decide) h
  exact hf.trans (pmInitialWithSeeds_seed_3 s)
#print axioms backwardSeed_pm_815_seed
theorem backwardSeed_pm_815_broadcast (s t : Store) (h : pmSeededDenoteWithInputs s = some t) :
    t 1191 = Tensor.mkShape (t 1189).shape (fun _ => 1) := by
  rw [backwardSeed_pm_815_read (pmInitialWithSeeds s) t h, backwardSeed_pm_815_seed s t h]
  exact unitSeed_bw_sum (t 1189)
#print axioms backwardSeed_pm_815_broadcast
end
end TrainVerify.Denote.RuntimeWorld
