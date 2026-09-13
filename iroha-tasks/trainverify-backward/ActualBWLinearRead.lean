import TrainVerifyRuntimeWorldData
import denote.SourceBWLinearRead
namespace TrainVerify.Denote.RuntimeWorld
noncomputable section
set_option maxHeartbeats 500000
theorem backwardLinearRead_sm_64_dx (s t : Store) (h : smDenoteWithInputs s = some t) :
    t 1374 = (bw_linear (t 1375) (t 1318) (t 1236)).1 := by
  apply SourceBWLinearRead.bw_linear_dx_value_of_split smGraph smScope smPeers smGraph.nodes
    smInputRequests (smInputRequests.take 64) (smInputRequests.drop 65) smNode_64
    0 1375 1318 1236 1374 1261 s t rfl ?_ rfl (by decide) ?_ ?_ ?_ h
  · calc
      smInputRequests = smInputRequests.take 64 ++ smInputRequests.drop 64 := (List.take_append_drop 64 smInputRequests).symm
      _ = _ := rfl
  · change ∀ row ∈ smInputRequests.drop 64, 1375 ∉ row.1.outs
    decide
  · change ∀ row ∈ smInputRequests.drop 64, 1318 ∉ row.1.outs
    decide
  · change ∀ row ∈ smInputRequests.drop 64, 1236 ∉ row.1.outs
    decide
#print axioms backwardLinearRead_sm_64_dx
theorem backwardLinearRead_sm_64_dw (s t : Store) (h : smDenoteWithInputs s = some t) :
    t 1261 = (bw_linear (t 1375) (t 1318) (t 1236)).2 := by
  apply SourceBWLinearRead.bw_linear_dw_value_of_split smGraph smScope smPeers smGraph.nodes
    smInputRequests (smInputRequests.take 64) (smInputRequests.drop 65) smNode_64
    0 1375 1318 1236 1374 1261 s t rfl ?_ rfl (by decide) ?_ ?_ ?_ h
  · calc
      smInputRequests = smInputRequests.take 64 ++ smInputRequests.drop 64 := (List.take_append_drop 64 smInputRequests).symm
      _ = _ := rfl
  · change ∀ row ∈ smInputRequests.drop 64, 1375 ∉ row.1.outs
    decide
  · change ∀ row ∈ smInputRequests.drop 64, 1318 ∉ row.1.outs
    decide
  · change ∀ row ∈ smInputRequests.drop 64, 1236 ∉ row.1.outs
    decide
#print axioms backwardLinearRead_sm_64_dw
theorem backwardLinearRead_pm_109_dx (s t : Store) (h : pmDenoteWithInputs s = some t) :
    t 279 = (bw_linear (t 278) (t 80) (t 72)).1 := by
  apply SourceBWLinearRead.bw_linear_dx_value_of_split pmGraph pmScope pmPeers pmGraph.nodes
    pmInputRequests (pmInputRequests.take 217) (pmInputRequests.drop 218) pmNode_109
    0 278 80 72 279 73 s t rfl ?_ rfl (by decide) ?_ ?_ ?_ h
  · calc
      pmInputRequests = pmInputRequests.take 217 ++ pmInputRequests.drop 217 := (List.take_append_drop 217 pmInputRequests).symm
      _ = _ := rfl
  · change ∀ row ∈ pmInputRequests.drop 217, 278 ∉ row.1.outs
    decide
  · change ∀ row ∈ pmInputRequests.drop 217, 80 ∉ row.1.outs
    decide
  · change ∀ row ∈ pmInputRequests.drop 217, 72 ∉ row.1.outs
    decide
#print axioms backwardLinearRead_pm_109_dx
theorem backwardLinearRead_pm_109_dw (s t : Store) (h : pmDenoteWithInputs s = some t) :
    t 73 = (bw_linear (t 278) (t 80) (t 72)).2 := by
  apply SourceBWLinearRead.bw_linear_dw_value_of_split pmGraph pmScope pmPeers pmGraph.nodes
    pmInputRequests (pmInputRequests.take 217) (pmInputRequests.drop 218) pmNode_109
    0 278 80 72 279 73 s t rfl ?_ rfl (by decide) ?_ ?_ ?_ h
  · calc
      pmInputRequests = pmInputRequests.take 217 ++ pmInputRequests.drop 217 := (List.take_append_drop 217 pmInputRequests).symm
      _ = _ := rfl
  · change ∀ row ∈ pmInputRequests.drop 217, 278 ∉ row.1.outs
    decide
  · change ∀ row ∈ pmInputRequests.drop 217, 80 ∉ row.1.outs
    decide
  · change ∀ row ∈ pmInputRequests.drop 217, 72 ∉ row.1.outs
    decide
#print axioms backwardLinearRead_pm_109_dw
theorem backwardLinearRead_pm_345_dx (s t : Store) (h : pmDenoteWithInputs s = some t) :
    t 581 = (bw_linear (t 582) (t 383) (t 375)).1 := by
  apply SourceBWLinearRead.bw_linear_dx_value_of_split pmGraph pmScope pmPeers pmGraph.nodes
    pmInputRequests (pmInputRequests.take 219) (pmInputRequests.drop 220) pmNode_345
    1 582 383 375 581 376 s t rfl ?_ rfl (by decide) ?_ ?_ ?_ h
  · calc
      pmInputRequests = pmInputRequests.take 219 ++ pmInputRequests.drop 219 := (List.take_append_drop 219 pmInputRequests).symm
      _ = _ := rfl
  · change ∀ row ∈ pmInputRequests.drop 219, 582 ∉ row.1.outs
    decide
  · change ∀ row ∈ pmInputRequests.drop 219, 383 ∉ row.1.outs
    decide
  · change ∀ row ∈ pmInputRequests.drop 219, 375 ∉ row.1.outs
    decide
#print axioms backwardLinearRead_pm_345_dx
theorem backwardLinearRead_pm_345_dw (s t : Store) (h : pmDenoteWithInputs s = some t) :
    t 376 = (bw_linear (t 582) (t 383) (t 375)).2 := by
  apply SourceBWLinearRead.bw_linear_dw_value_of_split pmGraph pmScope pmPeers pmGraph.nodes
    pmInputRequests (pmInputRequests.take 219) (pmInputRequests.drop 220) pmNode_345
    1 582 383 375 581 376 s t rfl ?_ rfl (by decide) ?_ ?_ ?_ h
  · calc
      pmInputRequests = pmInputRequests.take 219 ++ pmInputRequests.drop 219 := (List.take_append_drop 219 pmInputRequests).symm
      _ = _ := rfl
  · change ∀ row ∈ pmInputRequests.drop 219, 582 ∉ row.1.outs
    decide
  · change ∀ row ∈ pmInputRequests.drop 219, 383 ∉ row.1.outs
    decide
  · change ∀ row ∈ pmInputRequests.drop 219, 375 ∉ row.1.outs
    decide
#print axioms backwardLinearRead_pm_345_dw
theorem backwardLinearRead_pm_581_dx (s t : Store) (h : pmDenoteWithInputs s = some t) :
    t 885 = (bw_linear (t 884) (t 686) (t 678)).1 := by
  apply SourceBWLinearRead.bw_linear_dx_value_of_split pmGraph pmScope pmPeers pmGraph.nodes
    pmInputRequests (pmInputRequests.take 639) (pmInputRequests.drop 640) pmNode_581
    2 884 686 678 885 679 s t rfl ?_ rfl (by decide) ?_ ?_ ?_ h
  · calc
      pmInputRequests = pmInputRequests.take 639 ++ pmInputRequests.drop 639 := (List.take_append_drop 639 pmInputRequests).symm
      _ = _ := rfl
  · change ∀ row ∈ pmInputRequests.drop 639, 884 ∉ row.1.outs
    decide
  · change ∀ row ∈ pmInputRequests.drop 639, 686 ∉ row.1.outs
    decide
  · change ∀ row ∈ pmInputRequests.drop 639, 678 ∉ row.1.outs
    decide
#print axioms backwardLinearRead_pm_581_dx
theorem backwardLinearRead_pm_581_dw (s t : Store) (h : pmDenoteWithInputs s = some t) :
    t 679 = (bw_linear (t 884) (t 686) (t 678)).2 := by
  apply SourceBWLinearRead.bw_linear_dw_value_of_split pmGraph pmScope pmPeers pmGraph.nodes
    pmInputRequests (pmInputRequests.take 639) (pmInputRequests.drop 640) pmNode_581
    2 884 686 678 885 679 s t rfl ?_ rfl (by decide) ?_ ?_ ?_ h
  · calc
      pmInputRequests = pmInputRequests.take 639 ++ pmInputRequests.drop 639 := (List.take_append_drop 639 pmInputRequests).symm
      _ = _ := rfl
  · change ∀ row ∈ pmInputRequests.drop 639, 884 ∉ row.1.outs
    decide
  · change ∀ row ∈ pmInputRequests.drop 639, 686 ∉ row.1.outs
    decide
  · change ∀ row ∈ pmInputRequests.drop 639, 678 ∉ row.1.outs
    decide
#print axioms backwardLinearRead_pm_581_dw
theorem backwardLinearRead_pm_817_dx (s t : Store) (h : pmDenoteWithInputs s = some t) :
    t 1187 = (bw_linear (t 1188) (t 989) (t 981)).1 := by
  apply SourceBWLinearRead.bw_linear_dx_value_of_split pmGraph pmScope pmPeers pmGraph.nodes
    pmInputRequests (pmInputRequests.take 641) (pmInputRequests.drop 642) pmNode_817
    3 1188 989 981 1187 982 s t rfl ?_ rfl (by decide) ?_ ?_ ?_ h
  · calc
      pmInputRequests = pmInputRequests.take 641 ++ pmInputRequests.drop 641 := (List.take_append_drop 641 pmInputRequests).symm
      _ = _ := rfl
  · change ∀ row ∈ pmInputRequests.drop 641, 1188 ∉ row.1.outs
    decide
  · change ∀ row ∈ pmInputRequests.drop 641, 989 ∉ row.1.outs
    decide
  · change ∀ row ∈ pmInputRequests.drop 641, 981 ∉ row.1.outs
    decide
#print axioms backwardLinearRead_pm_817_dx
theorem backwardLinearRead_pm_817_dw (s t : Store) (h : pmDenoteWithInputs s = some t) :
    t 982 = (bw_linear (t 1188) (t 989) (t 981)).2 := by
  apply SourceBWLinearRead.bw_linear_dw_value_of_split pmGraph pmScope pmPeers pmGraph.nodes
    pmInputRequests (pmInputRequests.take 641) (pmInputRequests.drop 642) pmNode_817
    3 1188 989 981 1187 982 s t rfl ?_ rfl (by decide) ?_ ?_ ?_ h
  · calc
      pmInputRequests = pmInputRequests.take 641 ++ pmInputRequests.drop 641 := (List.take_append_drop 641 pmInputRequests).symm
      _ = _ := rfl
  · change ∀ row ∈ pmInputRequests.drop 641, 1188 ∉ row.1.outs
    decide
  · change ∀ row ∈ pmInputRequests.drop 641, 989 ∉ row.1.outs
    decide
  · change ∀ row ∈ pmInputRequests.drop 641, 981 ∉ row.1.outs
    decide
#print axioms backwardLinearRead_pm_817_dw
end
end TrainVerify.Denote.RuntimeWorld
