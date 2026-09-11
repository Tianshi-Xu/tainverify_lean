import TrainVerifyRuntimeWorldData
import ActualBWLinearRead
import ActualBWSeedRead
import denote.SourcePrimitiveRead
namespace TrainVerify.Denote.RuntimeWorld
noncomputable section
set_option maxHeartbeats 500000
theorem backwardCotangent_pm_108_read (s t : Store) (h : pmDenoteWithInputs s = some t) :
    t 278 = AllToAllSourceFaithful.tensor 2 0 1 2 ([282, 585].map t) := by
  apply SourcePrimitiveRead.allToAll_value_of_split pmGraph pmScope pmPeers pmGraph.nodes
    pmInputRequests (pmInputRequests.take 216) (pmInputRequests.drop 217) pmNode_108
    0 [0, 1] [282, 585] 278 1 2 s t rfl ?_ rfl ?_ h
  · calc
      pmInputRequests = pmInputRequests.take 216 ++ pmInputRequests.drop 216 := (List.take_append_drop 216 pmInputRequests).symm
      _ = _ := rfl
  · change ∀ tid ∈ ([282, 585] : List Tid), ∀ row ∈ pmInputRequests.drop 216, tid ∉ row.1.outs
    decide
#print axioms backwardCotangent_pm_108_read
theorem backwardCotangent_pm_108_seeded (s t : Store) (h : pmSeededDenoteWithInputs s = some t) :
    t 278 = AllToAllSourceFaithful.tensor 2 0 1 2 [Tensor.mkShape (t 280).shape (fun _ => 1), Tensor.mkShape (t 583).shape (fun _ => 1)] := by
  rw [backwardCotangent_pm_108_read (pmInitialWithSeeds s) t h]
  simp only [List.map_cons, List.map_nil]
  rw [backwardSeed_pm_107_broadcast s t h, backwardSeed_pm_343_broadcast s t h]
#print axioms backwardCotangent_pm_108_seeded
theorem backwardCotangent_pm_108_dx (s t : Store) (h : pmSeededDenoteWithInputs s = some t) :
    t 279 = (bw_linear (AllToAllSourceFaithful.tensor 2 0 1 2 [Tensor.mkShape (t 280).shape (fun _ => 1), Tensor.mkShape (t 583).shape (fun _ => 1)]) (t 80) (t 72)).1 := by
  rw [backwardLinearRead_pm_109_dx (pmInitialWithSeeds s) t h, backwardCotangent_pm_108_seeded s t h]
#print axioms backwardCotangent_pm_108_dx
theorem backwardCotangent_pm_108_dw (s t : Store) (h : pmSeededDenoteWithInputs s = some t) :
    t 73 = (bw_linear (AllToAllSourceFaithful.tensor 2 0 1 2 [Tensor.mkShape (t 280).shape (fun _ => 1), Tensor.mkShape (t 583).shape (fun _ => 1)]) (t 80) (t 72)).2 := by
  rw [backwardLinearRead_pm_109_dw (pmInitialWithSeeds s) t h, backwardCotangent_pm_108_seeded s t h]
#print axioms backwardCotangent_pm_108_dw
theorem backwardCotangent_pm_344_read (s t : Store) (h : pmDenoteWithInputs s = some t) :
    t 582 = AllToAllSourceFaithful.tensor 2 1 1 2 ([282, 585].map t) := by
  apply SourcePrimitiveRead.allToAll_value_of_split pmGraph pmScope pmPeers pmGraph.nodes
    pmInputRequests (pmInputRequests.take 218) (pmInputRequests.drop 219) pmNode_344
    1 [0, 1] [282, 585] 582 1 2 s t rfl ?_ rfl ?_ h
  · calc
      pmInputRequests = pmInputRequests.take 218 ++ pmInputRequests.drop 218 := (List.take_append_drop 218 pmInputRequests).symm
      _ = _ := rfl
  · change ∀ tid ∈ ([282, 585] : List Tid), ∀ row ∈ pmInputRequests.drop 218, tid ∉ row.1.outs
    decide
#print axioms backwardCotangent_pm_344_read
theorem backwardCotangent_pm_344_seeded (s t : Store) (h : pmSeededDenoteWithInputs s = some t) :
    t 582 = AllToAllSourceFaithful.tensor 2 1 1 2 [Tensor.mkShape (t 280).shape (fun _ => 1), Tensor.mkShape (t 583).shape (fun _ => 1)] := by
  rw [backwardCotangent_pm_344_read (pmInitialWithSeeds s) t h]
  simp only [List.map_cons, List.map_nil]
  rw [backwardSeed_pm_107_broadcast s t h, backwardSeed_pm_343_broadcast s t h]
#print axioms backwardCotangent_pm_344_seeded
theorem backwardCotangent_pm_344_dx (s t : Store) (h : pmSeededDenoteWithInputs s = some t) :
    t 581 = (bw_linear (AllToAllSourceFaithful.tensor 2 1 1 2 [Tensor.mkShape (t 280).shape (fun _ => 1), Tensor.mkShape (t 583).shape (fun _ => 1)]) (t 383) (t 375)).1 := by
  rw [backwardLinearRead_pm_345_dx (pmInitialWithSeeds s) t h, backwardCotangent_pm_344_seeded s t h]
#print axioms backwardCotangent_pm_344_dx
theorem backwardCotangent_pm_344_dw (s t : Store) (h : pmSeededDenoteWithInputs s = some t) :
    t 376 = (bw_linear (AllToAllSourceFaithful.tensor 2 1 1 2 [Tensor.mkShape (t 280).shape (fun _ => 1), Tensor.mkShape (t 583).shape (fun _ => 1)]) (t 383) (t 375)).2 := by
  rw [backwardLinearRead_pm_345_dw (pmInitialWithSeeds s) t h, backwardCotangent_pm_344_seeded s t h]
#print axioms backwardCotangent_pm_344_dw
theorem backwardCotangent_pm_580_read (s t : Store) (h : pmDenoteWithInputs s = some t) :
    t 884 = AllToAllSourceFaithful.tensor 2 0 1 2 ([888, 1191].map t) := by
  apply SourcePrimitiveRead.allToAll_value_of_split pmGraph pmScope pmPeers pmGraph.nodes
    pmInputRequests (pmInputRequests.take 638) (pmInputRequests.drop 639) pmNode_580
    2 [2, 3] [888, 1191] 884 1 2 s t rfl ?_ rfl ?_ h
  · calc
      pmInputRequests = pmInputRequests.take 638 ++ pmInputRequests.drop 638 := (List.take_append_drop 638 pmInputRequests).symm
      _ = _ := rfl
  · change ∀ tid ∈ ([888, 1191] : List Tid), ∀ row ∈ pmInputRequests.drop 638, tid ∉ row.1.outs
    decide
#print axioms backwardCotangent_pm_580_read
theorem backwardCotangent_pm_580_seeded (s t : Store) (h : pmSeededDenoteWithInputs s = some t) :
    t 884 = AllToAllSourceFaithful.tensor 2 0 1 2 [Tensor.mkShape (t 886).shape (fun _ => 1), Tensor.mkShape (t 1189).shape (fun _ => 1)] := by
  rw [backwardCotangent_pm_580_read (pmInitialWithSeeds s) t h]
  simp only [List.map_cons, List.map_nil]
  rw [backwardSeed_pm_579_broadcast s t h, backwardSeed_pm_815_broadcast s t h]
#print axioms backwardCotangent_pm_580_seeded
theorem backwardCotangent_pm_580_dx (s t : Store) (h : pmSeededDenoteWithInputs s = some t) :
    t 885 = (bw_linear (AllToAllSourceFaithful.tensor 2 0 1 2 [Tensor.mkShape (t 886).shape (fun _ => 1), Tensor.mkShape (t 1189).shape (fun _ => 1)]) (t 686) (t 678)).1 := by
  rw [backwardLinearRead_pm_581_dx (pmInitialWithSeeds s) t h, backwardCotangent_pm_580_seeded s t h]
#print axioms backwardCotangent_pm_580_dx
theorem backwardCotangent_pm_580_dw (s t : Store) (h : pmSeededDenoteWithInputs s = some t) :
    t 679 = (bw_linear (AllToAllSourceFaithful.tensor 2 0 1 2 [Tensor.mkShape (t 886).shape (fun _ => 1), Tensor.mkShape (t 1189).shape (fun _ => 1)]) (t 686) (t 678)).2 := by
  rw [backwardLinearRead_pm_581_dw (pmInitialWithSeeds s) t h, backwardCotangent_pm_580_seeded s t h]
#print axioms backwardCotangent_pm_580_dw
theorem backwardCotangent_pm_816_read (s t : Store) (h : pmDenoteWithInputs s = some t) :
    t 1188 = AllToAllSourceFaithful.tensor 2 1 1 2 ([888, 1191].map t) := by
  apply SourcePrimitiveRead.allToAll_value_of_split pmGraph pmScope pmPeers pmGraph.nodes
    pmInputRequests (pmInputRequests.take 640) (pmInputRequests.drop 641) pmNode_816
    3 [2, 3] [888, 1191] 1188 1 2 s t rfl ?_ rfl ?_ h
  · calc
      pmInputRequests = pmInputRequests.take 640 ++ pmInputRequests.drop 640 := (List.take_append_drop 640 pmInputRequests).symm
      _ = _ := rfl
  · change ∀ tid ∈ ([888, 1191] : List Tid), ∀ row ∈ pmInputRequests.drop 640, tid ∉ row.1.outs
    decide
#print axioms backwardCotangent_pm_816_read
theorem backwardCotangent_pm_816_seeded (s t : Store) (h : pmSeededDenoteWithInputs s = some t) :
    t 1188 = AllToAllSourceFaithful.tensor 2 1 1 2 [Tensor.mkShape (t 886).shape (fun _ => 1), Tensor.mkShape (t 1189).shape (fun _ => 1)] := by
  rw [backwardCotangent_pm_816_read (pmInitialWithSeeds s) t h]
  simp only [List.map_cons, List.map_nil]
  rw [backwardSeed_pm_579_broadcast s t h, backwardSeed_pm_815_broadcast s t h]
#print axioms backwardCotangent_pm_816_seeded
theorem backwardCotangent_pm_816_dx (s t : Store) (h : pmSeededDenoteWithInputs s = some t) :
    t 1187 = (bw_linear (AllToAllSourceFaithful.tensor 2 1 1 2 [Tensor.mkShape (t 886).shape (fun _ => 1), Tensor.mkShape (t 1189).shape (fun _ => 1)]) (t 989) (t 981)).1 := by
  rw [backwardLinearRead_pm_817_dx (pmInitialWithSeeds s) t h, backwardCotangent_pm_816_seeded s t h]
#print axioms backwardCotangent_pm_816_dx
theorem backwardCotangent_pm_816_dw (s t : Store) (h : pmSeededDenoteWithInputs s = some t) :
    t 982 = (bw_linear (AllToAllSourceFaithful.tensor 2 1 1 2 [Tensor.mkShape (t 886).shape (fun _ => 1), Tensor.mkShape (t 1189).shape (fun _ => 1)]) (t 989) (t 981)).2 := by
  rw [backwardLinearRead_pm_817_dw (pmInitialWithSeeds s) t h, backwardCotangent_pm_816_seeded s t h]
#print axioms backwardCotangent_pm_816_dw
end
end TrainVerify.Denote.RuntimeWorld
