import denote.KRankAddGather

open TrainVerify.Denote

namespace TrainVerify.Denote

#check @fw_add_allGather_dim_K
#print axioms fw_add_allGather_dim_K

/-- Kernel-checked specialization covering exactly the backend's legal 3-D dimensions
`0`, `1`, and `2`, while deriving every gather rank count from its shard list. -/
theorem fw_add_allGather_3d_K_witness
    (gatherDim B S D : Nat) (xs ys : List Tensor)
    (hxs_ne : xs ≠ []) (hxy_len : xs.length = ys.length)
    (hdim : gatherDim < 3)
    (hxs_shape : ∀ r (hr : r < xs.length), (xs.get ⟨r, hr⟩).shape = [B, S, D])
    (hys_shape : ∀ r (hr : r < ys.length), (ys.get ⟨r, hr⟩).shape = [B, S, D]) :
    elemwiseAdd
        (allGatherPrimDimN gatherDim xs.length 0 xs)
        (allGatherPrimDimN gatherDim ys.length 0 ys) =
      allGatherPrimDimN gatherDim (List.zipWith elemwiseAdd xs ys).length 0
        (List.zipWith elemwiseAdd xs ys) := by
  apply fw_add_allGather_dim_K gatherDim [B, S, D] xs ys hxs_ne hxy_len
  · simpa using hdim
  · exact hxs_shape
  · exact hys_shape

#print axioms fw_add_allGather_3d_K_witness

end TrainVerify.Denote
