/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.ZigzagRouterRel

/-!
# Top-k gate-score gather on dim 0

The third output of `fw_topk_routing` is row local, so applying it to a dim-0
all-gather is the same as applying it independently to both token shards and
gathering the results.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote

noncomputable section

/-- The gate-score output of `fw_topk_routing` commutes with a two-rank dim-0
all-gather. -/
theorem fw_topk_routing_gate_scores_allGather0_commute_2
    (lDim numExperts topK : Nat) (hl : 0 < lDim) (he : 0 < numExperts)
    (x0 x1 : Tensor)
    (hx0 : x0.shape = [lDim, numExperts])
    (hx1 : x1.shape = [lDim, numExperts]) :
    (fw_topk_routing (allGatherPrimDimN 0 2 0 [x0, x1]) topK numExperts).2.2 =
      allGatherPrimDimN 0 2 0
        [(fw_topk_routing x0 topK numExperts).2.2,
         (fw_topk_routing x1 topK numExperts).2.2] :=
  rowLocal_allGather0_commute_2
    (fun x => (fw_topk_routing x topK numExperts).2.2)
    numExperts numExperts lDim he he hl
    (RowLocalShape_topk_thd numExperts topK)
    (RowLocalCongr_topk_thd numExperts topK he)
    x0 x1 hx0 hx1

end
end TrainVerify.Denote.GeneratedPatterns
