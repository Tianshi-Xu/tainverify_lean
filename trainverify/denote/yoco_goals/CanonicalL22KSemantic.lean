/- Pure tensor-level K transport for canonical L22.
Graph weight facts and graph-node alignment live in separate modules. -/
import denote.yoco_goals.GatherOpGears

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
noncomputable section


/-- Ordinary rank-order transport for the L22 K operator segment. -/
theorem canonical_l22_k_ordinary_semantic
    {full shard0 shard1 rmsSM rmsPM kSM kPM : Tensor}
    (hCache : Gather2Rel full shard0 shard1 [4096, 1024] [2048, 1024])
    (hRmsW : rmsSM = rmsPM) (hKW : kSM = kPM)
    (hKShape : kPM.shape = [4, 64, 1024]) :
    Gather2Rel
      (fw_per_head_linear (fw_rms_norm full rmsSM) kSM)
      (fw_per_head_linear (fw_rms_norm shard0 rmsPM) kPM)
      (fw_per_head_linear (fw_rms_norm shard1 rmsPM) kPM)
      [4096, 4, 64] [2048, 4, 64] := by
  subst rmsPM
  subst kPM
  have hRms := hCache.rms_norm (w := rmsSM) 2048 1024 (by decide) (by decide)
  exact hRms.per_head_linear 2048 1024 4 64 hKShape
    (by decide) (by decide) (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
