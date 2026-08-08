/- Pure tensor-level V transport for canonical L22.
Graph weight facts and graph-node alignment live in separate modules. -/
import denote.yoco_goals.GatherOpGears

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
noncomputable section


/-- Ordinary rank-order transport for the L22 V operator segment. -/
theorem canonical_l22_v_ordinary_semantic
    {full shard0 shard1 rmsSM rmsPM vSM vPM : Tensor}
    (hCache : Gather2Rel full shard0 shard1 [4096, 1024] [2048, 1024])
    (hRmsW : rmsSM = rmsPM) (hVW : vSM = vPM)
    (hVShape : vPM.shape = [4, 64, 1024]) :
    Gather2Rel
      (fw_per_head_linear (fw_rms_norm full rmsSM) vSM)
      (fw_per_head_linear (fw_rms_norm shard0 rmsPM) vPM)
      (fw_per_head_linear (fw_rms_norm shard1 rmsPM) vPM)
      [4096, 4, 64] [2048, 4, 64] := by
  subst rmsPM
  subst vPM
  have hRms := hCache.rms_norm (w := rmsSM) 2048 1024 (by decide) (by decide)
  exact hRms.per_head_linear 2048 1024 4 64 hVShape
    (by decide) (by decide) (by decide) (by decide)

end
end TrainVerify.Denote.GeneratedPatterns
