/- Pure tensor-level ordinary K/V transport for canonical L16. -/
import denote.yoco_goals.GatherOpGears

set_option linter.style.setOption false
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
noncomputable section

private theorem cL16KV_ordinary_semantic
    {full shard0 shard1 rmsSM rmsPM wSM wPM : Tensor}
    (hCache : Gather2Rel full shard0 shard1 [4096, 1024] [2048, 1024])
    (hRmsW : rmsSM = rmsPM) (hw : wSM = wPM)
    (hwShape : wPM.shape = [4, 64, 1024]) :
    Gather2Rel
      (fw_per_head_linear (fw_rms_norm full rmsSM) wSM)
      (fw_per_head_linear (fw_rms_norm shard0 rmsPM) wPM)
      (fw_per_head_linear (fw_rms_norm shard1 rmsPM) wPM)
      [4096, 4, 64] [2048, 4, 64] := by
  subst rmsPM
  subst wPM
  have hr := hCache.rms_norm (w := rmsSM) 2048 1024 (by decide) (by decide)
  exact hr.per_head_linear 2048 1024 4 64 hwShape
    (by decide) (by decide) (by decide) (by decide)

/-- Ordinary rank-order K transport, kept separate from graph alignment. -/
theorem canonical_l16_k_ordinary_semantic
    {full shard0 shard1 rmsSM rmsPM kSM kPM : Tensor}
    (hCache : Gather2Rel full shard0 shard1 [4096, 1024] [2048, 1024])
    (hRmsW : rmsSM = rmsPM) (hKW : kSM = kPM)
    (hKShape : kPM.shape = [4, 64, 1024]) :
    Gather2Rel
      (fw_per_head_linear (fw_rms_norm full rmsSM) kSM)
      (fw_per_head_linear (fw_rms_norm shard0 rmsPM) kPM)
      (fw_per_head_linear (fw_rms_norm shard1 rmsPM) kPM)
      [4096, 4, 64] [2048, 4, 64] :=
  cL16KV_ordinary_semantic hCache hRmsW hKW hKShape

/-- Ordinary rank-order V transport, kept separate from graph alignment. -/
theorem canonical_l16_v_ordinary_semantic
    {full shard0 shard1 rmsSM rmsPM vSM vPM : Tensor}
    (hCache : Gather2Rel full shard0 shard1 [4096, 1024] [2048, 1024])
    (hRmsW : rmsSM = rmsPM) (hVW : vSM = vPM)
    (hVShape : vPM.shape = [4, 64, 1024]) :
    Gather2Rel
      (fw_per_head_linear (fw_rms_norm full rmsSM) vSM)
      (fw_per_head_linear (fw_rms_norm shard0 rmsPM) vPM)
      (fw_per_head_linear (fw_rms_norm shard1 rmsPM) vPM)
      [4096, 4, 64] [2048, 4, 64] :=
  cL16KV_ordinary_semantic hCache hRmsW hVW hVShape

end
end TrainVerify.Denote.GeneratedPatterns
