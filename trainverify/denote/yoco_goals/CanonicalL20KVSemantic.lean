/- Pure tensor-level K/V transport for canonical L20. -/
import denote.yoco_goals.ZigzagLayoutRel

set_option linter.style.setOption false
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
noncomputable section

private theorem cL20KV_semantic
    {full z0 z1 cu rmsSM rmsPM wSM wPM : Tensor}
    (hCache : Zigzag2Rel full z0 z1 cu [4096, 1024] [2048, 1024])
    (hRmsW : rmsSM = rmsPM) (hw : wSM = wPM)
    (hwShape : wPM.shape = [4, 64, 1024]) :
    Zigzag2Rel
      (fw_per_head_linear (fw_rms_norm full rmsSM) wSM)
      (fw_per_head_linear (fw_rms_norm z0 rmsPM) wPM)
      (fw_per_head_linear (fw_rms_norm z1 rmsPM) wPM)
      cu [4096, 4, 64] [2048, 4, 64] := by
  subst rmsPM
  subst wPM
  have hr : Zigzag2Rel (fw_rms_norm full rmsSM) (fw_rms_norm z0 rmsSM)
      (fw_rms_norm z1 rmsSM) cu [4096, 1024] [2048, 1024] :=
    Zigzag2Rel.rms_norm 2048 1024 hCache (by decide) (by decide) rfl
  exact Zigzag2Rel.per_head_linear 2048 1024 4 64 hr hwShape
    (by decide) (by decide) (by decide) (by decide)

/-- Semantic K transport, kept separate from graph alignment. -/
theorem canonical_l20_k_semantic
    {full z0 z1 cu rmsSM rmsPM kSM kPM : Tensor}
    (hCache : Zigzag2Rel full z0 z1 cu [4096, 1024] [2048, 1024])
    (hRmsW : rmsSM = rmsPM) (hKW : kSM = kPM)
    (hKShape : kPM.shape = [4, 64, 1024]) :
    Zigzag2Rel
      (fw_per_head_linear (fw_rms_norm full rmsSM) kSM)
      (fw_per_head_linear (fw_rms_norm z0 rmsPM) kPM)
      (fw_per_head_linear (fw_rms_norm z1 rmsPM) kPM)
      cu [4096, 4, 64] [2048, 4, 64] :=
  cL20KV_semantic hCache hRmsW hKW hKShape

/-- Semantic V transport, kept separate from graph alignment. -/
theorem canonical_l20_v_semantic
    {full z0 z1 cu rmsSM rmsPM vSM vPM : Tensor}
    (hCache : Zigzag2Rel full z0 z1 cu [4096, 1024] [2048, 1024])
    (hRmsW : rmsSM = rmsPM) (hVW : vSM = vPM)
    (hVShape : vPM.shape = [4, 64, 1024]) :
    Zigzag2Rel
      (fw_per_head_linear (fw_rms_norm full rmsSM) vSM)
      (fw_per_head_linear (fw_rms_norm z0 rmsPM) vPM)
      (fw_per_head_linear (fw_rms_norm z1 rmsPM) vPM)
      cu [4096, 4, 64] [2048, 4, 64] :=
  cL20KV_semantic hCache hRmsW hVW hVShape

end
end TrainVerify.Denote.GeneratedPatterns
