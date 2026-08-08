/- Pure tensor-level K transport for canonical L22.
Graph weight facts and graph-node alignment live in separate modules. -/
import denote.yoco_goals.ZigzagLayoutRel
import denote.yoco_goals.GatherOpGears

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote
open TrainVerify.Denote.ZigzagCollective
noncomputable section

private theorem rms_norm_two_weights
    {full z0 z1 cu wSM wPM : Tensor} {fullShape shardShape : Shape}
    (lDim h : Nat) (hw : wSM = wPM)
    (hrel : Zigzag2Rel full z0 z1 cu fullShape shardShape)
    (hl : 0 < lDim) (hh : 0 < h) (hshard : shardShape = [lDim, h]) :
    Zigzag2Rel (fw_rms_norm full wSM) (fw_rms_norm z0 wPM)
      (fw_rms_norm z1 wPM) cu fullShape shardShape := by
  subst wPM
  exact Zigzag2Rel.rms_norm lDim h hrel hl hh hshard

private theorem per_head_two_weights
    {full z0 z1 cu wSM wPM : Tensor} (lDim k hW dW : Nat)
    (hwEq : wSM = wPM)
    (hrel : Zigzag2Rel full z0 z1 cu [lDim * 2, k] [lDim, k])
    (hwShape : wPM.shape = [hW, dW, k])
    (hl : 0 < lDim) (hk : 0 < k) (hhW : 0 < hW) (hdW : 0 < dW) :
    Zigzag2Rel (fw_per_head_linear full wSM) (fw_per_head_linear z0 wPM)
      (fw_per_head_linear z1 wPM) cu [lDim * 2, hW, dW] [lDim, hW, dW] := by
  subst wPM
  exact Zigzag2Rel.per_head_linear lDim k hW dW hrel hwShape hl hk hhW hdW

/-- Pure semantic transport; all premises are internal facts supplied by the graph
composition layer, not a public caller contract. -/
theorem canonical_l22_k_semantic
    {full z0 z1 cu rmsSM rmsPM kSM kPM : Tensor}
    (hCache : Zigzag2Rel full z0 z1 cu [4096, 1024] [2048, 1024])
    (hRmsW : rmsSM = rmsPM) (hKW : kSM = kPM)
    (hKShape : kPM.shape = [4, 64, 1024]) :
    Zigzag2Rel
      (fw_per_head_linear (fw_rms_norm full rmsSM) kSM)
      (fw_per_head_linear (fw_rms_norm z0 rmsPM) kPM)
      (fw_per_head_linear (fw_rms_norm z1 rmsPM) kPM)
      cu [4096, 4, 64] [2048, 4, 64] := by
  have hRms := rms_norm_two_weights 2048 1024 hRmsW hCache
    (by decide) (by decide) rfl
  exact per_head_two_weights 2048 1024 4 64 hKW hRms hKShape
    (by decide) (by decide) (by decide) (by decide)

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
