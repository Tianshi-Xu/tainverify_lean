/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_920_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [9430], outs := [9436] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_921_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [15579, 9435], outs := [9439] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_922_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [15587, 9436], outs := [9440] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_923_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [9439], outs := [15637, 15641], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_924_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [9440], outs := [15645, 15649], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_925_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [15637, 5277], outs := [9443] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_926_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [15645, 5277], outs := [9444] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_927_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [9443], outs := [15654, 15658, 15662], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_928_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [9444], outs := [15667, 15671, 15675], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_929_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15654, 5279], outs := [9445] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_930_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15658, 5281], outs := [9457] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_931_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15662, 5283], outs := [9467] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_932_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15667, 5279], outs := [9446] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_933_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15671, 5281], outs := [9458] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_934_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15675, 5283], outs := [9468] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_935_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11864, 9477, 9445, 9457], outs := [9479, 9481], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_936_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11864, 9478, 9446, 9458], outs := [9480, 9482], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_937_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [9479, 9481, 9467, 5288, 5289], outs := [9483], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_938_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [9480, 9482, 9468, 5288, 5289], outs := [9484], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_939_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [9483], outs := [9485], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_940_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [9484], outs := [9486], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_941_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [9485], outs := [9491], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_942_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [9486], outs := [9492], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_943_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9491, 5293], outs := [9495] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_944_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9492, 5293], outs := [9496] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_945_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9495], outs := [9505], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_946_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9496], outs := [9506], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_947_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [9505], outs := [9509] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_948_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [9506], outs := [9510] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_949_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [15641, 9509], outs := [9513] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_950_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [15649, 9510], outs := [9514] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_951_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [9513], outs := [15679, 15683], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_952_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [9514], outs := [15687, 15691], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_953_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [15679, 5298], outs := [9517] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_954_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [15687, 5298], outs := [9518] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_955_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [9517], outs := [15698, 15702, 15706, 15710, 15714], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_956_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [9518], outs := [15721, 15725, 15729, 15733, 15737], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_957_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [15698], outs := [9519] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_958_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [15706], outs := [9539], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_959_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [15710], outs := [9553], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
