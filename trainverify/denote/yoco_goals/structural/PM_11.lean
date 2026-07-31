/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_440_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_swiglu", ins := [8266, 8284], outs := [8288] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_441_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [8287], outs := [8289], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_442_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [8288], outs := [8290], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_443_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8289, 4946], outs := [8295] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_444_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8290, 4946], outs := [8296] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_445_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8295], outs := [8305], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_446_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8296], outs := [8306], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_447_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mul", ins := [8249, 8305], outs := [8309] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_448_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mul", ins := [8250, 8306], outs := [8310] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_449_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [8235, 8309], outs := [8313] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_450_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [8236, 8310], outs := [8314] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_451_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [8313], outs := [8319] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_452_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [8314], outs := [8320] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_453_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [14955, 8319], outs := [8323] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_454_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [14963, 8320], outs := [8324] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_455_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [8323], outs := [15013, 15017], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_456_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [8324], outs := [15021, 15025], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_457_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [15013, 4953], outs := [8327] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_458_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [15021, 4953], outs := [8328] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_459_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [8327], outs := [15030, 15034, 15038], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_460_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [8328], outs := [15043, 15047, 15051], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_461_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15030, 4955], outs := [8329] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_462_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15034, 4957], outs := [8341] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_463_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15038, 4959], outs := [8351] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_464_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15043, 4955], outs := [8330] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_465_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15047, 4957], outs := [8342] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_466_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15051, 4959], outs := [8352] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_467_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11858, 8361, 8329, 8341], outs := [8363, 8365], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_468_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11858, 8362, 8330, 8342], outs := [8364, 8366], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_469_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [8363, 8365, 8351, 4964, 4965], outs := [8367], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_470_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [8364, 8366, 8352, 4964, 4965], outs := [8368], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_471_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [8367], outs := [8369], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_472_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [8368], outs := [8370], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_473_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [8369], outs := [8375], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_474_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [8370], outs := [8376], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_475_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8375, 4969], outs := [8379] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_476_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8376, 4969], outs := [8380] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_477_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8379], outs := [8389], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_478_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8380], outs := [8390], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_479_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [8389], outs := [8393] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
