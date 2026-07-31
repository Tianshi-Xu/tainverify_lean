/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_520_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [8474], outs := [8476], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_521_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8475, 5000], outs := [8481] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_522_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8476, 5000], outs := [8482] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_523_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8481], outs := [8491], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_524_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8482], outs := [8492], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_525_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mul", ins := [8435, 8491], outs := [8495] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_526_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mul", ins := [8436, 8492], outs := [8496] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_527_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [8421, 8495], outs := [8499] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_528_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [8422, 8496], outs := [8500] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_529_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [8499], outs := [8505] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_530_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [8500], outs := [8506] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_531_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [15059, 8505], outs := [8509] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_532_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [15067, 8506], outs := [8510] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_533_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [8509], outs := [15117, 15121], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_534_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [8510], outs := [15125, 15129], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_535_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [15117, 5007], outs := [8513] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_536_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [15125, 5007], outs := [8514] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_537_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [8513], outs := [15134, 15138, 15142], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_538_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [8514], outs := [15147, 15151, 15155], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_539_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15134, 5009], outs := [8515] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_540_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15138, 5011], outs := [8527] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_541_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15142, 5013], outs := [8537] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_542_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15147, 5009], outs := [8516] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_543_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15151, 5011], outs := [8528] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_544_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15155, 5013], outs := [8538] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_545_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11859, 8547, 8515, 8527], outs := [8549, 8551], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_546_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11859, 8548, 8516, 8528], outs := [8550, 8552], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_547_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [8549, 8551, 8537, 5018, 5019], outs := [8553], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_548_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [8550, 8552, 8538, 5018, 5019], outs := [8554], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_549_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [8553], outs := [8555], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_550_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [8554], outs := [8556], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_551_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [8555], outs := [8561], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_552_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [8556], outs := [8562], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_553_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8561, 5023], outs := [8565] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_554_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8562, 5023], outs := [8566] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_555_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8565], outs := [8575], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_556_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8566], outs := [8576], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_557_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [8575], outs := [8579] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_558_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [8576], outs := [8580] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_559_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [15121, 8579], outs := [8583] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
