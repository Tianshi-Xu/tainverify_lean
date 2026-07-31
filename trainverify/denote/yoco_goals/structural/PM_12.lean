/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_480_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [8390], outs := [8394] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_481_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [15017, 8393], outs := [8397] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_482_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [15025, 8394], outs := [8398] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_483_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [8397], outs := [15055, 15059], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_484_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [8398], outs := [15063, 15067], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_485_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [15055, 4974], outs := [8401] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_486_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [15063, 4974], outs := [8402] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_487_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [8401], outs := [15074, 15078, 15082, 15086, 15090], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_488_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [8402], outs := [15097, 15101, 15105, 15109, 15113], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_489_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [15074], outs := [8403] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_490_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [15082], outs := [8423], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_491_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [15086], outs := [8437], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_492_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [15090], outs := [8455], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_493_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [15097], outs := [8404] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_494_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [15105], outs := [8424], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_495_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [15109], outs := [8438], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_496_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [15113], outs := [8456], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_497_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_norm_linear", ins := [8403, 4977], outs := [8409] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_498_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8423, 4986], outs := [8427] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_499_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8437, 4991], outs := [8441] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_500_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8455, 4995], outs := [8459] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_501_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_norm_linear", ins := [8404, 4977], outs := [8410] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_502_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8424, 4986], outs := [8428] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_503_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8438, 4991], outs := [8442] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_504_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8456, 4995], outs := [8460] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_505_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_topk_routing", ins := [8409], outs := [8411, 8413, 8415], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_506_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8427], outs := [8433], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_507_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8441], outs := [8451], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_508_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8459], outs := [8469], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_509_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_topk_routing", ins := [8410], outs := [8412, 8414, 8416], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_510_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8428], outs := [8434], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_511_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8442], outs := [8452], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_512_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8460], outs := [8470], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_513_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [15078, 8411, 8413, 8417, 8419], outs := [8421], params := [64, 0, 32, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_514_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_sigmoid", ins := [8433], outs := [8435] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_515_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_swiglu", ins := [8451, 8469], outs := [8473] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_516_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [15101, 8412, 8414, 8418, 8420], outs := [8422], params := [64, 32, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_517_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_sigmoid", ins := [8434], outs := [8436] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_518_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_swiglu", ins := [8452, 8470], outs := [8474] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_519_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [8473], outs := [8475], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
