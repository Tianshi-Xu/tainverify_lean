/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_400_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8194], outs := [8204], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_401_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [8203], outs := [8207] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_402_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [8204], outs := [8208] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_403_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [14913, 8207], outs := [8211] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_404_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [14921, 8208], outs := [8212] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_405_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [8211], outs := [14951, 14955], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_406_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [8212], outs := [14959, 14963], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_407_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [14951, 4920], outs := [8215] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_408_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [14959, 4920], outs := [8216] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_409_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [8215], outs := [14970, 14974, 14978, 14982, 14986], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_410_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [8216], outs := [14993, 14997, 15001, 15005, 15009], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_411_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [14970], outs := [8217] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_412_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [14978], outs := [8237], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_413_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [14982], outs := [8251], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_414_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [14986], outs := [8269], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_415_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [14993], outs := [8218] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_416_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [15001], outs := [8238], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_417_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [15005], outs := [8252], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_418_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [15009], outs := [8270], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_419_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_norm_linear", ins := [8217, 4923], outs := [8223] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_420_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8237, 4932], outs := [8241] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_421_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8251, 4937], outs := [8255] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_422_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8269, 4941], outs := [8273] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_423_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_norm_linear", ins := [8218, 4923], outs := [8224] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_424_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8238, 4932], outs := [8242] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_425_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8252, 4937], outs := [8256] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_426_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8270, 4941], outs := [8274] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_427_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_topk_routing", ins := [8223], outs := [8225, 8227, 8229], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_428_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8241], outs := [8247], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_429_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8255], outs := [8265], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_430_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8273], outs := [8283], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_431_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_topk_routing", ins := [8224], outs := [8226, 8228, 8230], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_432_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8242], outs := [8248], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_433_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8256], outs := [8266], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_434_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8274], outs := [8284], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_435_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [14974, 8225, 8227, 8231, 8233], outs := [8235], params := [64, 0, 32, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_436_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_sigmoid", ins := [8247], outs := [8249] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_437_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_swiglu", ins := [8265, 8283], outs := [8287] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_438_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [14997, 8226, 8228, 8232, 8234], outs := [8236], params := [64, 32, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_439_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_sigmoid", ins := [8248], outs := [8250] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
