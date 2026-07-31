/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem sm_node_480_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5340, 5341], outs := [5342] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_481_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_to", ins := [8033], outs := [5343] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_482_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_to", ins := [8037], outs := [5392] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_483_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_to", ins := [8041], outs := [5441] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_484_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_to", ins := [8045], outs := [5490] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_485_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_to", ins := [8049], outs := [5539] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_486_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_to", ins := [8053], outs := [5588] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_487_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_to", ins := [8057], outs := [5637] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_488_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_to", ins := [8061], outs := [5686] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_489_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_to", ins := [8065], outs := [5735] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_490_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_to", ins := [8069], outs := [5784] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_491_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_to", ins := [8073], outs := [5833] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_492_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_to", ins := [8077], outs := [5882] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_493_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_to", ins := [8091], outs := [5344] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_494_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_to", ins := [8095], outs := [5393] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_495_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_to", ins := [8099], outs := [5442] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_496_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_to", ins := [8103], outs := [5491] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_497_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_to", ins := [8107], outs := [5540] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_498_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_to", ins := [8111], outs := [5589] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_499_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_to", ins := [8115], outs := [5638] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_500_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_to", ins := [8119], outs := [5687] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_501_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_to", ins := [8123], outs := [5736] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_502_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_to", ins := [8127], outs := [5785] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_503_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_to", ins := [8131], outs := [5834] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_504_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_to", ins := [8135], outs := [5883] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_505_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_attn_zigzag", ins := ((List.range 5).map (fun r => 5342 + r)), outs := [5347], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_506_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5347], outs := [5348], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_507_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5348], outs := [5349], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_508_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5349, 5350], outs := [5351] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_509_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5351], outs := [5352], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_510_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5352], outs := [5353] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_511_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [8143, 5353], outs := [5354] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_512_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5354], outs := [8147, 8151], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_513_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8147, 5355], outs := [5356] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_514_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5356], outs := [8158, 8162, 8166, 8170, 8174], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem sm_node_515_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [8158], outs := [5357] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_516_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8166], outs := [5366], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_517_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8170], outs := [5371], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_518_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8174], outs := [5375], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_519_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_norm_linear", ins := [5357, 5358], outs := [5359] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
