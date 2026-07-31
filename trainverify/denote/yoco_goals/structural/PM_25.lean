/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_1000_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [15691, 9622], outs := [9626] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1001_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [9625], outs := [14597, 13257], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1002_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [9626], outs := [14599, 13258], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1003_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [13257, 5337], outs := [9655], params := [2, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1004_wf : IsWellFormedNode pm { rank := 0, op := "OpName.AllGatherPrim", ins := [14597, 14599], outs := [11917], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1005_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [13258, 5337], outs := [9656], params := [2, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1006_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [9655], outs := [15969, 15973], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1007_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [11917, 5331], outs := [5332] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1008_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [11917, 5331], outs := [5332] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1009_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [9656], outs := [15977, 15981], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1010_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [15969, 5339], outs := [9657] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1011_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [5332], outs := [15741, 15745], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1012_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [5332], outs := [15749, 15753], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1013_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [15977, 5339], outs := [9658] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1014_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [9657, 5341], outs := [9659] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1015_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15741, 5333], outs := [5334] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1016_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15745, 5335], outs := [5336] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1017_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15749, 5333], outs := [5334] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1018_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15753, 5335], outs := [5336] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1019_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [9658, 5341], outs := [9660] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1020_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811], params := [12] } := by
  intro s
  change 12 ≥ 12
  omega

theorem pm_node_1021_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] } := by
  intro s
  change 12 ≥ 12
  omega

theorem pm_node_1022_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917], params := [12] } := by
  intro s
  change 12 ≥ 12
  omega

theorem pm_node_1023_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] } := by
  intro s
  change 12 ≥ 12
  omega

theorem pm_node_1024_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_to", ins := [15767], outs := [5343] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1025_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_to", ins := [15771], outs := [5392] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1026_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_to", ins := [15775], outs := [5441] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1027_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_to", ins := [15779], outs := [5490] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1028_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_to", ins := [15783], outs := [5539] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1029_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_to", ins := [15787], outs := [5588] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1030_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_to", ins := [15791], outs := [5637] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1031_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_to", ins := [15795], outs := [5686] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1032_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_to", ins := [15799], outs := [5735] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1033_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_to", ins := [15803], outs := [5784] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1034_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_to", ins := [15807], outs := [5833] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1035_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_to", ins := [15811], outs := [5882] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1036_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_to", ins := [15815], outs := [5343] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1037_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_to", ins := [15819], outs := [5392] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1038_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_to", ins := [15823], outs := [5441] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1039_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_to", ins := [15827], outs := [5490] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
