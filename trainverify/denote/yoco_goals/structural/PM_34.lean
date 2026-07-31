/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_1360_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10387], outs := [10397], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1361_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10388], outs := [10398], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1362_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [10397], outs := [10401] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1363_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [10398], outs := [10402] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1364_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [16285, 10401], outs := [10405] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1365_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [16293, 10402], outs := [10406] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1366_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [10405], outs := [16297, 16301], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1367_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [10406], outs := [16305, 16309], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1368_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [16297, 5551], outs := [10409] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1369_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [16305, 5551], outs := [10410] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1370_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [10409], outs := [16316, 16320, 16324, 16328, 16332], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_1371_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [10410], outs := [16339, 16343, 16347, 16351, 16355], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_1372_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [16316], outs := [10411] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1373_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16324], outs := [10431], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1374_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16328], outs := [10445], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1375_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16332], outs := [10463], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1376_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [16339], outs := [10412] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1377_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16347], outs := [10432], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1378_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16351], outs := [10446], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1379_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16355], outs := [10464], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1380_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_norm_linear", ins := [10411, 5554], outs := [10417] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1381_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10431, 5563], outs := [10435] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1382_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10445, 5568], outs := [10449] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1383_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10463, 5572], outs := [10467] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1384_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_norm_linear", ins := [10412, 5554], outs := [10418] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1385_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10432, 5563], outs := [10436] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1386_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10446, 5568], outs := [10450] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1387_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10464, 5572], outs := [10468] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1388_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_topk_routing", ins := [10417], outs := [10419, 10421, 10423], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_1389_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10435], outs := [10441], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1390_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10449], outs := [10459], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1391_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10467], outs := [10477], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1392_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_topk_routing", ins := [10418], outs := [10420, 10422, 10424], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_1393_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10436], outs := [10442], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1394_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10450], outs := [10460], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1395_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10468], outs := [10478], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1396_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16320, 10419, 10421, 10425, 10427], outs := [10429], params := [64, 0, 32, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1397_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_sigmoid", ins := [10441], outs := [10443] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1398_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_swiglu", ins := [10459, 10477], outs := [10481] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1399_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16343, 10420, 10422, 10426, 10428], outs := [10430], params := [64, 32, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
