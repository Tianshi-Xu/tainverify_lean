/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_1560_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [10865, 5684], outs := [10867] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1561_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [10866, 5684], outs := [10868] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1562_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_attn_zigzag", ins := [10867, 5686, 5687, 5688, 5689], outs := [10891], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1563_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_attn_zigzag", ins := [10868, 5686, 5687, 5688, 5689], outs := [10892], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1564_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [10891], outs := [10893], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1565_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [10892], outs := [10894], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1566_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [10893], outs := [10899], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1567_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [10894], outs := [10900], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1568_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10899, 5693], outs := [10903] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1569_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10900, 5693], outs := [10904] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1570_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10903], outs := [10913], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1571_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10904], outs := [10914], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1572_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [10913], outs := [10917] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1573_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [10914], outs := [10918] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1574_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [16519, 10917], outs := [10921] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1575_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [16527, 10918], outs := [10922] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1576_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [10921], outs := [16531, 16535], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1577_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [10922], outs := [16539, 16543], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1578_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [16531, 5698], outs := [10925] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1579_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [16539, 5698], outs := [10926] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1580_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [10925], outs := [16550, 16554, 16558, 16562, 16566], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_1581_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [10926], outs := [16573, 16577, 16581, 16585, 16589], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_1582_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [16550], outs := [10927] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1583_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16558], outs := [10947], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1584_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16562], outs := [10961], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1585_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16566], outs := [10979], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1586_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [16573], outs := [10928] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1587_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16581], outs := [10948], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1588_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16585], outs := [10962], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1589_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16589], outs := [10980], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1590_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_norm_linear", ins := [10927, 5701], outs := [10933] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1591_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10947, 5710], outs := [10951] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1592_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10961, 5715], outs := [10965] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1593_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10979, 5719], outs := [10983] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1594_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_norm_linear", ins := [10928, 5701], outs := [10934] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1595_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10948, 5710], outs := [10952] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1596_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10962, 5715], outs := [10966] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1597_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10980, 5719], outs := [10984] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1598_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_topk_routing", ins := [10933], outs := [10935, 10937, 10939], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_1599_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10951], outs := [10957], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
