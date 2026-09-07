import denote.gpt_ly4_regen.GeneratedData
import denote.KRankBWLinearDwSequenceGeneral
import denote.KRankBWLinearDxSequence
import denote.KRankBWMatmulHead
/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.SequenceDwMixedsegment_000264

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_000044 : RelationFact :=
  .joined 586 586 [1, 4, 8, 8]

private def fact_000064 : RelationFact :=
  .joined 590 590 [1, 8, 32]

private def fact_000066 : RelationFact :=
  .joined 596 596 [1, 8, 32]

private def fact_000076 : RelationFact :=
  .joined 631 631 [1, 8, 32]

private def fact_000077 : RelationFact :=
  .joined 634 634 [1, 8, 128]

private def fact_000078 : RelationFact :=
  .joined 926 917 [1, 8, 32]

private def fact_000079 : RelationFact :=
  .joined 1004 999 [1, 8, 32]

private def fact_000080 : RelationFact :=
  .joined 1008 1000 [1, 8, 32]

private def fact_000128 : RelationFact :=
  .sharded 563 [1065, 1066, 1067, 1068] 0 [128, 32] [32, 32]

private def fact_000129 : RelationFact :=
  .sharded 568 [568] 0 [32] [32]

private def fact_000130 : RelationFact :=
  .sharded 569 [569] 0 [32] [32]

private def fact_000131 : RelationFact :=
  .sharded 571 [571] 0 [32, 32] [32, 32]

private def fact_000132 : RelationFact :=
  .sharded 573 [573] 0 [32, 32] [32, 32]

private def fact_000133 : RelationFact :=
  .sharded 575 [1229, 1230, 1231, 1232] 0 [32, 32] [8, 32]

private def fact_000134 : RelationFact :=
  .sharded 591 [1473, 1474, 1475, 1476] 0 [32, 32] [8, 32]

private def fact_000135 : RelationFact :=
  .sharded 594 [594] 0 [32] [32]

private def fact_000136 : RelationFact :=
  .sharded 595 [595] 0 [32] [32]

private def fact_000137 : RelationFact :=
  .sharded 597 [1557, 1558, 1559, 1560] 0 [128, 32] [32, 32]

private def fact_000138 : RelationFact :=
  .sharded 600 [600] 0 [32, 128] [32, 128]

private def fact_000139 : RelationFact :=
  .sharded 603 [603] 0 [32] [32]

private def fact_000140 : RelationFact :=
  .sharded 604 [604] 0 [32] [32]

private def fact_000141 : RelationFact :=
  .sharded 606 [1697, 1698, 1699, 1700] 1 [32, 32] [32, 8]

private def fact_000142 : RelationFact :=
  .sharded 608 [608] 0 [32, 32] [32, 32]

private def fact_000143 : RelationFact :=
  .sharded 610 [1753, 1754, 1755, 1756] 1 [32, 32] [32, 8]

private def fact_000144 : RelationFact :=
  .sharded 626 [626] 0 [32, 32] [32, 32]

private def fact_000145 : RelationFact :=
  .sharded 629 [629] 0 [32] [32]

private def fact_000146 : RelationFact :=
  .sharded 630 [630] 0 [32] [32]

private def fact_000147 : RelationFact :=
  .sharded 632 [2113, 2114, 2115, 2116] 0 [128, 32] [32, 32]

private def fact_000148 : RelationFact :=
  .sharded 635 [2165, 2166, 2167, 2168] 0 [32, 128] [8, 128]

private def fact_000149 : RelationFact :=
  .sharded 638 [638] 0 [32] [32]

private def fact_000150 : RelationFact :=
  .sharded 639 [639] 0 [32] [32]

private def fact_000151 : RelationFact :=
  .sharded 641 [2257, 2258, 2259, 2260] 0 [32, 32] [8, 32]

private def fact_000152 : RelationFact :=
  .sharded 643 [2285, 2286, 2287, 2288] 0 [32, 32] [8, 32]

private def fact_000153 : RelationFact :=
  .sharded 645 [645] 0 [32, 32] [32, 32]

private def fact_000172 : RelationFact :=
  .sharded 714 [714] 0 [1, 8] [1, 8]

private def fact_000173 : RelationFact :=
  .sharded 564 [1109, 1110, 1111, 1112] 2 [1, 8, 32] [1, 8, 8]

private def fact_000216 : RelationFact :=
  .sharded 578 [1261, 1262, 1263, 1264] 3 [1, 4, 8, 8] [1, 4, 8, 2]

private def fact_000249 : RelationFact :=
  .sharded 582 [1309, 1310, 1311, 1312] 3 [1, 4, 8, 8] [1, 4, 8, 2]

private def fact_000257 : RelationFact :=
  .sharded 994 [2625, 2628, 2631, 2634] 1 [1, 8, 32] [1, 2, 32]

private def fact_000265 : RelationFact :=
  .sharded 583 [1333, 1334, 1335, 1336] 2 [1, 4, 8, 8] [1, 4, 2, 8]

private def fact_000273 : RelationFact :=
  .sharded 820 [2331, 2334, 2337, 2340] 1 [1, 8, 32] [1, 2, 32]

private def fact_000275 : RelationFact :=
  .sharded 822 [2358, 2360, 2362, 2364] 1 [1, 4, 8, 8] [1, 1, 8, 8]

private def fact_000276 : RelationFact :=
  .sharded 827 [2430, 2432, 2434, 2436] 1 [1, 4, 8, 8] [1, 1, 8, 8]

private def fact_000277 : RelationFact :=
  .sharded 1013 [2329, 2332, 2335, 2338] 1 [1, 8, 32] [1, 2, 32]

private def fact_000278 : RelationFact :=
  .sharded 824 [2429, 2431, 2433, 2435] 1 [1, 4, 8, 8] [1, 1, 8, 8]

private def fact_000280 : RelationFact :=
  .sharded 821 [2357, 2359, 2361, 2363] 2 [1, 8, 4, 8] [1, 8, 1, 8]

private def fact_000298 : RelationFact :=
  .sharded 585 [1389, 1390, 1391, 1392] 2 [1, 4, 8, 8] [1, 4, 2, 8]

private def fact_000384 : RelationFact :=
  .sharded 592 [1477, 1478, 1479, 1480] 2 [1, 8, 32] [1, 8, 8]

private def fact_000387 : RelationFact :=
  .sharded 934 [1525, 1526, 1527, 1528] 1 [1, 8, 32] [1, 2, 32]

private def fact_000388 : RelationFact :=
  .sharded 938 [1629, 1630, 1631, 1632] 2 [1, 8, 32] [1, 8, 8]

private def fact_000390 : RelationFact :=
  .sharded 598 [1561, 1562, 1563, 1564] 2 [1, 8, 128] [1, 8, 32]

private def fact_000392 : RelationFact :=
  .sharded 599 [1601, 1602, 1603, 1604] 1 [1, 8, 128] [1, 2, 128]

private def fact_000394 : RelationFact :=
  .sharded 601 [1633, 1634, 1635, 1636] 2 [1, 8, 32] [1, 8, 8]

private def fact_000398 : RelationFact :=
  .sharded 946 [1661, 1662, 1663, 1664] 1 [1, 8, 32] [1, 2, 32]

private def fact_000399 : RelationFact :=
  .sharded 950 [2049, 2050, 2051, 2052] 2 [1, 8, 32] [1, 8, 8]

private def fact_000402 : RelationFact :=
  .sharded 961 [1693, 1694, 1695, 1696] 2 [1, 8, 32] [1, 8, 8]

private def fact_000403 : RelationFact :=
  .sharded 965 [1721, 1722, 1723, 1724] 1 [1, 8, 32] [1, 2, 32]

private def fact_000405 : RelationFact :=
  .sharded 969 [1749, 1750, 1751, 1752] 2 [1, 8, 32] [1, 8, 8]

private def fact_000411 : RelationFact :=
  .sharded 903 [1141, 1142, 1143, 1144] 1 [1, 8, 32] [1, 2, 32]

private def fact_000412 : RelationFact :=
  .sharded 907 [1501, 1502, 1503, 1504] 2 [1, 8, 32] [1, 8, 8]

private def fact_000414 : RelationFact :=
  .sharded 613 [1873, 1874, 1875, 1876] 1 [1, 4, 8, 8] [1, 1, 8, 8]

private def fact_000418 : RelationFact :=
  .sharded 617 [1949, 1950, 1951, 1952] 2 [1, 4, 8, 8] [1, 4, 2, 8]

private def fact_000420 : RelationFact :=
  .sharded 618 [1877, 1878, 1879, 1880] 1 [1, 4, 8, 8] [1, 1, 8, 8]

private def fact_000423 : RelationFact :=
  .sharded 620 [1909, 1910, 1911, 1912] 2 [1, 4, 8, 8] [1, 4, 2, 8]

private def fact_000425 : RelationFact :=
  .sharded 621 [1945, 1946, 1947, 1948] 3 [1, 4, 8, 8] [1, 4, 8, 2]

private def fact_000431 : RelationFact :=
  .sharded 625 [2021, 2022, 2023, 2024] 1 [1, 8, 32] [1, 2, 32]

private def fact_000433 : RelationFact :=
  .sharded 627 [2053, 2054, 2055, 2056] 2 [1, 8, 32] [1, 8, 8]

private def fact_000436 : RelationFact :=
  .sharded 977 [2081, 2082, 2083, 2084] 1 [1, 8, 32] [1, 2, 32]

private def fact_000438 : RelationFact :=
  .sharded 981 [2193, 2194, 2195, 2196] 1 [1, 8, 32] [1, 2, 32]

private def fact_000441 : RelationFact :=
  .sharded 633 [2141, 2142, 2143, 2144] 1 [1, 8, 128] [1, 2, 128]

private def fact_000444 : RelationFact :=
  .sharded 636 [2197, 2198, 2199, 2200] 1 [1, 8, 32] [1, 2, 32]

private def fact_000446 : RelationFact :=
  .sharded 989 [2225, 2226, 2227, 2228] 1 [1, 8, 32] [1, 2, 32]

private def fact_000448 : RelationFact :=
  .sharded 918 [1173, 1174, 1175, 1176] 1 [1, 8, 32] [1, 2, 32]

private def fact_000449 : RelationFact :=
  .sharded 922 [1201, 1202, 1203, 1204] 1 [1, 8, 32] [1, 2, 32]

private def fact_000454 : RelationFact :=
  .sharded 1012 [2313, 2314, 2315, 2316] 1 [1, 8, 32] [1, 2, 32]

private def test_dw_fact : RelationFact :=
  .reduction 819 [2330, 2333, 2336, 2339] [32, 32]

private def authority_transition_eq_sm_565_pm_565 : RelationFact :=
  .tensorEq .sm 565 .pm 565

private def authority_transition_eq_sm_568_pm_568 : RelationFact :=
  .tensorEq .sm 568 .pm 568

private def authority_transition_eq_sm_569_pm_569 : RelationFact :=
  .tensorEq .sm 569 .pm 569

private def authority_transition_eq_sm_571_pm_571 : RelationFact :=
  .tensorEq .sm 571 .pm 571

private def authority_transition_eq_sm_573_pm_573 : RelationFact :=
  .tensorEq .sm 573 .pm 573

private def authority_transition_eq_sm_594_pm_594 : RelationFact :=
  .tensorEq .sm 594 .pm 594

private def authority_transition_eq_sm_595_pm_595 : RelationFact :=
  .tensorEq .sm 595 .pm 595

private def authority_transition_eq_sm_600_pm_600 : RelationFact :=
  .tensorEq .sm 600 .pm 600

private def authority_transition_eq_sm_603_pm_603 : RelationFact :=
  .tensorEq .sm 603 .pm 603

private def authority_transition_eq_sm_604_pm_604 : RelationFact :=
  .tensorEq .sm 604 .pm 604

private def authority_transition_eq_sm_608_pm_608 : RelationFact :=
  .tensorEq .sm 608 .pm 608

private def authority_transition_eq_sm_626_pm_626 : RelationFact :=
  .tensorEq .sm 626 .pm 626

private def authority_transition_eq_sm_629_pm_629 : RelationFact :=
  .tensorEq .sm 629 .pm 629

private def authority_transition_eq_sm_630_pm_630 : RelationFact :=
  .tensorEq .sm 630 .pm 630

private def authority_transition_eq_sm_638_pm_638 : RelationFact :=
  .tensorEq .sm 638 .pm 638

private def authority_transition_eq_sm_639_pm_639 : RelationFact :=
  .tensorEq .sm 639 .pm 639

private def authority_transition_eq_sm_645_pm_645 : RelationFact :=
  .tensorEq .sm 645 .pm 645

private def authority_transition_eq_sm_714_pm_714 : RelationFact :=
  .tensorEq .sm 714 .pm 714

private def authority_transition_eq_sm_716_pm_716 : RelationFact :=
  .tensorEq .sm 716 .pm 716

private def authority_transition_shape_pm_565 : RelationFact :=
  .tensorShape .pm 565 [8, 32]

private def authority_transition_shape_pm_568 : RelationFact :=
  .tensorShape .pm 568 [32]

private def authority_transition_shape_pm_569 : RelationFact :=
  .tensorShape .pm 569 [32]

private def authority_transition_shape_pm_571 : RelationFact :=
  .tensorShape .pm 571 [32, 32]

private def authority_transition_shape_pm_573 : RelationFact :=
  .tensorShape .pm 573 [32, 32]

private def authority_transition_shape_pm_594 : RelationFact :=
  .tensorShape .pm 594 [32]

private def authority_transition_shape_pm_595 : RelationFact :=
  .tensorShape .pm 595 [32]

private def authority_transition_shape_pm_600 : RelationFact :=
  .tensorShape .pm 600 [32, 128]

private def authority_transition_shape_pm_603 : RelationFact :=
  .tensorShape .pm 603 [32]

private def authority_transition_shape_pm_604 : RelationFact :=
  .tensorShape .pm 604 [32]

private def authority_transition_shape_pm_608 : RelationFact :=
  .tensorShape .pm 608 [32, 32]

private def authority_transition_shape_pm_626 : RelationFact :=
  .tensorShape .pm 626 [32, 32]

private def authority_transition_shape_pm_629 : RelationFact :=
  .tensorShape .pm 629 [32]

private def authority_transition_shape_pm_630 : RelationFact :=
  .tensorShape .pm 630 [32]

private def authority_transition_shape_pm_638 : RelationFact :=
  .tensorShape .pm 638 [32]

private def authority_transition_shape_pm_639 : RelationFact :=
  .tensorShape .pm 639 [32]

private def authority_transition_shape_pm_645 : RelationFact :=
  .tensorShape .pm 645 [32, 32]

private def authority_transition_shape_pm_714 : RelationFact :=
  .tensorShape .pm 714 [1, 8]

private def anchor_sm_shape_563 : RelationFact :=
  .tensorShape .sm 563 [128, 32]

private def state_000264 : RelationState where
  facts := [anchor_sm_shape_563, authority_transition_eq_sm_565_pm_565, authority_transition_eq_sm_568_pm_568, authority_transition_eq_sm_569_pm_569, authority_transition_eq_sm_571_pm_571, authority_transition_eq_sm_573_pm_573, authority_transition_eq_sm_594_pm_594, authority_transition_eq_sm_595_pm_595, authority_transition_eq_sm_600_pm_600, authority_transition_eq_sm_603_pm_603, authority_transition_eq_sm_604_pm_604, authority_transition_eq_sm_608_pm_608, authority_transition_eq_sm_626_pm_626, authority_transition_eq_sm_629_pm_629, authority_transition_eq_sm_630_pm_630, authority_transition_eq_sm_638_pm_638, authority_transition_eq_sm_639_pm_639, authority_transition_eq_sm_645_pm_645, authority_transition_eq_sm_714_pm_714, authority_transition_eq_sm_716_pm_716, authority_transition_shape_pm_565, authority_transition_shape_pm_568, authority_transition_shape_pm_569, authority_transition_shape_pm_571, authority_transition_shape_pm_573, authority_transition_shape_pm_594, authority_transition_shape_pm_595, authority_transition_shape_pm_600, authority_transition_shape_pm_603, authority_transition_shape_pm_604, authority_transition_shape_pm_608, authority_transition_shape_pm_626, authority_transition_shape_pm_629, authority_transition_shape_pm_630, authority_transition_shape_pm_638, authority_transition_shape_pm_639, authority_transition_shape_pm_645, authority_transition_shape_pm_714, fact_000044, fact_000064, fact_000066, fact_000076, fact_000077, fact_000078, fact_000079, fact_000080, fact_000128, fact_000129, fact_000130, fact_000131, fact_000132, fact_000133, fact_000134, fact_000135, fact_000136, fact_000137, fact_000138, fact_000139, fact_000140, fact_000141, fact_000142, fact_000143, fact_000144, fact_000145, fact_000146, fact_000147, fact_000148, fact_000149, fact_000150, fact_000151, fact_000152, fact_000153, fact_000172, fact_000173, fact_000216, fact_000249, fact_000257, fact_000265, fact_000273, fact_000275, fact_000276, fact_000298, fact_000384, fact_000387, fact_000388, fact_000390, fact_000392, fact_000394, fact_000398, fact_000399, fact_000402, fact_000403, fact_000405, fact_000411, fact_000412, fact_000414, fact_000418, fact_000420, fact_000423, fact_000425, fact_000431, fact_000433, fact_000436, fact_000438, fact_000441, fact_000444, fact_000446, fact_000448, fact_000449, fact_000454]
  nonempty := by decide

private def state_000265 : RelationState where
  facts := [anchor_sm_shape_563, authority_transition_eq_sm_565_pm_565, authority_transition_eq_sm_568_pm_568, authority_transition_eq_sm_569_pm_569, authority_transition_eq_sm_571_pm_571, authority_transition_eq_sm_573_pm_573, authority_transition_eq_sm_594_pm_594, authority_transition_eq_sm_595_pm_595, authority_transition_eq_sm_600_pm_600, authority_transition_eq_sm_603_pm_603, authority_transition_eq_sm_604_pm_604, authority_transition_eq_sm_608_pm_608, authority_transition_eq_sm_626_pm_626, authority_transition_eq_sm_629_pm_629, authority_transition_eq_sm_630_pm_630, authority_transition_eq_sm_638_pm_638, authority_transition_eq_sm_639_pm_639, authority_transition_eq_sm_714_pm_714, authority_transition_eq_sm_716_pm_716, authority_transition_shape_pm_565, authority_transition_shape_pm_568, authority_transition_shape_pm_569, authority_transition_shape_pm_571, authority_transition_shape_pm_573, authority_transition_shape_pm_594, authority_transition_shape_pm_595, authority_transition_shape_pm_600, authority_transition_shape_pm_603, authority_transition_shape_pm_604, authority_transition_shape_pm_608, authority_transition_shape_pm_626, authority_transition_shape_pm_629, authority_transition_shape_pm_630, authority_transition_shape_pm_638, authority_transition_shape_pm_639, authority_transition_shape_pm_714, fact_000044, fact_000064, fact_000066, fact_000076, fact_000077, fact_000078, fact_000079, fact_000080, fact_000128, fact_000129, fact_000130, fact_000131, fact_000132, fact_000133, fact_000134, fact_000135, fact_000136, fact_000137, fact_000138, fact_000139, fact_000140, fact_000141, fact_000142, fact_000143, fact_000144, fact_000145, fact_000146, fact_000147, fact_000148, fact_000149, fact_000150, fact_000151, fact_000152, fact_000172, fact_000173, fact_000216, fact_000249, fact_000257, fact_000265, fact_000277, fact_000278, fact_000280, fact_000298, fact_000384, fact_000387, fact_000388, fact_000390, fact_000392, fact_000394, fact_000398, fact_000399, fact_000402, fact_000403, fact_000405, fact_000411, fact_000412, fact_000414, fact_000418, fact_000420, fact_000423, fact_000425, fact_000431, fact_000433, fact_000436, fact_000438, fact_000441, fact_000444, fact_000446, fact_000448, fact_000449, test_dw_fact]
  nonempty := by decide

end
end TrainVerify.Denote.SequenceDwMixedsegment_000264

namespace TrainVerify.Denote.SequenceDwMixedsegment_000264
set_option maxHeartbeats 500000
noncomputable section
private def segment_000264_sm_nodes:List NodeDecl:=[{ rank := 0, op := "OpName.BW_linear", ins := [820, 1012, 645], outs := [1013, 819] }, { rank := 0, op := "OpName.BW_transpose", ins := [827, 650], outs := [824], params := [2, 3] }, { rank := 0, op := "OpName.BW_transpose", ins := [822, 647], outs := [821], params := [1, 2] }]
private def segment_000264_pm_nodes:List NodeDecl:=[{ rank := 0, op := "OpName.BW_transpose", ins := [2358, 2341], outs := [2357], params := [1, 2] }, { rank := 1, op := "OpName.BW_transpose", ins := [2360, 2342], outs := [2359], params := [1, 2] }, { rank := 2, op := "OpName.BW_transpose", ins := [2362, 2343], outs := [2361], params := [1, 2] }, { rank := 3, op := "OpName.BW_transpose", ins := [2364, 2344], outs := [2363], params := [1, 2] }, { rank := 0, op := "OpName.BW_linear", ins := [2331, 2313, 645], outs := [2329, 2330] }, { rank := 1, op := "OpName.BW_linear", ins := [2334, 2314, 645], outs := [2332, 2333] }, { rank := 2, op := "OpName.BW_linear", ins := [2337, 2315, 645], outs := [2335, 2336] }, { rank := 3, op := "OpName.BW_linear", ins := [2340, 2316, 645], outs := [2338, 2339] }, { rank := 0, op := "OpName.BW_transpose", ins := [2430, 2413], outs := [2429], params := [2, 3] }, { rank := 1, op := "OpName.BW_transpose", ins := [2432, 2414], outs := [2431], params := [2, 3] }, { rank := 2, op := "OpName.BW_transpose", ins := [2434, 2415], outs := [2433], params := [2, 3] }, { rank := 3, op := "OpName.BW_transpose", ins := [2436, 2416], outs := [2435], params := [2, 3] }]
@[irreducible] private def segment_000264_sm_final(s:Store):Store:=segment_000264_sm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) s
@[irreducible] private def segment_000264_pm_final(s:Store):Store:=segment_000264_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) s

private theorem segment_000264_hLinearSm(smStore:Store):(segment_000264_sm_final smStore) 1013=(bw_linear ((segment_000264_sm_final smStore) 820) ((segment_000264_sm_final smStore) 1012) ((segment_000264_sm_final smStore) 645)).1:=by
  have hfinal:(segment_000264_sm_final smStore)=segment_000264_sm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore:=by unfold segment_000264_sm_final;rfl
  have hout_nodes : segment_000264_sm_nodes = (segment_000264_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [820, 1012, 645], outs := [1013, 819] }] ++ (segment_000264_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000264_sm_final smStore) 1013 = (bw_linear (((segment_000264_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 820) (((segment_000264_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 1012) (((segment_000264_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 645)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.sm smStore
      (segment_000264_sm_nodes.take 0) (segment_000264_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [820, 1012, 645], outs := [1013, 819] } 1013
      (fun t => (bw_linear (t 820) (t 1012) (t 645)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out TrainVerify.Denote.Generated.sm t 0 820 1012 645 1013 819 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000264_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 820 = (segment_000264_sm_final smStore) 820 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000264_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [820, 1012, 645], outs := [1013, 819] } :: (segment_000264_sm_nodes.drop 1)) 820
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000264_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 1012 = (segment_000264_sm_final smStore) 1012 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000264_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [820, 1012, 645], outs := [1013, 819] } :: (segment_000264_sm_nodes.drop 1)) 1012
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000264_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 645 = (segment_000264_sm_final smStore) 645 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000264_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [820, 1012, 645], outs := [1013, 819] } :: (segment_000264_sm_nodes.drop 1)) 645
      (by native_decide) (by native_decide)
  have hout : (segment_000264_sm_final smStore) 1013 = (bw_linear ((segment_000264_sm_final smStore) 820) ((segment_000264_sm_final smStore) 1012) ((segment_000264_sm_final smStore) 645)).1 := by
    calc
      _ = (bw_linear (((segment_000264_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 820) (((segment_000264_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 1012) (((segment_000264_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 645)).1 := hout_prefix
      _ = (bw_linear ((segment_000264_sm_final smStore) 820) ((segment_000264_sm_final smStore) 1012) ((segment_000264_sm_final smStore) 645)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000264_hLinearPm0(pmStore:Store):(segment_000264_pm_final pmStore) 2329=(bw_linear ((segment_000264_pm_final pmStore) 2331) ((segment_000264_pm_final pmStore) 2313) ((segment_000264_pm_final pmStore) 645)).1:=by
  have hfinal:(segment_000264_pm_final pmStore)=segment_000264_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000264_pm_final;rfl
  have hout_nodes : segment_000264_pm_nodes = (segment_000264_pm_nodes.take 4) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [2331, 2313, 645], outs := [2329, 2330] }] ++ (segment_000264_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000264_pm_final pmStore) 2329 = (bw_linear (((segment_000264_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2331) (((segment_000264_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2313) (((segment_000264_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 645)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 4) (segment_000264_pm_nodes.drop 5)
      { rank := 0, op := "OpName.BW_linear", ins := [2331, 2313, 645], outs := [2329, 2330] } 2329
      (fun t => (bw_linear (t 2331) (t 2313) (t 645)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out TrainVerify.Denote.Generated.pm t 0 2331 2313 645 2329 2330 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000264_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2331 = (segment_000264_pm_final pmStore) 2331 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 4) ({ rank := 0, op := "OpName.BW_linear", ins := [2331, 2313, 645], outs := [2329, 2330] } :: (segment_000264_pm_nodes.drop 5)) 2331
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000264_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2313 = (segment_000264_pm_final pmStore) 2313 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 4) ({ rank := 0, op := "OpName.BW_linear", ins := [2331, 2313, 645], outs := [2329, 2330] } :: (segment_000264_pm_nodes.drop 5)) 2313
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000264_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 645 = (segment_000264_pm_final pmStore) 645 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 4) ({ rank := 0, op := "OpName.BW_linear", ins := [2331, 2313, 645], outs := [2329, 2330] } :: (segment_000264_pm_nodes.drop 5)) 645
      (by native_decide) (by native_decide)
  have hout : (segment_000264_pm_final pmStore) 2329 = (bw_linear ((segment_000264_pm_final pmStore) 2331) ((segment_000264_pm_final pmStore) 2313) ((segment_000264_pm_final pmStore) 645)).1 := by
    calc
      _ = (bw_linear (((segment_000264_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2331) (((segment_000264_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2313) (((segment_000264_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 645)).1 := hout_prefix
      _ = (bw_linear ((segment_000264_pm_final pmStore) 2331) ((segment_000264_pm_final pmStore) 2313) ((segment_000264_pm_final pmStore) 645)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000264_hLinearPm1(pmStore:Store):(segment_000264_pm_final pmStore) 2332=(bw_linear ((segment_000264_pm_final pmStore) 2334) ((segment_000264_pm_final pmStore) 2314) ((segment_000264_pm_final pmStore) 645)).1:=by
  have hfinal:(segment_000264_pm_final pmStore)=segment_000264_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000264_pm_final;rfl
  have hout_nodes : segment_000264_pm_nodes = (segment_000264_pm_nodes.take 5) ++ [{ rank := 1, op := "OpName.BW_linear", ins := [2334, 2314, 645], outs := [2332, 2333] }] ++ (segment_000264_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000264_pm_final pmStore) 2332 = (bw_linear (((segment_000264_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2334) (((segment_000264_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2314) (((segment_000264_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 645)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 5) (segment_000264_pm_nodes.drop 6)
      { rank := 1, op := "OpName.BW_linear", ins := [2334, 2314, 645], outs := [2332, 2333] } 2332
      (fun t => (bw_linear (t 2334) (t 2314) (t 645)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out TrainVerify.Denote.Generated.pm t 1 2334 2314 645 2332 2333 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000264_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2334 = (segment_000264_pm_final pmStore) 2334 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 5) ({ rank := 1, op := "OpName.BW_linear", ins := [2334, 2314, 645], outs := [2332, 2333] } :: (segment_000264_pm_nodes.drop 6)) 2334
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000264_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2314 = (segment_000264_pm_final pmStore) 2314 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 5) ({ rank := 1, op := "OpName.BW_linear", ins := [2334, 2314, 645], outs := [2332, 2333] } :: (segment_000264_pm_nodes.drop 6)) 2314
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000264_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 645 = (segment_000264_pm_final pmStore) 645 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 5) ({ rank := 1, op := "OpName.BW_linear", ins := [2334, 2314, 645], outs := [2332, 2333] } :: (segment_000264_pm_nodes.drop 6)) 645
      (by native_decide) (by native_decide)
  have hout : (segment_000264_pm_final pmStore) 2332 = (bw_linear ((segment_000264_pm_final pmStore) 2334) ((segment_000264_pm_final pmStore) 2314) ((segment_000264_pm_final pmStore) 645)).1 := by
    calc
      _ = (bw_linear (((segment_000264_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2334) (((segment_000264_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2314) (((segment_000264_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 645)).1 := hout_prefix
      _ = (bw_linear ((segment_000264_pm_final pmStore) 2334) ((segment_000264_pm_final pmStore) 2314) ((segment_000264_pm_final pmStore) 645)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000264_hLinearPm2(pmStore:Store):(segment_000264_pm_final pmStore) 2335=(bw_linear ((segment_000264_pm_final pmStore) 2337) ((segment_000264_pm_final pmStore) 2315) ((segment_000264_pm_final pmStore) 645)).1:=by
  have hfinal:(segment_000264_pm_final pmStore)=segment_000264_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000264_pm_final;rfl
  have hout_nodes : segment_000264_pm_nodes = (segment_000264_pm_nodes.take 6) ++ [{ rank := 2, op := "OpName.BW_linear", ins := [2337, 2315, 645], outs := [2335, 2336] }] ++ (segment_000264_pm_nodes.drop 7) := by
    native_decide
  have hout_prefix : (segment_000264_pm_final pmStore) 2335 = (bw_linear (((segment_000264_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2337) (((segment_000264_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2315) (((segment_000264_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 645)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 6) (segment_000264_pm_nodes.drop 7)
      { rank := 2, op := "OpName.BW_linear", ins := [2337, 2315, 645], outs := [2335, 2336] } 2335
      (fun t => (bw_linear (t 2337) (t 2315) (t 645)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out TrainVerify.Denote.Generated.pm t 2 2337 2315 645 2335 2336 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000264_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2337 = (segment_000264_pm_final pmStore) 2337 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 6) ({ rank := 2, op := "OpName.BW_linear", ins := [2337, 2315, 645], outs := [2335, 2336] } :: (segment_000264_pm_nodes.drop 7)) 2337
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000264_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2315 = (segment_000264_pm_final pmStore) 2315 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 6) ({ rank := 2, op := "OpName.BW_linear", ins := [2337, 2315, 645], outs := [2335, 2336] } :: (segment_000264_pm_nodes.drop 7)) 2315
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000264_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 645 = (segment_000264_pm_final pmStore) 645 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 6) ({ rank := 2, op := "OpName.BW_linear", ins := [2337, 2315, 645], outs := [2335, 2336] } :: (segment_000264_pm_nodes.drop 7)) 645
      (by native_decide) (by native_decide)
  have hout : (segment_000264_pm_final pmStore) 2335 = (bw_linear ((segment_000264_pm_final pmStore) 2337) ((segment_000264_pm_final pmStore) 2315) ((segment_000264_pm_final pmStore) 645)).1 := by
    calc
      _ = (bw_linear (((segment_000264_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2337) (((segment_000264_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2315) (((segment_000264_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 645)).1 := hout_prefix
      _ = (bw_linear ((segment_000264_pm_final pmStore) 2337) ((segment_000264_pm_final pmStore) 2315) ((segment_000264_pm_final pmStore) 645)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000264_hLinearPm3(pmStore:Store):(segment_000264_pm_final pmStore) 2338=(bw_linear ((segment_000264_pm_final pmStore) 2340) ((segment_000264_pm_final pmStore) 2316) ((segment_000264_pm_final pmStore) 645)).1:=by
  have hfinal:(segment_000264_pm_final pmStore)=segment_000264_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000264_pm_final;rfl
  have hout_nodes : segment_000264_pm_nodes = (segment_000264_pm_nodes.take 7) ++ [{ rank := 3, op := "OpName.BW_linear", ins := [2340, 2316, 645], outs := [2338, 2339] }] ++ (segment_000264_pm_nodes.drop 8) := by
    native_decide
  have hout_prefix : (segment_000264_pm_final pmStore) 2338 = (bw_linear (((segment_000264_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2340) (((segment_000264_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2316) (((segment_000264_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 645)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 7) (segment_000264_pm_nodes.drop 8)
      { rank := 3, op := "OpName.BW_linear", ins := [2340, 2316, 645], outs := [2338, 2339] } 2338
      (fun t => (bw_linear (t 2340) (t 2316) (t 645)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out TrainVerify.Denote.Generated.pm t 3 2340 2316 645 2338 2339 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000264_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2340 = (segment_000264_pm_final pmStore) 2340 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_linear", ins := [2340, 2316, 645], outs := [2338, 2339] } :: (segment_000264_pm_nodes.drop 8)) 2340
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000264_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2316 = (segment_000264_pm_final pmStore) 2316 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_linear", ins := [2340, 2316, 645], outs := [2338, 2339] } :: (segment_000264_pm_nodes.drop 8)) 2316
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000264_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 645 = (segment_000264_pm_final pmStore) 645 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_linear", ins := [2340, 2316, 645], outs := [2338, 2339] } :: (segment_000264_pm_nodes.drop 8)) 645
      (by native_decide) (by native_decide)
  have hout : (segment_000264_pm_final pmStore) 2338 = (bw_linear ((segment_000264_pm_final pmStore) 2340) ((segment_000264_pm_final pmStore) 2316) ((segment_000264_pm_final pmStore) 645)).1 := by
    calc
      _ = (bw_linear (((segment_000264_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2340) (((segment_000264_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2316) (((segment_000264_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 645)).1 := hout_prefix
      _ = (bw_linear ((segment_000264_pm_final pmStore) 2340) ((segment_000264_pm_final pmStore) 2316) ((segment_000264_pm_final pmStore) 645)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000264_hLinearDwSm(smStore:Store):(segment_000264_sm_final smStore) 819=(bw_linear ((segment_000264_sm_final smStore) 820) ((segment_000264_sm_final smStore) 1012) ((segment_000264_sm_final smStore) 645)).2:=by
  have hfinal:(segment_000264_sm_final smStore)=segment_000264_sm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore:=by unfold segment_000264_sm_final;rfl
  have hout_nodes : segment_000264_sm_nodes = (segment_000264_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [820, 1012, 645], outs := [1013, 819] }] ++ (segment_000264_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000264_sm_final smStore) 819 = (bw_linear (((segment_000264_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 820) (((segment_000264_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 1012) (((segment_000264_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 645)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.sm smStore
      (segment_000264_sm_nodes.take 0) (segment_000264_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [820, 1012, 645], outs := [1013, 819] } 819
      (fun t => (bw_linear (t 820) (t 1012) (t 645)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out TrainVerify.Denote.Generated.sm t 0 820 1012 645 1013 819 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000264_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 820 = (segment_000264_sm_final smStore) 820 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000264_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [820, 1012, 645], outs := [1013, 819] } :: (segment_000264_sm_nodes.drop 1)) 820
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000264_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 1012 = (segment_000264_sm_final smStore) 1012 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000264_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [820, 1012, 645], outs := [1013, 819] } :: (segment_000264_sm_nodes.drop 1)) 1012
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000264_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 645 = (segment_000264_sm_final smStore) 645 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000264_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [820, 1012, 645], outs := [1013, 819] } :: (segment_000264_sm_nodes.drop 1)) 645
      (by native_decide) (by native_decide)
  have hout : (segment_000264_sm_final smStore) 819 = (bw_linear ((segment_000264_sm_final smStore) 820) ((segment_000264_sm_final smStore) 1012) ((segment_000264_sm_final smStore) 645)).2 := by
    calc
      _ = (bw_linear (((segment_000264_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 820) (((segment_000264_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 1012) (((segment_000264_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 645)).2 := hout_prefix
      _ = (bw_linear ((segment_000264_sm_final smStore) 820) ((segment_000264_sm_final smStore) 1012) ((segment_000264_sm_final smStore) 645)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000264_hLinearDwPm0(pmStore:Store):(segment_000264_pm_final pmStore) 2330=(bw_linear ((segment_000264_pm_final pmStore) 2331) ((segment_000264_pm_final pmStore) 2313) ((segment_000264_pm_final pmStore) 645)).2:=by
  have hfinal:(segment_000264_pm_final pmStore)=segment_000264_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000264_pm_final;rfl
  have hout_nodes : segment_000264_pm_nodes = (segment_000264_pm_nodes.take 4) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [2331, 2313, 645], outs := [2329, 2330] }] ++ (segment_000264_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000264_pm_final pmStore) 2330 = (bw_linear (((segment_000264_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2331) (((segment_000264_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2313) (((segment_000264_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 645)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 4) (segment_000264_pm_nodes.drop 5)
      { rank := 0, op := "OpName.BW_linear", ins := [2331, 2313, 645], outs := [2329, 2330] } 2330
      (fun t => (bw_linear (t 2331) (t 2313) (t 645)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out TrainVerify.Denote.Generated.pm t 0 2331 2313 645 2329 2330 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000264_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2331 = (segment_000264_pm_final pmStore) 2331 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 4) ({ rank := 0, op := "OpName.BW_linear", ins := [2331, 2313, 645], outs := [2329, 2330] } :: (segment_000264_pm_nodes.drop 5)) 2331
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000264_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2313 = (segment_000264_pm_final pmStore) 2313 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 4) ({ rank := 0, op := "OpName.BW_linear", ins := [2331, 2313, 645], outs := [2329, 2330] } :: (segment_000264_pm_nodes.drop 5)) 2313
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000264_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 645 = (segment_000264_pm_final pmStore) 645 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 4) ({ rank := 0, op := "OpName.BW_linear", ins := [2331, 2313, 645], outs := [2329, 2330] } :: (segment_000264_pm_nodes.drop 5)) 645
      (by native_decide) (by native_decide)
  have hout : (segment_000264_pm_final pmStore) 2330 = (bw_linear ((segment_000264_pm_final pmStore) 2331) ((segment_000264_pm_final pmStore) 2313) ((segment_000264_pm_final pmStore) 645)).2 := by
    calc
      _ = (bw_linear (((segment_000264_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2331) (((segment_000264_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2313) (((segment_000264_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 645)).2 := hout_prefix
      _ = (bw_linear ((segment_000264_pm_final pmStore) 2331) ((segment_000264_pm_final pmStore) 2313) ((segment_000264_pm_final pmStore) 645)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000264_hLinearDwPm1(pmStore:Store):(segment_000264_pm_final pmStore) 2333=(bw_linear ((segment_000264_pm_final pmStore) 2334) ((segment_000264_pm_final pmStore) 2314) ((segment_000264_pm_final pmStore) 645)).2:=by
  have hfinal:(segment_000264_pm_final pmStore)=segment_000264_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000264_pm_final;rfl
  have hout_nodes : segment_000264_pm_nodes = (segment_000264_pm_nodes.take 5) ++ [{ rank := 1, op := "OpName.BW_linear", ins := [2334, 2314, 645], outs := [2332, 2333] }] ++ (segment_000264_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000264_pm_final pmStore) 2333 = (bw_linear (((segment_000264_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2334) (((segment_000264_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2314) (((segment_000264_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 645)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 5) (segment_000264_pm_nodes.drop 6)
      { rank := 1, op := "OpName.BW_linear", ins := [2334, 2314, 645], outs := [2332, 2333] } 2333
      (fun t => (bw_linear (t 2334) (t 2314) (t 645)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out TrainVerify.Denote.Generated.pm t 1 2334 2314 645 2332 2333 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000264_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2334 = (segment_000264_pm_final pmStore) 2334 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 5) ({ rank := 1, op := "OpName.BW_linear", ins := [2334, 2314, 645], outs := [2332, 2333] } :: (segment_000264_pm_nodes.drop 6)) 2334
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000264_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2314 = (segment_000264_pm_final pmStore) 2314 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 5) ({ rank := 1, op := "OpName.BW_linear", ins := [2334, 2314, 645], outs := [2332, 2333] } :: (segment_000264_pm_nodes.drop 6)) 2314
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000264_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 645 = (segment_000264_pm_final pmStore) 645 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 5) ({ rank := 1, op := "OpName.BW_linear", ins := [2334, 2314, 645], outs := [2332, 2333] } :: (segment_000264_pm_nodes.drop 6)) 645
      (by native_decide) (by native_decide)
  have hout : (segment_000264_pm_final pmStore) 2333 = (bw_linear ((segment_000264_pm_final pmStore) 2334) ((segment_000264_pm_final pmStore) 2314) ((segment_000264_pm_final pmStore) 645)).2 := by
    calc
      _ = (bw_linear (((segment_000264_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2334) (((segment_000264_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2314) (((segment_000264_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 645)).2 := hout_prefix
      _ = (bw_linear ((segment_000264_pm_final pmStore) 2334) ((segment_000264_pm_final pmStore) 2314) ((segment_000264_pm_final pmStore) 645)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000264_hLinearDwPm2(pmStore:Store):(segment_000264_pm_final pmStore) 2336=(bw_linear ((segment_000264_pm_final pmStore) 2337) ((segment_000264_pm_final pmStore) 2315) ((segment_000264_pm_final pmStore) 645)).2:=by
  have hfinal:(segment_000264_pm_final pmStore)=segment_000264_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000264_pm_final;rfl
  have hout_nodes : segment_000264_pm_nodes = (segment_000264_pm_nodes.take 6) ++ [{ rank := 2, op := "OpName.BW_linear", ins := [2337, 2315, 645], outs := [2335, 2336] }] ++ (segment_000264_pm_nodes.drop 7) := by
    native_decide
  have hout_prefix : (segment_000264_pm_final pmStore) 2336 = (bw_linear (((segment_000264_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2337) (((segment_000264_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2315) (((segment_000264_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 645)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 6) (segment_000264_pm_nodes.drop 7)
      { rank := 2, op := "OpName.BW_linear", ins := [2337, 2315, 645], outs := [2335, 2336] } 2336
      (fun t => (bw_linear (t 2337) (t 2315) (t 645)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out TrainVerify.Denote.Generated.pm t 2 2337 2315 645 2335 2336 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000264_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2337 = (segment_000264_pm_final pmStore) 2337 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 6) ({ rank := 2, op := "OpName.BW_linear", ins := [2337, 2315, 645], outs := [2335, 2336] } :: (segment_000264_pm_nodes.drop 7)) 2337
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000264_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2315 = (segment_000264_pm_final pmStore) 2315 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 6) ({ rank := 2, op := "OpName.BW_linear", ins := [2337, 2315, 645], outs := [2335, 2336] } :: (segment_000264_pm_nodes.drop 7)) 2315
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000264_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 645 = (segment_000264_pm_final pmStore) 645 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 6) ({ rank := 2, op := "OpName.BW_linear", ins := [2337, 2315, 645], outs := [2335, 2336] } :: (segment_000264_pm_nodes.drop 7)) 645
      (by native_decide) (by native_decide)
  have hout : (segment_000264_pm_final pmStore) 2336 = (bw_linear ((segment_000264_pm_final pmStore) 2337) ((segment_000264_pm_final pmStore) 2315) ((segment_000264_pm_final pmStore) 645)).2 := by
    calc
      _ = (bw_linear (((segment_000264_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2337) (((segment_000264_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2315) (((segment_000264_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 645)).2 := hout_prefix
      _ = (bw_linear ((segment_000264_pm_final pmStore) 2337) ((segment_000264_pm_final pmStore) 2315) ((segment_000264_pm_final pmStore) 645)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000264_hLinearDwPm3(pmStore:Store):(segment_000264_pm_final pmStore) 2339=(bw_linear ((segment_000264_pm_final pmStore) 2340) ((segment_000264_pm_final pmStore) 2316) ((segment_000264_pm_final pmStore) 645)).2:=by
  have hfinal:(segment_000264_pm_final pmStore)=segment_000264_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000264_pm_final;rfl
  have hout_nodes : segment_000264_pm_nodes = (segment_000264_pm_nodes.take 7) ++ [{ rank := 3, op := "OpName.BW_linear", ins := [2340, 2316, 645], outs := [2338, 2339] }] ++ (segment_000264_pm_nodes.drop 8) := by
    native_decide
  have hout_prefix : (segment_000264_pm_final pmStore) 2339 = (bw_linear (((segment_000264_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2340) (((segment_000264_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2316) (((segment_000264_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 645)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 7) (segment_000264_pm_nodes.drop 8)
      { rank := 3, op := "OpName.BW_linear", ins := [2340, 2316, 645], outs := [2338, 2339] } 2339
      (fun t => (bw_linear (t 2340) (t 2316) (t 645)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out TrainVerify.Denote.Generated.pm t 3 2340 2316 645 2338 2339 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000264_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2340 = (segment_000264_pm_final pmStore) 2340 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_linear", ins := [2340, 2316, 645], outs := [2338, 2339] } :: (segment_000264_pm_nodes.drop 8)) 2340
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000264_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2316 = (segment_000264_pm_final pmStore) 2316 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_linear", ins := [2340, 2316, 645], outs := [2338, 2339] } :: (segment_000264_pm_nodes.drop 8)) 2316
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000264_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 645 = (segment_000264_pm_final pmStore) 645 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_linear", ins := [2340, 2316, 645], outs := [2338, 2339] } :: (segment_000264_pm_nodes.drop 8)) 645
      (by native_decide) (by native_decide)
  have hout : (segment_000264_pm_final pmStore) 2339 = (bw_linear ((segment_000264_pm_final pmStore) 2340) ((segment_000264_pm_final pmStore) 2316) ((segment_000264_pm_final pmStore) 645)).2 := by
    calc
      _ = (bw_linear (((segment_000264_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2340) (((segment_000264_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2316) (((segment_000264_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 645)).2 := hout_prefix
      _ = (bw_linear ((segment_000264_pm_final pmStore) 2340) ((segment_000264_pm_final pmStore) 2316) ((segment_000264_pm_final pmStore) 645)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000264_hTr0Sm(smStore:Store):(segment_000264_sm_final smStore) 821=transposeAxes 1 2 ((segment_000264_sm_final smStore) 822):=by
  have hfinal:(segment_000264_sm_final smStore)=segment_000264_sm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore:=by unfold segment_000264_sm_final;rfl
  have hout_nodes : segment_000264_sm_nodes = (segment_000264_sm_nodes.take 2) ++ [{ rank := 0, op := "OpName.BW_transpose", ins := [822, 647], outs := [821], params := [1, 2] }] ++ (segment_000264_sm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000264_sm_final smStore) 821 = transposeAxes 1 2 (((segment_000264_sm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 822) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.sm smStore
      (segment_000264_sm_nodes.take 2) (segment_000264_sm_nodes.drop 3)
      { rank := 0, op := "OpName.BW_transpose", ins := [822, 647], outs := [821], params := [1, 2] } 821
      (fun t => transposeAxes 1 2 (t 822)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out TrainVerify.Denote.Generated.sm t 0 822 647 821 1 2
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000264_sm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 822 = (segment_000264_sm_final smStore) 822 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000264_sm_nodes.take 2) ({ rank := 0, op := "OpName.BW_transpose", ins := [822, 647], outs := [821], params := [1, 2] } :: (segment_000264_sm_nodes.drop 3)) 822
      (by native_decide) (by native_decide)
  have hout : (segment_000264_sm_final smStore) 821 = transposeAxes 1 2 ((segment_000264_sm_final smStore) 822) := by
    calc
      _ = transposeAxes 1 2 (((segment_000264_sm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 822) := hout_prefix
      _ = transposeAxes 1 2 ((segment_000264_sm_final smStore) 822) := by rw [hout_read_0]
  exact hout

private theorem segment_000264_hTr0Pm0(pmStore:Store):(segment_000264_pm_final pmStore) 2357=transposeAxes 1 2 ((segment_000264_pm_final pmStore) 2358):=by
  have hfinal:(segment_000264_pm_final pmStore)=segment_000264_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000264_pm_final;rfl
  have hout_nodes : segment_000264_pm_nodes = (segment_000264_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_transpose", ins := [2358, 2341], outs := [2357], params := [1, 2] }] ++ (segment_000264_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000264_pm_final pmStore) 2357 = transposeAxes 1 2 (((segment_000264_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2358) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 0) (segment_000264_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_transpose", ins := [2358, 2341], outs := [2357], params := [1, 2] } 2357
      (fun t => transposeAxes 1 2 (t 2358)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out TrainVerify.Denote.Generated.pm t 0 2358 2341 2357 1 2
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000264_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2358 = (segment_000264_pm_final pmStore) 2358 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_transpose", ins := [2358, 2341], outs := [2357], params := [1, 2] } :: (segment_000264_pm_nodes.drop 1)) 2358
      (by native_decide) (by native_decide)
  have hout : (segment_000264_pm_final pmStore) 2357 = transposeAxes 1 2 ((segment_000264_pm_final pmStore) 2358) := by
    calc
      _ = transposeAxes 1 2 (((segment_000264_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2358) := hout_prefix
      _ = transposeAxes 1 2 ((segment_000264_pm_final pmStore) 2358) := by rw [hout_read_0]
  exact hout

private theorem segment_000264_hTr0Pm1(pmStore:Store):(segment_000264_pm_final pmStore) 2359=transposeAxes 1 2 ((segment_000264_pm_final pmStore) 2360):=by
  have hfinal:(segment_000264_pm_final pmStore)=segment_000264_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000264_pm_final;rfl
  have hout_nodes : segment_000264_pm_nodes = (segment_000264_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_transpose", ins := [2360, 2342], outs := [2359], params := [1, 2] }] ++ (segment_000264_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000264_pm_final pmStore) 2359 = transposeAxes 1 2 (((segment_000264_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2360) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 1) (segment_000264_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_transpose", ins := [2360, 2342], outs := [2359], params := [1, 2] } 2359
      (fun t => transposeAxes 1 2 (t 2360)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out TrainVerify.Denote.Generated.pm t 1 2360 2342 2359 1 2
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000264_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2360 = (segment_000264_pm_final pmStore) 2360 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_transpose", ins := [2360, 2342], outs := [2359], params := [1, 2] } :: (segment_000264_pm_nodes.drop 2)) 2360
      (by native_decide) (by native_decide)
  have hout : (segment_000264_pm_final pmStore) 2359 = transposeAxes 1 2 ((segment_000264_pm_final pmStore) 2360) := by
    calc
      _ = transposeAxes 1 2 (((segment_000264_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2360) := hout_prefix
      _ = transposeAxes 1 2 ((segment_000264_pm_final pmStore) 2360) := by rw [hout_read_0]
  exact hout

private theorem segment_000264_hTr0Pm2(pmStore:Store):(segment_000264_pm_final pmStore) 2361=transposeAxes 1 2 ((segment_000264_pm_final pmStore) 2362):=by
  have hfinal:(segment_000264_pm_final pmStore)=segment_000264_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000264_pm_final;rfl
  have hout_nodes : segment_000264_pm_nodes = (segment_000264_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_transpose", ins := [2362, 2343], outs := [2361], params := [1, 2] }] ++ (segment_000264_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000264_pm_final pmStore) 2361 = transposeAxes 1 2 (((segment_000264_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2362) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 2) (segment_000264_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_transpose", ins := [2362, 2343], outs := [2361], params := [1, 2] } 2361
      (fun t => transposeAxes 1 2 (t 2362)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out TrainVerify.Denote.Generated.pm t 2 2362 2343 2361 1 2
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000264_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2362 = (segment_000264_pm_final pmStore) 2362 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_transpose", ins := [2362, 2343], outs := [2361], params := [1, 2] } :: (segment_000264_pm_nodes.drop 3)) 2362
      (by native_decide) (by native_decide)
  have hout : (segment_000264_pm_final pmStore) 2361 = transposeAxes 1 2 ((segment_000264_pm_final pmStore) 2362) := by
    calc
      _ = transposeAxes 1 2 (((segment_000264_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2362) := hout_prefix
      _ = transposeAxes 1 2 ((segment_000264_pm_final pmStore) 2362) := by rw [hout_read_0]
  exact hout

private theorem segment_000264_hTr0Pm3(pmStore:Store):(segment_000264_pm_final pmStore) 2363=transposeAxes 1 2 ((segment_000264_pm_final pmStore) 2364):=by
  have hfinal:(segment_000264_pm_final pmStore)=segment_000264_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000264_pm_final;rfl
  have hout_nodes : segment_000264_pm_nodes = (segment_000264_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_transpose", ins := [2364, 2344], outs := [2363], params := [1, 2] }] ++ (segment_000264_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000264_pm_final pmStore) 2363 = transposeAxes 1 2 (((segment_000264_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2364) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 3) (segment_000264_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_transpose", ins := [2364, 2344], outs := [2363], params := [1, 2] } 2363
      (fun t => transposeAxes 1 2 (t 2364)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out TrainVerify.Denote.Generated.pm t 3 2364 2344 2363 1 2
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000264_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2364 = (segment_000264_pm_final pmStore) 2364 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_transpose", ins := [2364, 2344], outs := [2363], params := [1, 2] } :: (segment_000264_pm_nodes.drop 4)) 2364
      (by native_decide) (by native_decide)
  have hout : (segment_000264_pm_final pmStore) 2363 = transposeAxes 1 2 ((segment_000264_pm_final pmStore) 2364) := by
    calc
      _ = transposeAxes 1 2 (((segment_000264_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2364) := hout_prefix
      _ = transposeAxes 1 2 ((segment_000264_pm_final pmStore) 2364) := by rw [hout_read_0]
  exact hout

private theorem segment_000264_hTr1Sm(smStore:Store):(segment_000264_sm_final smStore) 824=transposeAxes 2 3 ((segment_000264_sm_final smStore) 827):=by
  have hfinal:(segment_000264_sm_final smStore)=segment_000264_sm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore:=by unfold segment_000264_sm_final;rfl
  have hout_nodes : segment_000264_sm_nodes = (segment_000264_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_transpose", ins := [827, 650], outs := [824], params := [2, 3] }] ++ (segment_000264_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000264_sm_final smStore) 824 = transposeAxes 2 3 (((segment_000264_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 827) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.sm smStore
      (segment_000264_sm_nodes.take 1) (segment_000264_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_transpose", ins := [827, 650], outs := [824], params := [2, 3] } 824
      (fun t => transposeAxes 2 3 (t 827)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out TrainVerify.Denote.Generated.sm t 0 827 650 824 2 3
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000264_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 827 = (segment_000264_sm_final smStore) 827 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000264_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_transpose", ins := [827, 650], outs := [824], params := [2, 3] } :: (segment_000264_sm_nodes.drop 2)) 827
      (by native_decide) (by native_decide)
  have hout : (segment_000264_sm_final smStore) 824 = transposeAxes 2 3 ((segment_000264_sm_final smStore) 827) := by
    calc
      _ = transposeAxes 2 3 (((segment_000264_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 827) := hout_prefix
      _ = transposeAxes 2 3 ((segment_000264_sm_final smStore) 827) := by rw [hout_read_0]
  exact hout

private theorem segment_000264_hTr1Pm0(pmStore:Store):(segment_000264_pm_final pmStore) 2429=transposeAxes 2 3 ((segment_000264_pm_final pmStore) 2430):=by
  have hfinal:(segment_000264_pm_final pmStore)=segment_000264_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000264_pm_final;rfl
  have hout_nodes : segment_000264_pm_nodes = (segment_000264_pm_nodes.take 8) ++ [{ rank := 0, op := "OpName.BW_transpose", ins := [2430, 2413], outs := [2429], params := [2, 3] }] ++ (segment_000264_pm_nodes.drop 9) := by
    native_decide
  have hout_prefix : (segment_000264_pm_final pmStore) 2429 = transposeAxes 2 3 (((segment_000264_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2430) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 8) (segment_000264_pm_nodes.drop 9)
      { rank := 0, op := "OpName.BW_transpose", ins := [2430, 2413], outs := [2429], params := [2, 3] } 2429
      (fun t => transposeAxes 2 3 (t 2430)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out TrainVerify.Denote.Generated.pm t 0 2430 2413 2429 2 3
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000264_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2430 = (segment_000264_pm_final pmStore) 2430 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 8) ({ rank := 0, op := "OpName.BW_transpose", ins := [2430, 2413], outs := [2429], params := [2, 3] } :: (segment_000264_pm_nodes.drop 9)) 2430
      (by native_decide) (by native_decide)
  have hout : (segment_000264_pm_final pmStore) 2429 = transposeAxes 2 3 ((segment_000264_pm_final pmStore) 2430) := by
    calc
      _ = transposeAxes 2 3 (((segment_000264_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2430) := hout_prefix
      _ = transposeAxes 2 3 ((segment_000264_pm_final pmStore) 2430) := by rw [hout_read_0]
  exact hout

private theorem segment_000264_hTr1Pm1(pmStore:Store):(segment_000264_pm_final pmStore) 2431=transposeAxes 2 3 ((segment_000264_pm_final pmStore) 2432):=by
  have hfinal:(segment_000264_pm_final pmStore)=segment_000264_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000264_pm_final;rfl
  have hout_nodes : segment_000264_pm_nodes = (segment_000264_pm_nodes.take 9) ++ [{ rank := 1, op := "OpName.BW_transpose", ins := [2432, 2414], outs := [2431], params := [2, 3] }] ++ (segment_000264_pm_nodes.drop 10) := by
    native_decide
  have hout_prefix : (segment_000264_pm_final pmStore) 2431 = transposeAxes 2 3 (((segment_000264_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2432) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 9) (segment_000264_pm_nodes.drop 10)
      { rank := 1, op := "OpName.BW_transpose", ins := [2432, 2414], outs := [2431], params := [2, 3] } 2431
      (fun t => transposeAxes 2 3 (t 2432)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out TrainVerify.Denote.Generated.pm t 1 2432 2414 2431 2 3
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000264_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2432 = (segment_000264_pm_final pmStore) 2432 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 9) ({ rank := 1, op := "OpName.BW_transpose", ins := [2432, 2414], outs := [2431], params := [2, 3] } :: (segment_000264_pm_nodes.drop 10)) 2432
      (by native_decide) (by native_decide)
  have hout : (segment_000264_pm_final pmStore) 2431 = transposeAxes 2 3 ((segment_000264_pm_final pmStore) 2432) := by
    calc
      _ = transposeAxes 2 3 (((segment_000264_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2432) := hout_prefix
      _ = transposeAxes 2 3 ((segment_000264_pm_final pmStore) 2432) := by rw [hout_read_0]
  exact hout

private theorem segment_000264_hTr1Pm2(pmStore:Store):(segment_000264_pm_final pmStore) 2433=transposeAxes 2 3 ((segment_000264_pm_final pmStore) 2434):=by
  have hfinal:(segment_000264_pm_final pmStore)=segment_000264_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000264_pm_final;rfl
  have hout_nodes : segment_000264_pm_nodes = (segment_000264_pm_nodes.take 10) ++ [{ rank := 2, op := "OpName.BW_transpose", ins := [2434, 2415], outs := [2433], params := [2, 3] }] ++ (segment_000264_pm_nodes.drop 11) := by
    native_decide
  have hout_prefix : (segment_000264_pm_final pmStore) 2433 = transposeAxes 2 3 (((segment_000264_pm_nodes.take 10)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2434) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 10) (segment_000264_pm_nodes.drop 11)
      { rank := 2, op := "OpName.BW_transpose", ins := [2434, 2415], outs := [2433], params := [2, 3] } 2433
      (fun t => transposeAxes 2 3 (t 2434)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out TrainVerify.Denote.Generated.pm t 2 2434 2415 2433 2 3
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000264_pm_nodes.take 10)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2434 = (segment_000264_pm_final pmStore) 2434 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 10) ({ rank := 2, op := "OpName.BW_transpose", ins := [2434, 2415], outs := [2433], params := [2, 3] } :: (segment_000264_pm_nodes.drop 11)) 2434
      (by native_decide) (by native_decide)
  have hout : (segment_000264_pm_final pmStore) 2433 = transposeAxes 2 3 ((segment_000264_pm_final pmStore) 2434) := by
    calc
      _ = transposeAxes 2 3 (((segment_000264_pm_nodes.take 10)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2434) := hout_prefix
      _ = transposeAxes 2 3 ((segment_000264_pm_final pmStore) 2434) := by rw [hout_read_0]
  exact hout

private theorem segment_000264_hTr1Pm3(pmStore:Store):(segment_000264_pm_final pmStore) 2435=transposeAxes 2 3 ((segment_000264_pm_final pmStore) 2436):=by
  have hfinal:(segment_000264_pm_final pmStore)=segment_000264_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000264_pm_final;rfl
  have hout_nodes : segment_000264_pm_nodes = (segment_000264_pm_nodes.take 11) ++ [{ rank := 3, op := "OpName.BW_transpose", ins := [2436, 2416], outs := [2435], params := [2, 3] }] ++ (segment_000264_pm_nodes.drop 12) := by
    native_decide
  have hout_prefix : (segment_000264_pm_final pmStore) 2435 = transposeAxes 2 3 (((segment_000264_pm_nodes.take 11)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2436) := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 11) (segment_000264_pm_nodes.drop 12)
      { rank := 3, op := "OpName.BW_transpose", ins := [2436, 2416], outs := [2435], params := [2, 3] } 2435
      (fun t => transposeAxes 2 3 (t 2436)) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_transposeAxes_out TrainVerify.Denote.Generated.pm t 3 2436 2416 2435 2 3
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000264_pm_nodes.take 11)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2436 = (segment_000264_pm_final pmStore) 2436 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000264_pm_nodes.take 11) ({ rank := 3, op := "OpName.BW_transpose", ins := [2436, 2416], outs := [2435], params := [2, 3] } :: (segment_000264_pm_nodes.drop 12)) 2436
      (by native_decide) (by native_decide)
  have hout : (segment_000264_pm_final pmStore) 2435 = transposeAxes 2 3 ((segment_000264_pm_final pmStore) 2436) := by
    calc
      _ = transposeAxes 2 3 (((segment_000264_pm_nodes.take 11)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2436) := hout_prefix
      _ = transposeAxes 2 3 ((segment_000264_pm_final pmStore) 2436) := by rw [hout_read_0]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000264_sound (smStore pmStore : Store) (hstate : state_000264.Holds smStore pmStore) : state_000265.Holds (segment_000264_sm_final smStore) (segment_000264_pm_final pmStore) := by
 let smFinal:=segment_000264_sm_final smStore
 let pmFinal:=segment_000264_pm_final pmStore
 have hframe:state_000264.Holds smFinal pmFinal:=by unfold smFinal pmFinal segment_000264_sm_final segment_000264_pm_final;apply RelationState.Holds.fold_frame segment_000264_sm_nodes segment_000264_pm_nodes smStore pmStore hstate <;> native_decide
 have hlg:fact_000273.Holds smFinal pmFinal:=hframe _ (by native_decide)
 change ShardedRel (smFinal 820) [pmFinal 2331, pmFinal 2334, pmFinal 2337, pmFinal 2340] 1 [1, 8, 32] [1, 2, 32] at hlg
 have hlgV:smFinal 820=allGatherPrimDimN 1 4 0 [pmFinal 2331, pmFinal 2334, pmFinal 2337, pmFinal 2340]:=by simpa only [List.length_cons,List.length_nil] using hlg.full_value
 have hlx:fact_000454.Holds smFinal pmFinal:=hframe _ (by native_decide)
 change ShardedRel (smFinal 1012) [pmFinal 2313, pmFinal 2314, pmFinal 2315, pmFinal 2316] 1 [1, 8, 32] [1, 2, 32] at hlx
 have hlxV:smFinal 1012=allGatherPrimDimN 1 4 0 [pmFinal 2313, pmFinal 2314, pmFinal 2315, pmFinal 2316]:=by simpa only [List.length_cons,List.length_nil] using hlx.full_value
 have hw:fact_000153.Holds smFinal pmFinal:=hframe _ (by native_decide)
 change ShardedRel (smFinal 645) [pmFinal 645] 0 [32, 32] [32, 32] at hw
 have hwEq:smFinal 645=pmFinal 645:=by rw [hw.full_value];exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hw.shard_shapes _ (by simp)];native_decide)
 have hLS:=segment_000264_hLinearSm smStore
 change smFinal 1013=(bw_linear (smFinal 820) (smFinal 1012) (smFinal 645)).1 at hLS
 have hDS:=segment_000264_hLinearDwSm smStore
 change smFinal 819=(bw_linear (smFinal 820) (smFinal 1012) (smFinal 645)).2 at hDS
 have hLP0:=segment_000264_hLinearPm0 pmStore
 change pmFinal 2329=(bw_linear (pmFinal 2331) (pmFinal 2313) (pmFinal 645)).1 at hLP0
 have hDP0:=segment_000264_hLinearDwPm0 pmStore
 change pmFinal 2330=(bw_linear (pmFinal 2331) (pmFinal 2313) (pmFinal 645)).2 at hDP0
 have hLP1:=segment_000264_hLinearPm1 pmStore
 change pmFinal 2332=(bw_linear (pmFinal 2334) (pmFinal 2314) (pmFinal 645)).1 at hLP1
 have hDP1:=segment_000264_hLinearDwPm1 pmStore
 change pmFinal 2333=(bw_linear (pmFinal 2334) (pmFinal 2314) (pmFinal 645)).2 at hDP1
 have hLP2:=segment_000264_hLinearPm2 pmStore
 change pmFinal 2335=(bw_linear (pmFinal 2337) (pmFinal 2315) (pmFinal 645)).1 at hLP2
 have hDP2:=segment_000264_hLinearDwPm2 pmStore
 change pmFinal 2336=(bw_linear (pmFinal 2337) (pmFinal 2315) (pmFinal 645)).2 at hDP2
 have hLP3:=segment_000264_hLinearPm3 pmStore
 change pmFinal 2338=(bw_linear (pmFinal 2340) (pmFinal 2316) (pmFinal 645)).1 at hLP3
 have hDP3:=segment_000264_hLinearDwPm3 pmStore
 change pmFinal 2339=(bw_linear (pmFinal 2340) (pmFinal 2316) (pmFinal 645)).2 at hDP3
 have hLC:=TrainVerify.Denote.bw_linear_dx_sequence_allGather_rank3 4 1 2 32 32 [pmFinal 2331, pmFinal 2334, pmFinal 2337, pmFinal 2340] [pmFinal 2313, pmFinal 2314, pmFinal 2315, pmFinal 2316] (smFinal 1012) (pmFinal 645) (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl hlg.shard_shapes hlx.shard_shapes hlx.full_shape (hw.shard_shapes _ (by simp))
 simp only [List.zipWith] at hLC
 have hLV:smFinal 1013=allGatherPrimDimN 1 4 0 [pmFinal 2329, pmFinal 2332, pmFinal 2335, pmFinal 2338]:=by rw [hLS,hlgV,hwEq,hLC];rw [←hLP0, ←hLP1, ←hLP2, ←hLP3]
 have hLVL:smFinal 1013=allGatherPrimDimN 1 [pmFinal 2329, pmFinal 2332, pmFinal 2335, pmFinal 2338].length 0 [pmFinal 2329, pmFinal 2332, pmFinal 2335, pmFinal 2338]:=by simpa only [List.length_cons,List.length_nil] using hLV
 have hLFull:(smFinal 1013).shape=[1, 8, 32]:=by rw [hLS];exact bw_linear_3d_fst_shape 1 8 32 32 _ _ _ hlg.full_shape hlx.full_shape hw.full_shape
 have hLShape0:(pmFinal 2329).shape=[1, 2, 32]:=by rw [hLP0];exact bw_linear_3d_fst_shape 1 2 32 32 _ _ _ (hlg.shard_shapes _ (by simp)) (hlx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hLShape1:(pmFinal 2332).shape=[1, 2, 32]:=by rw [hLP1];exact bw_linear_3d_fst_shape 1 2 32 32 _ _ _ (hlg.shard_shapes _ (by simp)) (hlx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hLShape2:(pmFinal 2335).shape=[1, 2, 32]:=by rw [hLP2];exact bw_linear_3d_fst_shape 1 2 32 32 _ _ _ (hlg.shard_shapes _ (by simp)) (hlx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hLShape3:(pmFinal 2338).shape=[1, 2, 32]:=by rw [hLP3];exact bw_linear_3d_fst_shape 1 2 32 32 _ _ _ (hlg.shard_shapes _ (by simp)) (hlx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hLShapes:∀z∈[pmFinal 2329, pmFinal 2332, pmFinal 2335, pmFinal 2338],z.shape=[1, 2, 32]:=by simp only [List.forall_mem_cons];exact ⟨hLShape0,hLShape1,hLShape2,hLShape3,List.forall_mem_nil _⟩
 have houtL:fact_000277.Holds smFinal pmFinal:=by exact {full_value:=hLVL,full_shape:=hLFull,shards_nonempty:=List.cons_ne_nil _ _,gather_dim_lt:=by native_decide,shard_shapes:=hLShapes,shape_contract:=by simp only [List.map,List.length_cons,List.length_nil];native_decide}
 have hDC:=TrainVerify.Denote.bw_linear_dw_sequence_reduction_rank3 4 1 2 32 32 [pmFinal 2331, pmFinal 2334, pmFinal 2337, pmFinal 2340] [pmFinal 2313, pmFinal 2314, pmFinal 2315, pmFinal 2316] (pmFinal 645) (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl hlg.shard_shapes hlx.shard_shapes (hw.shard_shapes _ (by simp))
 simp only [List.zipWith] at hDC
 have hDsum:smFinal 819=tensorSum [pmFinal 2330, pmFinal 2333, pmFinal 2336, pmFinal 2339]:=by rw [hDS,hlgV,hlxV,hwEq,hDC,←hDP0, ←hDP1, ←hDP2, ←hDP3]
 have hDReduce:smFinal 819=allReducePrim [pmFinal 2330, pmFinal 2333, pmFinal 2336, pmFinal 2339].length 0 [pmFinal 2330, pmFinal 2333, pmFinal 2336, pmFinal 2339]:=by rw [hDsum];rfl
 have hDFull:(smFinal 819).shape=[32, 32]:=by rw [hDS];exact bw_linear_3d_snd_shape 1 8 32 32 _ _ _ hlg.full_shape hlx.full_shape hw.full_shape
 have hDShape0:(pmFinal 2330).shape=[32, 32]:=by rw [hDP0];exact bw_linear_3d_snd_shape 1 2 32 32 _ _ _ (hlg.shard_shapes _ (by simp)) (hlx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hDShape1:(pmFinal 2333).shape=[32, 32]:=by rw [hDP1];exact bw_linear_3d_snd_shape 1 2 32 32 _ _ _ (hlg.shard_shapes _ (by simp)) (hlx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hDShape2:(pmFinal 2336).shape=[32, 32]:=by rw [hDP2];exact bw_linear_3d_snd_shape 1 2 32 32 _ _ _ (hlg.shard_shapes _ (by simp)) (hlx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have hDShape3:(pmFinal 2339).shape=[32, 32]:=by rw [hDP3];exact bw_linear_3d_snd_shape 1 2 32 32 _ _ _ (hlg.shard_shapes _ (by simp)) (hlx.shard_shapes _ (by simp)) (hw.shard_shapes _ (by simp))
 have houtD:test_dw_fact.Holds smFinal pmFinal:=by
  change ReductionRel (smFinal 819) [pmFinal 2330, pmFinal 2333, pmFinal 2336, pmFinal 2339] [32, 32]
  refine {full_value:=hDReduce,full_shape:=hDFull,contributions_nonempty:=by simp,contribution_shapes:=?_,reduced_shape:=?_}
  · intro z hz; simp only [List.mem_cons,List.not_mem_nil,or_false] at hz;rcases hz with h0|h1|h2|h3
    · subst z;exact hDShape0
    · subst z;exact hDShape1
    · subst z;exact hDShape2
    · subst z;exact hDShape3
  · rw [←hDReduce];exact hDFull
 have hti0:fact_000275.Holds smFinal pmFinal:=hframe _ (by native_decide)
 change ShardedRel (smFinal 822) [pmFinal 2358, pmFinal 2360, pmFinal 2362, pmFinal 2364] 1 [1, 1 * [pmFinal 2358, pmFinal 2360, pmFinal 2362, pmFinal 2364].length, 8, 8] [1, 1, 8, 8] at hti0
 have htS0:=segment_000264_hTr0Sm smStore
 change smFinal 821=transposeAxes 1 2 (smFinal 822) at htS0
 have htP0_0:=segment_000264_hTr0Pm0 pmStore
 change pmFinal 2357=transposeAxes 1 2 (pmFinal 2358) at htP0_0
 have htP0_1:=segment_000264_hTr0Pm1 pmStore
 change pmFinal 2359=transposeAxes 1 2 (pmFinal 2360) at htP0_1
 have htP0_2:=segment_000264_hTr0Pm2 pmStore
 change pmFinal 2361=transposeAxes 1 2 (pmFinal 2362) at htP0_2
 have htP0_3:=segment_000264_hTr0Pm3 pmStore
 change pmFinal 2363=transposeAxes 1 2 (pmFinal 2364) at htP0_3
 have htRaw0:=TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim1_to_dim2_rank4 hti0
 have houtT0:fact_000280.Holds smFinal pmFinal:=by change ShardedRel (smFinal 821) [pmFinal 2357, pmFinal 2359, pmFinal 2361, pmFinal 2363] 2 [1, 8, 4, 8] [1, 8, 1, 8];rw [htS0,htP0_0, htP0_1, htP0_2, htP0_3];simpa using htRaw0
 have hti1:fact_000276.Holds smFinal pmFinal:=hframe _ (by native_decide)
 change ShardedRel (smFinal 827) [pmFinal 2430, pmFinal 2432, pmFinal 2434, pmFinal 2436] 1 [1, 1 * [pmFinal 2430, pmFinal 2432, pmFinal 2434, pmFinal 2436].length, 8, 8] [1, 1, 8, 8] at hti1
 have htS1:=segment_000264_hTr1Sm smStore
 change smFinal 824=transposeAxes 2 3 (smFinal 827) at htS1
 have htP1_0:=segment_000264_hTr1Pm0 pmStore
 change pmFinal 2429=transposeAxes 2 3 (pmFinal 2430) at htP1_0
 have htP1_1:=segment_000264_hTr1Pm1 pmStore
 change pmFinal 2431=transposeAxes 2 3 (pmFinal 2432) at htP1_1
 have htP1_2:=segment_000264_hTr1Pm2 pmStore
 change pmFinal 2433=transposeAxes 2 3 (pmFinal 2434) at htP1_2
 have htP1_3:=segment_000264_hTr1Pm3 pmStore
 change pmFinal 2435=transposeAxes 2 3 (pmFinal 2436) at htP1_3
 have htRaw1:=TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim1_rank4 hti1
 have houtT1:fact_000278.Holds smFinal pmFinal:=by change ShardedRel (smFinal 824) [pmFinal 2429, pmFinal 2431, pmFinal 2433, pmFinal 2435] 1 [1, 4, 8, 8] [1, 1, 8, 8];rw [htS1,htP1_0, htP1_1, htP1_2, htP1_3];simpa using htRaw1
 intro fact hfact
 have hc:fact∈[fact_000277,test_dw_fact,fact_000280,fact_000278]++state_000264.facts:=by exact (show state_000265.facts⊆[fact_000277,test_dw_fact,fact_000280,fact_000278]++state_000264.facts by native_decide) hfact
 simp only [List.mem_append] at hc
 rcases hc with fresh|old
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh;rcases fresh with rfl|rfl|rfl|rfl
   · exact houtL
   · exact houtD
   · exact houtT0
   · exact houtT1
 · exact hframe fact old

private def segment_000264:ClosedDepSegmentCertificate TrainVerify.Denote.Generated.sm TrainVerify.Denote.Generated.pm state_000264 state_000265 where
 smNodes:=segment_000264_sm_nodes
 pmNodes:=segment_000264_pm_nodes
 sound:=by intro a b h;have z:=segment_000264_sound a b h;unfold segment_000264_sm_final segment_000264_pm_final at z;exact z

#print axioms segment_000264
end
end TrainVerify.Denote.SequenceDwMixedsegment_000264
