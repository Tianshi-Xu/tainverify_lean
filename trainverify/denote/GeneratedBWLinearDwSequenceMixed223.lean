import denote.gpt_ly4_regen.GeneratedData
import denote.KRankBWLinearDwSequenceGeneral
import denote.KRankBWLinearDxSequence
import denote.KRankBWMatmulHead
/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.SequenceDwMixedsegment_000223

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

private def fact_000088 : RelationFact :=
  .joined 653 653 [1, 4, 8, 8]

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

private def fact_000154 : RelationFact :=
  .sharded 661 [2581, 2582, 2583, 2584] 1 [32, 32] [32, 8]

private def fact_000155 : RelationFact :=
  .sharded 664 [664] 0 [32] [32]

private def fact_000156 : RelationFact :=
  .sharded 665 [665] 0 [32] [32]

private def fact_000157 : RelationFact :=
  .sharded 667 [2673, 2674, 2675, 2676] 1 [128, 32] [128, 8]

private def fact_000158 : RelationFact :=
  .sharded 670 [2725, 2726, 2727, 2728] 1 [32, 128] [32, 32]

private def fact_000159 : RelationFact :=
  .sharded 673 [673] 0 [32] [32]

private def fact_000160 : RelationFact :=
  .sharded 674 [674] 0 [32] [32]

private def fact_000161 : RelationFact :=
  .sharded 676 [2817, 2818, 2819, 2820] 1 [32, 32] [32, 8]

private def fact_000162 : RelationFact :=
  .sharded 678 [2845, 2846, 2847, 2848] 1 [32, 32] [32, 8]

private def fact_000163 : RelationFact :=
  .sharded 680 [680] 0 [32, 32] [32, 32]

private def fact_000172 : RelationFact :=
  .sharded 714 [714] 0 [1, 8] [1, 8]

private def fact_000173 : RelationFact :=
  .sharded 564 [1109, 1110, 1111, 1112] 2 [1, 8, 32] [1, 8, 8]

private def fact_000212 : RelationFact :=
  .sharded 1037 [3189, 3192, 3195, 3198] 1 [1, 8, 32] [1, 2, 32]

private def fact_000216 : RelationFact :=
  .sharded 578 [1261, 1262, 1263, 1264] 3 [1, 4, 8, 8] [1, 4, 8, 2]

private def fact_000228 : RelationFact :=
  .sharded 870 [3010, 3012, 3014, 3016] 1 [1, 4, 8, 8] [1, 1, 8, 8]

private def fact_000229 : RelationFact :=
  .sharded 862 [2887, 2890, 2893, 2896] 1 [1, 8, 32] [1, 2, 32]

private def fact_000230 : RelationFact :=
  .sharded 864 [2914, 2916, 2918, 2920] 1 [1, 4, 8, 8] [1, 1, 8, 8]

private def fact_000231 : RelationFact :=
  .sharded 869 [3009, 3011, 3013, 3015] 1 [1, 4, 8, 8] [1, 1, 8, 8]

private def fact_000233 : RelationFact :=
  .sharded 1056 [2885, 2888, 2891, 2894] 1 [1, 8, 32] [1, 2, 32]

private def fact_000249 : RelationFact :=
  .sharded 582 [1309, 1310, 1311, 1312] 3 [1, 4, 8, 8] [1, 4, 8, 2]

private def fact_000265 : RelationFact :=
  .sharded 583 [1333, 1334, 1335, 1336] 2 [1, 4, 8, 8] [1, 4, 2, 8]

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

private def fact_000447 : RelationFact :=
  .sharded 993 [2605, 2606, 2607, 2608] 1 [1, 8, 32] [1, 2, 32]

private def fact_000448 : RelationFact :=
  .sharded 918 [1173, 1174, 1175, 1176] 1 [1, 8, 32] [1, 2, 32]

private def fact_000449 : RelationFact :=
  .sharded 922 [1201, 1202, 1203, 1204] 1 [1, 8, 32] [1, 2, 32]

private def fact_000454 : RelationFact :=
  .sharded 1012 [2313, 2314, 2315, 2316] 1 [1, 8, 32] [1, 2, 32]

private def fact_000462 : RelationFact :=
  .sharded 648 [2437, 2438, 2439, 2440] 2 [1, 4, 8, 8] [1, 4, 2, 8]

private def fact_000467 : RelationFact :=
  .sharded 652 [2501, 2502, 2503, 2504] 1 [1, 4, 8, 8] [1, 1, 8, 8]

private def fact_000470 : RelationFact :=
  .sharded 655 [2465, 2466, 2467, 2468] 2 [1, 4, 8, 8] [1, 4, 2, 8]

private def fact_000472 : RelationFact :=
  .sharded 656 [2497, 2498, 2499, 2500] 1 [1, 4, 8, 8] [1, 1, 8, 8]

private def fact_000478 : RelationFact :=
  .sharded 660 [2577, 2578, 2579, 2580] 2 [1, 8, 32] [1, 8, 8]

private def fact_000479 : RelationFact :=
  .sharded 662 [2609, 2610, 2611, 2612] 1 [1, 8, 32] [1, 2, 32]

private def fact_000482 : RelationFact :=
  .sharded 1020 [2637, 2638, 2639, 2640] 1 [1, 8, 32] [1, 2, 32]

private def fact_000483 : RelationFact :=
  .sharded 1024 [2749, 2750, 2751, 2752] 1 [1, 8, 32] [1, 2, 32]

private def fact_000485 : RelationFact :=
  .sharded 666 [2669, 2670, 2671, 2672] 2 [1, 8, 32] [1, 8, 8]

private def fact_000486 : RelationFact :=
  .sharded 668 [2697, 2698, 2699, 2700] 1 [1, 8, 128] [1, 2, 128]

private def fact_000488 : RelationFact :=
  .sharded 669 [2721, 2722, 2723, 2724] 2 [1, 8, 128] [1, 8, 32]

private def fact_000489 : RelationFact :=
  .sharded 671 [2753, 2754, 2755, 2756] 1 [1, 8, 32] [1, 2, 32]

private def fact_000491 : RelationFact :=
  .sharded 1032 [2781, 2782, 2783, 2784] 1 [1, 8, 32] [1, 2, 32]

private def fact_000495 : RelationFact :=
  .sharded 1047 [2813, 2814, 2815, 2816] 2 [1, 8, 32] [1, 8, 8]

private def fact_000497 : RelationFact :=
  .sharded 1051 [2841, 2842, 2843, 2844] 2 [1, 8, 32] [1, 8, 8]

private def fact_000498 : RelationFact :=
  .sharded 1055 [2869, 2870, 2871, 2872] 1 [1, 8, 32] [1, 2, 32]

private def fact_000504 : RelationFact :=
  .sharded 683 [2901, 2902, 2903, 2904] 1 [1, 4, 8, 8] [1, 1, 8, 8]

private def fact_000510 : RelationFact :=
  .sharded 688 [2993, 2994, 2995, 2996] 1 [1, 4, 8, 8] [1, 1, 8, 8]

private def test_dw_fact : RelationFact :=
  .reduction 861 [2886, 2889, 2892, 2895] [32, 32]

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

private def authority_transition_eq_sm_664_pm_664 : RelationFact :=
  .tensorEq .sm 664 .pm 664

private def authority_transition_eq_sm_665_pm_665 : RelationFact :=
  .tensorEq .sm 665 .pm 665

private def authority_transition_eq_sm_673_pm_673 : RelationFact :=
  .tensorEq .sm 673 .pm 673

private def authority_transition_eq_sm_674_pm_674 : RelationFact :=
  .tensorEq .sm 674 .pm 674

private def authority_transition_eq_sm_680_pm_680 : RelationFact :=
  .tensorEq .sm 680 .pm 680

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

private def authority_transition_shape_pm_664 : RelationFact :=
  .tensorShape .pm 664 [32]

private def authority_transition_shape_pm_665 : RelationFact :=
  .tensorShape .pm 665 [32]

private def authority_transition_shape_pm_673 : RelationFact :=
  .tensorShape .pm 673 [32]

private def authority_transition_shape_pm_674 : RelationFact :=
  .tensorShape .pm 674 [32]

private def authority_transition_shape_pm_680 : RelationFact :=
  .tensorShape .pm 680 [32, 32]

private def authority_transition_shape_pm_714 : RelationFact :=
  .tensorShape .pm 714 [1, 8]

private def anchor_sm_shape_563 : RelationFact :=
  .tensorShape .sm 563 [128, 32]

private def state_000223 : RelationState where
  facts := [anchor_sm_shape_563, authority_transition_eq_sm_565_pm_565, authority_transition_eq_sm_568_pm_568, authority_transition_eq_sm_569_pm_569, authority_transition_eq_sm_571_pm_571, authority_transition_eq_sm_573_pm_573, authority_transition_eq_sm_594_pm_594, authority_transition_eq_sm_595_pm_595, authority_transition_eq_sm_600_pm_600, authority_transition_eq_sm_603_pm_603, authority_transition_eq_sm_604_pm_604, authority_transition_eq_sm_608_pm_608, authority_transition_eq_sm_626_pm_626, authority_transition_eq_sm_629_pm_629, authority_transition_eq_sm_630_pm_630, authority_transition_eq_sm_638_pm_638, authority_transition_eq_sm_639_pm_639, authority_transition_eq_sm_645_pm_645, authority_transition_eq_sm_664_pm_664, authority_transition_eq_sm_665_pm_665, authority_transition_eq_sm_673_pm_673, authority_transition_eq_sm_674_pm_674, authority_transition_eq_sm_680_pm_680, authority_transition_eq_sm_714_pm_714, authority_transition_eq_sm_716_pm_716, authority_transition_shape_pm_565, authority_transition_shape_pm_568, authority_transition_shape_pm_569, authority_transition_shape_pm_571, authority_transition_shape_pm_573, authority_transition_shape_pm_594, authority_transition_shape_pm_595, authority_transition_shape_pm_600, authority_transition_shape_pm_603, authority_transition_shape_pm_604, authority_transition_shape_pm_608, authority_transition_shape_pm_626, authority_transition_shape_pm_629, authority_transition_shape_pm_630, authority_transition_shape_pm_638, authority_transition_shape_pm_639, authority_transition_shape_pm_645, authority_transition_shape_pm_664, authority_transition_shape_pm_665, authority_transition_shape_pm_673, authority_transition_shape_pm_674, authority_transition_shape_pm_680, authority_transition_shape_pm_714, fact_000044, fact_000064, fact_000066, fact_000076, fact_000077, fact_000078, fact_000079, fact_000080, fact_000088, fact_000128, fact_000129, fact_000130, fact_000131, fact_000132, fact_000133, fact_000134, fact_000135, fact_000136, fact_000137, fact_000138, fact_000139, fact_000140, fact_000141, fact_000142, fact_000143, fact_000144, fact_000145, fact_000146, fact_000147, fact_000148, fact_000149, fact_000150, fact_000151, fact_000152, fact_000153, fact_000154, fact_000155, fact_000156, fact_000157, fact_000158, fact_000159, fact_000160, fact_000161, fact_000162, fact_000163, fact_000172, fact_000173, fact_000212, fact_000216, fact_000228, fact_000229, fact_000249, fact_000265, fact_000298, fact_000384, fact_000387, fact_000388, fact_000390, fact_000392, fact_000394, fact_000398, fact_000399, fact_000402, fact_000403, fact_000405, fact_000411, fact_000412, fact_000414, fact_000418, fact_000420, fact_000423, fact_000425, fact_000431, fact_000433, fact_000436, fact_000438, fact_000441, fact_000444, fact_000446, fact_000447, fact_000448, fact_000449, fact_000454, fact_000462, fact_000467, fact_000470, fact_000472, fact_000478, fact_000479, fact_000482, fact_000483, fact_000485, fact_000486, fact_000488, fact_000489, fact_000491, fact_000495, fact_000497, fact_000498, fact_000504, fact_000510]
  nonempty := by decide

private def state_000224 : RelationState where
  facts := [anchor_sm_shape_563, authority_transition_eq_sm_565_pm_565, authority_transition_eq_sm_568_pm_568, authority_transition_eq_sm_569_pm_569, authority_transition_eq_sm_571_pm_571, authority_transition_eq_sm_573_pm_573, authority_transition_eq_sm_594_pm_594, authority_transition_eq_sm_595_pm_595, authority_transition_eq_sm_600_pm_600, authority_transition_eq_sm_603_pm_603, authority_transition_eq_sm_604_pm_604, authority_transition_eq_sm_608_pm_608, authority_transition_eq_sm_626_pm_626, authority_transition_eq_sm_629_pm_629, authority_transition_eq_sm_630_pm_630, authority_transition_eq_sm_638_pm_638, authority_transition_eq_sm_639_pm_639, authority_transition_eq_sm_645_pm_645, authority_transition_eq_sm_664_pm_664, authority_transition_eq_sm_665_pm_665, authority_transition_eq_sm_673_pm_673, authority_transition_eq_sm_674_pm_674, authority_transition_eq_sm_714_pm_714, authority_transition_eq_sm_716_pm_716, authority_transition_shape_pm_565, authority_transition_shape_pm_568, authority_transition_shape_pm_569, authority_transition_shape_pm_571, authority_transition_shape_pm_573, authority_transition_shape_pm_594, authority_transition_shape_pm_595, authority_transition_shape_pm_600, authority_transition_shape_pm_603, authority_transition_shape_pm_604, authority_transition_shape_pm_608, authority_transition_shape_pm_626, authority_transition_shape_pm_629, authority_transition_shape_pm_630, authority_transition_shape_pm_638, authority_transition_shape_pm_639, authority_transition_shape_pm_645, authority_transition_shape_pm_664, authority_transition_shape_pm_665, authority_transition_shape_pm_673, authority_transition_shape_pm_674, authority_transition_shape_pm_714, fact_000044, fact_000064, fact_000066, fact_000076, fact_000077, fact_000078, fact_000079, fact_000080, fact_000088, fact_000128, fact_000129, fact_000130, fact_000131, fact_000132, fact_000133, fact_000134, fact_000135, fact_000136, fact_000137, fact_000138, fact_000139, fact_000140, fact_000141, fact_000142, fact_000143, fact_000144, fact_000145, fact_000146, fact_000147, fact_000148, fact_000149, fact_000150, fact_000151, fact_000152, fact_000153, fact_000154, fact_000155, fact_000156, fact_000157, fact_000158, fact_000159, fact_000160, fact_000161, fact_000162, fact_000172, fact_000173, fact_000212, fact_000216, fact_000230, fact_000231, fact_000233, fact_000249, fact_000265, fact_000298, fact_000384, fact_000387, fact_000388, fact_000390, fact_000392, fact_000394, fact_000398, fact_000399, fact_000402, fact_000403, fact_000405, fact_000411, fact_000412, fact_000414, fact_000418, fact_000420, fact_000423, fact_000425, fact_000431, fact_000433, fact_000436, fact_000438, fact_000441, fact_000444, fact_000446, fact_000447, fact_000448, fact_000449, fact_000454, fact_000462, fact_000467, fact_000470, fact_000472, fact_000478, fact_000479, fact_000482, fact_000483, fact_000485, fact_000486, fact_000488, fact_000489, fact_000491, fact_000495, fact_000497, test_dw_fact]
  nonempty := by decide

end
end TrainVerify.Denote.SequenceDwMixedsegment_000223

namespace TrainVerify.Denote.SequenceDwMixedsegment_000223
set_option maxHeartbeats 500000
noncomputable section
private def segment_000223_sm_nodes:List NodeDecl:=[{ rank := 0, op := "OpName.BW_matmul", ins := [870, 683, 688], outs := [864, 869] }, { rank := 0, op := "OpName.BW_linear", ins := [862, 1055, 680], outs := [1056, 861] }]
private def segment_000223_pm_nodes:List NodeDecl:=[{ rank := 0, op := "OpName.BW_linear", ins := [2887, 2869, 680], outs := [2885, 2886] }, { rank := 1, op := "OpName.BW_linear", ins := [2890, 2870, 680], outs := [2888, 2889] }, { rank := 2, op := "OpName.BW_linear", ins := [2893, 2871, 680], outs := [2891, 2892] }, { rank := 3, op := "OpName.BW_linear", ins := [2896, 2872, 680], outs := [2894, 2895] }, { rank := 0, op := "OpName.BW_matmul", ins := [3010, 2901, 2993], outs := [2914, 3009] }, { rank := 1, op := "OpName.BW_matmul", ins := [3012, 2902, 2994], outs := [2916, 3011] }, { rank := 2, op := "OpName.BW_matmul", ins := [3014, 2903, 2995], outs := [2918, 3013] }, { rank := 3, op := "OpName.BW_matmul", ins := [3016, 2904, 2996], outs := [2920, 3015] }]
@[irreducible] private def segment_000223_sm_final(z:Store):Store:=segment_000223_sm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) z
@[irreducible] private def segment_000223_pm_final(z:Store):Store:=segment_000223_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) z

private theorem segment_000223_hLinearSm(smStore:Store):(segment_000223_sm_final smStore) 1056=(bw_linear ((segment_000223_sm_final smStore) 862) ((segment_000223_sm_final smStore) 1055) ((segment_000223_sm_final smStore) 680)).1:=by
  have hfinal:(segment_000223_sm_final smStore)=segment_000223_sm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore:=by unfold segment_000223_sm_final;rfl
  have hout_nodes : segment_000223_sm_nodes = (segment_000223_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [862, 1055, 680], outs := [1056, 861] }] ++ (segment_000223_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000223_sm_final smStore) 1056 = (bw_linear (((segment_000223_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 862) (((segment_000223_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 1055) (((segment_000223_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 680)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.sm smStore
      (segment_000223_sm_nodes.take 1) (segment_000223_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_linear", ins := [862, 1055, 680], outs := [1056, 861] } 1056
      (fun t => (bw_linear (t 862) (t 1055) (t 680)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out TrainVerify.Denote.Generated.sm t 0 862 1055 680 1056 861 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000223_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 862 = (segment_000223_sm_final smStore) 862 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000223_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_linear", ins := [862, 1055, 680], outs := [1056, 861] } :: (segment_000223_sm_nodes.drop 2)) 862
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000223_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 1055 = (segment_000223_sm_final smStore) 1055 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000223_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_linear", ins := [862, 1055, 680], outs := [1056, 861] } :: (segment_000223_sm_nodes.drop 2)) 1055
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000223_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 680 = (segment_000223_sm_final smStore) 680 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000223_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_linear", ins := [862, 1055, 680], outs := [1056, 861] } :: (segment_000223_sm_nodes.drop 2)) 680
      (by native_decide) (by native_decide)
  have hout : (segment_000223_sm_final smStore) 1056 = (bw_linear ((segment_000223_sm_final smStore) 862) ((segment_000223_sm_final smStore) 1055) ((segment_000223_sm_final smStore) 680)).1 := by
    calc
      _ = (bw_linear (((segment_000223_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 862) (((segment_000223_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 1055) (((segment_000223_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 680)).1 := hout_prefix
      _ = (bw_linear ((segment_000223_sm_final smStore) 862) ((segment_000223_sm_final smStore) 1055) ((segment_000223_sm_final smStore) 680)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000223_hLinearPm0(pmStore:Store):(segment_000223_pm_final pmStore) 2885=(bw_linear ((segment_000223_pm_final pmStore) 2887) ((segment_000223_pm_final pmStore) 2869) ((segment_000223_pm_final pmStore) 680)).1:=by
  have hfinal:(segment_000223_pm_final pmStore)=segment_000223_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000223_pm_final;rfl
  have hout_nodes : segment_000223_pm_nodes = (segment_000223_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [2887, 2869, 680], outs := [2885, 2886] }] ++ (segment_000223_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000223_pm_final pmStore) 2885 = (bw_linear (((segment_000223_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2887) (((segment_000223_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2869) (((segment_000223_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 680)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 0) (segment_000223_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [2887, 2869, 680], outs := [2885, 2886] } 2885
      (fun t => (bw_linear (t 2887) (t 2869) (t 680)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out TrainVerify.Denote.Generated.pm t 0 2887 2869 680 2885 2886 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000223_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2887 = (segment_000223_pm_final pmStore) 2887 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [2887, 2869, 680], outs := [2885, 2886] } :: (segment_000223_pm_nodes.drop 1)) 2887
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000223_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2869 = (segment_000223_pm_final pmStore) 2869 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [2887, 2869, 680], outs := [2885, 2886] } :: (segment_000223_pm_nodes.drop 1)) 2869
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000223_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 680 = (segment_000223_pm_final pmStore) 680 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [2887, 2869, 680], outs := [2885, 2886] } :: (segment_000223_pm_nodes.drop 1)) 680
      (by native_decide) (by native_decide)
  have hout : (segment_000223_pm_final pmStore) 2885 = (bw_linear ((segment_000223_pm_final pmStore) 2887) ((segment_000223_pm_final pmStore) 2869) ((segment_000223_pm_final pmStore) 680)).1 := by
    calc
      _ = (bw_linear (((segment_000223_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2887) (((segment_000223_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2869) (((segment_000223_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 680)).1 := hout_prefix
      _ = (bw_linear ((segment_000223_pm_final pmStore) 2887) ((segment_000223_pm_final pmStore) 2869) ((segment_000223_pm_final pmStore) 680)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000223_hLinearPm1(pmStore:Store):(segment_000223_pm_final pmStore) 2888=(bw_linear ((segment_000223_pm_final pmStore) 2890) ((segment_000223_pm_final pmStore) 2870) ((segment_000223_pm_final pmStore) 680)).1:=by
  have hfinal:(segment_000223_pm_final pmStore)=segment_000223_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000223_pm_final;rfl
  have hout_nodes : segment_000223_pm_nodes = (segment_000223_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_linear", ins := [2890, 2870, 680], outs := [2888, 2889] }] ++ (segment_000223_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000223_pm_final pmStore) 2888 = (bw_linear (((segment_000223_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2890) (((segment_000223_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2870) (((segment_000223_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 680)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 1) (segment_000223_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_linear", ins := [2890, 2870, 680], outs := [2888, 2889] } 2888
      (fun t => (bw_linear (t 2890) (t 2870) (t 680)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out TrainVerify.Denote.Generated.pm t 1 2890 2870 680 2888 2889 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000223_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2890 = (segment_000223_pm_final pmStore) 2890 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [2890, 2870, 680], outs := [2888, 2889] } :: (segment_000223_pm_nodes.drop 2)) 2890
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000223_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2870 = (segment_000223_pm_final pmStore) 2870 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [2890, 2870, 680], outs := [2888, 2889] } :: (segment_000223_pm_nodes.drop 2)) 2870
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000223_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 680 = (segment_000223_pm_final pmStore) 680 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [2890, 2870, 680], outs := [2888, 2889] } :: (segment_000223_pm_nodes.drop 2)) 680
      (by native_decide) (by native_decide)
  have hout : (segment_000223_pm_final pmStore) 2888 = (bw_linear ((segment_000223_pm_final pmStore) 2890) ((segment_000223_pm_final pmStore) 2870) ((segment_000223_pm_final pmStore) 680)).1 := by
    calc
      _ = (bw_linear (((segment_000223_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2890) (((segment_000223_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2870) (((segment_000223_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 680)).1 := hout_prefix
      _ = (bw_linear ((segment_000223_pm_final pmStore) 2890) ((segment_000223_pm_final pmStore) 2870) ((segment_000223_pm_final pmStore) 680)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000223_hLinearPm2(pmStore:Store):(segment_000223_pm_final pmStore) 2891=(bw_linear ((segment_000223_pm_final pmStore) 2893) ((segment_000223_pm_final pmStore) 2871) ((segment_000223_pm_final pmStore) 680)).1:=by
  have hfinal:(segment_000223_pm_final pmStore)=segment_000223_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000223_pm_final;rfl
  have hout_nodes : segment_000223_pm_nodes = (segment_000223_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_linear", ins := [2893, 2871, 680], outs := [2891, 2892] }] ++ (segment_000223_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000223_pm_final pmStore) 2891 = (bw_linear (((segment_000223_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2893) (((segment_000223_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2871) (((segment_000223_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 680)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 2) (segment_000223_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_linear", ins := [2893, 2871, 680], outs := [2891, 2892] } 2891
      (fun t => (bw_linear (t 2893) (t 2871) (t 680)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out TrainVerify.Denote.Generated.pm t 2 2893 2871 680 2891 2892 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000223_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2893 = (segment_000223_pm_final pmStore) 2893 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [2893, 2871, 680], outs := [2891, 2892] } :: (segment_000223_pm_nodes.drop 3)) 2893
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000223_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2871 = (segment_000223_pm_final pmStore) 2871 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [2893, 2871, 680], outs := [2891, 2892] } :: (segment_000223_pm_nodes.drop 3)) 2871
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000223_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 680 = (segment_000223_pm_final pmStore) 680 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [2893, 2871, 680], outs := [2891, 2892] } :: (segment_000223_pm_nodes.drop 3)) 680
      (by native_decide) (by native_decide)
  have hout : (segment_000223_pm_final pmStore) 2891 = (bw_linear ((segment_000223_pm_final pmStore) 2893) ((segment_000223_pm_final pmStore) 2871) ((segment_000223_pm_final pmStore) 680)).1 := by
    calc
      _ = (bw_linear (((segment_000223_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2893) (((segment_000223_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2871) (((segment_000223_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 680)).1 := hout_prefix
      _ = (bw_linear ((segment_000223_pm_final pmStore) 2893) ((segment_000223_pm_final pmStore) 2871) ((segment_000223_pm_final pmStore) 680)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000223_hLinearPm3(pmStore:Store):(segment_000223_pm_final pmStore) 2894=(bw_linear ((segment_000223_pm_final pmStore) 2896) ((segment_000223_pm_final pmStore) 2872) ((segment_000223_pm_final pmStore) 680)).1:=by
  have hfinal:(segment_000223_pm_final pmStore)=segment_000223_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000223_pm_final;rfl
  have hout_nodes : segment_000223_pm_nodes = (segment_000223_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_linear", ins := [2896, 2872, 680], outs := [2894, 2895] }] ++ (segment_000223_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000223_pm_final pmStore) 2894 = (bw_linear (((segment_000223_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2896) (((segment_000223_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2872) (((segment_000223_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 680)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 3) (segment_000223_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_linear", ins := [2896, 2872, 680], outs := [2894, 2895] } 2894
      (fun t => (bw_linear (t 2896) (t 2872) (t 680)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out TrainVerify.Denote.Generated.pm t 3 2896 2872 680 2894 2895 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000223_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2896 = (segment_000223_pm_final pmStore) 2896 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [2896, 2872, 680], outs := [2894, 2895] } :: (segment_000223_pm_nodes.drop 4)) 2896
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000223_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2872 = (segment_000223_pm_final pmStore) 2872 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [2896, 2872, 680], outs := [2894, 2895] } :: (segment_000223_pm_nodes.drop 4)) 2872
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000223_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 680 = (segment_000223_pm_final pmStore) 680 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [2896, 2872, 680], outs := [2894, 2895] } :: (segment_000223_pm_nodes.drop 4)) 680
      (by native_decide) (by native_decide)
  have hout : (segment_000223_pm_final pmStore) 2894 = (bw_linear ((segment_000223_pm_final pmStore) 2896) ((segment_000223_pm_final pmStore) 2872) ((segment_000223_pm_final pmStore) 680)).1 := by
    calc
      _ = (bw_linear (((segment_000223_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2896) (((segment_000223_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2872) (((segment_000223_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 680)).1 := hout_prefix
      _ = (bw_linear ((segment_000223_pm_final pmStore) 2896) ((segment_000223_pm_final pmStore) 2872) ((segment_000223_pm_final pmStore) 680)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000223_hLinearDwSm(smStore:Store):(segment_000223_sm_final smStore) 861=(bw_linear ((segment_000223_sm_final smStore) 862) ((segment_000223_sm_final smStore) 1055) ((segment_000223_sm_final smStore) 680)).2:=by
  have hfinal:(segment_000223_sm_final smStore)=segment_000223_sm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore:=by unfold segment_000223_sm_final;rfl
  have hout_nodes : segment_000223_sm_nodes = (segment_000223_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [862, 1055, 680], outs := [1056, 861] }] ++ (segment_000223_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000223_sm_final smStore) 861 = (bw_linear (((segment_000223_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 862) (((segment_000223_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 1055) (((segment_000223_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 680)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.sm smStore
      (segment_000223_sm_nodes.take 1) (segment_000223_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_linear", ins := [862, 1055, 680], outs := [1056, 861] } 861
      (fun t => (bw_linear (t 862) (t 1055) (t 680)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out TrainVerify.Denote.Generated.sm t 0 862 1055 680 1056 861 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000223_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 862 = (segment_000223_sm_final smStore) 862 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000223_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_linear", ins := [862, 1055, 680], outs := [1056, 861] } :: (segment_000223_sm_nodes.drop 2)) 862
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000223_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 1055 = (segment_000223_sm_final smStore) 1055 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000223_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_linear", ins := [862, 1055, 680], outs := [1056, 861] } :: (segment_000223_sm_nodes.drop 2)) 1055
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000223_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 680 = (segment_000223_sm_final smStore) 680 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000223_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_linear", ins := [862, 1055, 680], outs := [1056, 861] } :: (segment_000223_sm_nodes.drop 2)) 680
      (by native_decide) (by native_decide)
  have hout : (segment_000223_sm_final smStore) 861 = (bw_linear ((segment_000223_sm_final smStore) 862) ((segment_000223_sm_final smStore) 1055) ((segment_000223_sm_final smStore) 680)).2 := by
    calc
      _ = (bw_linear (((segment_000223_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 862) (((segment_000223_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 1055) (((segment_000223_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 680)).2 := hout_prefix
      _ = (bw_linear ((segment_000223_sm_final smStore) 862) ((segment_000223_sm_final smStore) 1055) ((segment_000223_sm_final smStore) 680)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000223_hLinearDwPm0(pmStore:Store):(segment_000223_pm_final pmStore) 2886=(bw_linear ((segment_000223_pm_final pmStore) 2887) ((segment_000223_pm_final pmStore) 2869) ((segment_000223_pm_final pmStore) 680)).2:=by
  have hfinal:(segment_000223_pm_final pmStore)=segment_000223_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000223_pm_final;rfl
  have hout_nodes : segment_000223_pm_nodes = (segment_000223_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [2887, 2869, 680], outs := [2885, 2886] }] ++ (segment_000223_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000223_pm_final pmStore) 2886 = (bw_linear (((segment_000223_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2887) (((segment_000223_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2869) (((segment_000223_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 680)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 0) (segment_000223_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [2887, 2869, 680], outs := [2885, 2886] } 2886
      (fun t => (bw_linear (t 2887) (t 2869) (t 680)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out TrainVerify.Denote.Generated.pm t 0 2887 2869 680 2885 2886 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000223_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2887 = (segment_000223_pm_final pmStore) 2887 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [2887, 2869, 680], outs := [2885, 2886] } :: (segment_000223_pm_nodes.drop 1)) 2887
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000223_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2869 = (segment_000223_pm_final pmStore) 2869 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [2887, 2869, 680], outs := [2885, 2886] } :: (segment_000223_pm_nodes.drop 1)) 2869
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000223_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 680 = (segment_000223_pm_final pmStore) 680 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [2887, 2869, 680], outs := [2885, 2886] } :: (segment_000223_pm_nodes.drop 1)) 680
      (by native_decide) (by native_decide)
  have hout : (segment_000223_pm_final pmStore) 2886 = (bw_linear ((segment_000223_pm_final pmStore) 2887) ((segment_000223_pm_final pmStore) 2869) ((segment_000223_pm_final pmStore) 680)).2 := by
    calc
      _ = (bw_linear (((segment_000223_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2887) (((segment_000223_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2869) (((segment_000223_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 680)).2 := hout_prefix
      _ = (bw_linear ((segment_000223_pm_final pmStore) 2887) ((segment_000223_pm_final pmStore) 2869) ((segment_000223_pm_final pmStore) 680)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000223_hLinearDwPm1(pmStore:Store):(segment_000223_pm_final pmStore) 2889=(bw_linear ((segment_000223_pm_final pmStore) 2890) ((segment_000223_pm_final pmStore) 2870) ((segment_000223_pm_final pmStore) 680)).2:=by
  have hfinal:(segment_000223_pm_final pmStore)=segment_000223_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000223_pm_final;rfl
  have hout_nodes : segment_000223_pm_nodes = (segment_000223_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_linear", ins := [2890, 2870, 680], outs := [2888, 2889] }] ++ (segment_000223_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000223_pm_final pmStore) 2889 = (bw_linear (((segment_000223_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2890) (((segment_000223_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2870) (((segment_000223_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 680)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 1) (segment_000223_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_linear", ins := [2890, 2870, 680], outs := [2888, 2889] } 2889
      (fun t => (bw_linear (t 2890) (t 2870) (t 680)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out TrainVerify.Denote.Generated.pm t 1 2890 2870 680 2888 2889 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000223_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2890 = (segment_000223_pm_final pmStore) 2890 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [2890, 2870, 680], outs := [2888, 2889] } :: (segment_000223_pm_nodes.drop 2)) 2890
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000223_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2870 = (segment_000223_pm_final pmStore) 2870 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [2890, 2870, 680], outs := [2888, 2889] } :: (segment_000223_pm_nodes.drop 2)) 2870
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000223_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 680 = (segment_000223_pm_final pmStore) 680 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [2890, 2870, 680], outs := [2888, 2889] } :: (segment_000223_pm_nodes.drop 2)) 680
      (by native_decide) (by native_decide)
  have hout : (segment_000223_pm_final pmStore) 2889 = (bw_linear ((segment_000223_pm_final pmStore) 2890) ((segment_000223_pm_final pmStore) 2870) ((segment_000223_pm_final pmStore) 680)).2 := by
    calc
      _ = (bw_linear (((segment_000223_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2890) (((segment_000223_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2870) (((segment_000223_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 680)).2 := hout_prefix
      _ = (bw_linear ((segment_000223_pm_final pmStore) 2890) ((segment_000223_pm_final pmStore) 2870) ((segment_000223_pm_final pmStore) 680)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000223_hLinearDwPm2(pmStore:Store):(segment_000223_pm_final pmStore) 2892=(bw_linear ((segment_000223_pm_final pmStore) 2893) ((segment_000223_pm_final pmStore) 2871) ((segment_000223_pm_final pmStore) 680)).2:=by
  have hfinal:(segment_000223_pm_final pmStore)=segment_000223_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000223_pm_final;rfl
  have hout_nodes : segment_000223_pm_nodes = (segment_000223_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_linear", ins := [2893, 2871, 680], outs := [2891, 2892] }] ++ (segment_000223_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000223_pm_final pmStore) 2892 = (bw_linear (((segment_000223_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2893) (((segment_000223_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2871) (((segment_000223_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 680)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 2) (segment_000223_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_linear", ins := [2893, 2871, 680], outs := [2891, 2892] } 2892
      (fun t => (bw_linear (t 2893) (t 2871) (t 680)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out TrainVerify.Denote.Generated.pm t 2 2893 2871 680 2891 2892 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000223_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2893 = (segment_000223_pm_final pmStore) 2893 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [2893, 2871, 680], outs := [2891, 2892] } :: (segment_000223_pm_nodes.drop 3)) 2893
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000223_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2871 = (segment_000223_pm_final pmStore) 2871 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [2893, 2871, 680], outs := [2891, 2892] } :: (segment_000223_pm_nodes.drop 3)) 2871
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000223_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 680 = (segment_000223_pm_final pmStore) 680 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [2893, 2871, 680], outs := [2891, 2892] } :: (segment_000223_pm_nodes.drop 3)) 680
      (by native_decide) (by native_decide)
  have hout : (segment_000223_pm_final pmStore) 2892 = (bw_linear ((segment_000223_pm_final pmStore) 2893) ((segment_000223_pm_final pmStore) 2871) ((segment_000223_pm_final pmStore) 680)).2 := by
    calc
      _ = (bw_linear (((segment_000223_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2893) (((segment_000223_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2871) (((segment_000223_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 680)).2 := hout_prefix
      _ = (bw_linear ((segment_000223_pm_final pmStore) 2893) ((segment_000223_pm_final pmStore) 2871) ((segment_000223_pm_final pmStore) 680)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000223_hLinearDwPm3(pmStore:Store):(segment_000223_pm_final pmStore) 2895=(bw_linear ((segment_000223_pm_final pmStore) 2896) ((segment_000223_pm_final pmStore) 2872) ((segment_000223_pm_final pmStore) 680)).2:=by
  have hfinal:(segment_000223_pm_final pmStore)=segment_000223_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000223_pm_final;rfl
  have hout_nodes : segment_000223_pm_nodes = (segment_000223_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_linear", ins := [2896, 2872, 680], outs := [2894, 2895] }] ++ (segment_000223_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000223_pm_final pmStore) 2895 = (bw_linear (((segment_000223_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2896) (((segment_000223_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2872) (((segment_000223_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 680)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 3) (segment_000223_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_linear", ins := [2896, 2872, 680], outs := [2894, 2895] } 2895
      (fun t => (bw_linear (t 2896) (t 2872) (t 680)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out TrainVerify.Denote.Generated.pm t 3 2896 2872 680 2894 2895 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000223_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2896 = (segment_000223_pm_final pmStore) 2896 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [2896, 2872, 680], outs := [2894, 2895] } :: (segment_000223_pm_nodes.drop 4)) 2896
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000223_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2872 = (segment_000223_pm_final pmStore) 2872 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [2896, 2872, 680], outs := [2894, 2895] } :: (segment_000223_pm_nodes.drop 4)) 2872
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000223_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 680 = (segment_000223_pm_final pmStore) 680 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [2896, 2872, 680], outs := [2894, 2895] } :: (segment_000223_pm_nodes.drop 4)) 680
      (by native_decide) (by native_decide)
  have hout : (segment_000223_pm_final pmStore) 2895 = (bw_linear ((segment_000223_pm_final pmStore) 2896) ((segment_000223_pm_final pmStore) 2872) ((segment_000223_pm_final pmStore) 680)).2 := by
    calc
      _ = (bw_linear (((segment_000223_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2896) (((segment_000223_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2872) (((segment_000223_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 680)).2 := hout_prefix
      _ = (bw_linear ((segment_000223_pm_final pmStore) 2896) ((segment_000223_pm_final pmStore) 2872) ((segment_000223_pm_final pmStore) 680)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000223_hMatmulSm0(smStore:Store):(segment_000223_sm_final smStore) 864=(bw_matmul ((segment_000223_sm_final smStore) 870) ((segment_000223_sm_final smStore) 683) ((segment_000223_sm_final smStore) 688)).1:=by
  have hfinal:(segment_000223_sm_final smStore)=segment_000223_sm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore:=by unfold segment_000223_sm_final;rfl
  have hout_nodes : segment_000223_sm_nodes = (segment_000223_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [870, 683, 688], outs := [864, 869] }] ++ (segment_000223_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000223_sm_final smStore) 864 = (bw_matmul (((segment_000223_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 870) (((segment_000223_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 683) (((segment_000223_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 688)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.sm smStore
      (segment_000223_sm_nodes.take 0) (segment_000223_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [870, 683, 688], outs := [864, 869] } 864
      (fun t => (bw_matmul (t 870) (t 683) (t 688)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out TrainVerify.Denote.Generated.sm t 0 870 683 688 864 869 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000223_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 870 = (segment_000223_sm_final smStore) 870 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000223_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [870, 683, 688], outs := [864, 869] } :: (segment_000223_sm_nodes.drop 1)) 870
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000223_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 683 = (segment_000223_sm_final smStore) 683 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000223_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [870, 683, 688], outs := [864, 869] } :: (segment_000223_sm_nodes.drop 1)) 683
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000223_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 688 = (segment_000223_sm_final smStore) 688 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000223_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [870, 683, 688], outs := [864, 869] } :: (segment_000223_sm_nodes.drop 1)) 688
      (by native_decide) (by native_decide)
  have hout : (segment_000223_sm_final smStore) 864 = (bw_matmul ((segment_000223_sm_final smStore) 870) ((segment_000223_sm_final smStore) 683) ((segment_000223_sm_final smStore) 688)).1 := by
    calc
      _ = (bw_matmul (((segment_000223_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 870) (((segment_000223_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 683) (((segment_000223_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 688)).1 := hout_prefix
      _ = (bw_matmul ((segment_000223_sm_final smStore) 870) ((segment_000223_sm_final smStore) 683) ((segment_000223_sm_final smStore) 688)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000223_hMatmulSm1(smStore:Store):(segment_000223_sm_final smStore) 869=(bw_matmul ((segment_000223_sm_final smStore) 870) ((segment_000223_sm_final smStore) 683) ((segment_000223_sm_final smStore) 688)).2:=by
  have hfinal:(segment_000223_sm_final smStore)=segment_000223_sm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore:=by unfold segment_000223_sm_final;rfl
  have hout_nodes : segment_000223_sm_nodes = (segment_000223_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [870, 683, 688], outs := [864, 869] }] ++ (segment_000223_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000223_sm_final smStore) 869 = (bw_matmul (((segment_000223_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 870) (((segment_000223_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 683) (((segment_000223_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 688)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.sm smStore
      (segment_000223_sm_nodes.take 0) (segment_000223_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [870, 683, 688], outs := [864, 869] } 869
      (fun t => (bw_matmul (t 870) (t 683) (t 688)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out TrainVerify.Denote.Generated.sm t 0 870 683 688 864 869 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000223_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 870 = (segment_000223_sm_final smStore) 870 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000223_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [870, 683, 688], outs := [864, 869] } :: (segment_000223_sm_nodes.drop 1)) 870
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000223_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 683 = (segment_000223_sm_final smStore) 683 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000223_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [870, 683, 688], outs := [864, 869] } :: (segment_000223_sm_nodes.drop 1)) 683
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000223_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 688 = (segment_000223_sm_final smStore) 688 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000223_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [870, 683, 688], outs := [864, 869] } :: (segment_000223_sm_nodes.drop 1)) 688
      (by native_decide) (by native_decide)
  have hout : (segment_000223_sm_final smStore) 869 = (bw_matmul ((segment_000223_sm_final smStore) 870) ((segment_000223_sm_final smStore) 683) ((segment_000223_sm_final smStore) 688)).2 := by
    calc
      _ = (bw_matmul (((segment_000223_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 870) (((segment_000223_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 683) (((segment_000223_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 688)).2 := hout_prefix
      _ = (bw_matmul ((segment_000223_sm_final smStore) 870) ((segment_000223_sm_final smStore) 683) ((segment_000223_sm_final smStore) 688)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000223_hMatmulPm0_0(pmStore:Store):(segment_000223_pm_final pmStore) 2914=(bw_matmul ((segment_000223_pm_final pmStore) 3010) ((segment_000223_pm_final pmStore) 2901) ((segment_000223_pm_final pmStore) 2993)).1:=by
  have hfinal:(segment_000223_pm_final pmStore)=segment_000223_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000223_pm_final;rfl
  have hout_nodes : segment_000223_pm_nodes = (segment_000223_pm_nodes.take 4) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [3010, 2901, 2993], outs := [2914, 3009] }] ++ (segment_000223_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000223_pm_final pmStore) 2914 = (bw_matmul (((segment_000223_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 3010) (((segment_000223_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2901) (((segment_000223_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2993)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 4) (segment_000223_pm_nodes.drop 5)
      { rank := 0, op := "OpName.BW_matmul", ins := [3010, 2901, 2993], outs := [2914, 3009] } 2914
      (fun t => (bw_matmul (t 3010) (t 2901) (t 2993)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out TrainVerify.Denote.Generated.pm t 0 3010 2901 2993 2914 3009 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000223_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 3010 = (segment_000223_pm_final pmStore) 3010 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 4) ({ rank := 0, op := "OpName.BW_matmul", ins := [3010, 2901, 2993], outs := [2914, 3009] } :: (segment_000223_pm_nodes.drop 5)) 3010
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000223_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2901 = (segment_000223_pm_final pmStore) 2901 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 4) ({ rank := 0, op := "OpName.BW_matmul", ins := [3010, 2901, 2993], outs := [2914, 3009] } :: (segment_000223_pm_nodes.drop 5)) 2901
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000223_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2993 = (segment_000223_pm_final pmStore) 2993 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 4) ({ rank := 0, op := "OpName.BW_matmul", ins := [3010, 2901, 2993], outs := [2914, 3009] } :: (segment_000223_pm_nodes.drop 5)) 2993
      (by native_decide) (by native_decide)
  have hout : (segment_000223_pm_final pmStore) 2914 = (bw_matmul ((segment_000223_pm_final pmStore) 3010) ((segment_000223_pm_final pmStore) 2901) ((segment_000223_pm_final pmStore) 2993)).1 := by
    calc
      _ = (bw_matmul (((segment_000223_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 3010) (((segment_000223_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2901) (((segment_000223_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2993)).1 := hout_prefix
      _ = (bw_matmul ((segment_000223_pm_final pmStore) 3010) ((segment_000223_pm_final pmStore) 2901) ((segment_000223_pm_final pmStore) 2993)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000223_hMatmulPm0_1(pmStore:Store):(segment_000223_pm_final pmStore) 2916=(bw_matmul ((segment_000223_pm_final pmStore) 3012) ((segment_000223_pm_final pmStore) 2902) ((segment_000223_pm_final pmStore) 2994)).1:=by
  have hfinal:(segment_000223_pm_final pmStore)=segment_000223_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000223_pm_final;rfl
  have hout_nodes : segment_000223_pm_nodes = (segment_000223_pm_nodes.take 5) ++ [{ rank := 1, op := "OpName.BW_matmul", ins := [3012, 2902, 2994], outs := [2916, 3011] }] ++ (segment_000223_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000223_pm_final pmStore) 2916 = (bw_matmul (((segment_000223_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 3012) (((segment_000223_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2902) (((segment_000223_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2994)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 5) (segment_000223_pm_nodes.drop 6)
      { rank := 1, op := "OpName.BW_matmul", ins := [3012, 2902, 2994], outs := [2916, 3011] } 2916
      (fun t => (bw_matmul (t 3012) (t 2902) (t 2994)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out TrainVerify.Denote.Generated.pm t 1 3012 2902 2994 2916 3011 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000223_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 3012 = (segment_000223_pm_final pmStore) 3012 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 5) ({ rank := 1, op := "OpName.BW_matmul", ins := [3012, 2902, 2994], outs := [2916, 3011] } :: (segment_000223_pm_nodes.drop 6)) 3012
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000223_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2902 = (segment_000223_pm_final pmStore) 2902 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 5) ({ rank := 1, op := "OpName.BW_matmul", ins := [3012, 2902, 2994], outs := [2916, 3011] } :: (segment_000223_pm_nodes.drop 6)) 2902
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000223_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2994 = (segment_000223_pm_final pmStore) 2994 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 5) ({ rank := 1, op := "OpName.BW_matmul", ins := [3012, 2902, 2994], outs := [2916, 3011] } :: (segment_000223_pm_nodes.drop 6)) 2994
      (by native_decide) (by native_decide)
  have hout : (segment_000223_pm_final pmStore) 2916 = (bw_matmul ((segment_000223_pm_final pmStore) 3012) ((segment_000223_pm_final pmStore) 2902) ((segment_000223_pm_final pmStore) 2994)).1 := by
    calc
      _ = (bw_matmul (((segment_000223_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 3012) (((segment_000223_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2902) (((segment_000223_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2994)).1 := hout_prefix
      _ = (bw_matmul ((segment_000223_pm_final pmStore) 3012) ((segment_000223_pm_final pmStore) 2902) ((segment_000223_pm_final pmStore) 2994)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000223_hMatmulPm0_2(pmStore:Store):(segment_000223_pm_final pmStore) 2918=(bw_matmul ((segment_000223_pm_final pmStore) 3014) ((segment_000223_pm_final pmStore) 2903) ((segment_000223_pm_final pmStore) 2995)).1:=by
  have hfinal:(segment_000223_pm_final pmStore)=segment_000223_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000223_pm_final;rfl
  have hout_nodes : segment_000223_pm_nodes = (segment_000223_pm_nodes.take 6) ++ [{ rank := 2, op := "OpName.BW_matmul", ins := [3014, 2903, 2995], outs := [2918, 3013] }] ++ (segment_000223_pm_nodes.drop 7) := by
    native_decide
  have hout_prefix : (segment_000223_pm_final pmStore) 2918 = (bw_matmul (((segment_000223_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 3014) (((segment_000223_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2903) (((segment_000223_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2995)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 6) (segment_000223_pm_nodes.drop 7)
      { rank := 2, op := "OpName.BW_matmul", ins := [3014, 2903, 2995], outs := [2918, 3013] } 2918
      (fun t => (bw_matmul (t 3014) (t 2903) (t 2995)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out TrainVerify.Denote.Generated.pm t 2 3014 2903 2995 2918 3013 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000223_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 3014 = (segment_000223_pm_final pmStore) 3014 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 6) ({ rank := 2, op := "OpName.BW_matmul", ins := [3014, 2903, 2995], outs := [2918, 3013] } :: (segment_000223_pm_nodes.drop 7)) 3014
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000223_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2903 = (segment_000223_pm_final pmStore) 2903 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 6) ({ rank := 2, op := "OpName.BW_matmul", ins := [3014, 2903, 2995], outs := [2918, 3013] } :: (segment_000223_pm_nodes.drop 7)) 2903
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000223_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2995 = (segment_000223_pm_final pmStore) 2995 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 6) ({ rank := 2, op := "OpName.BW_matmul", ins := [3014, 2903, 2995], outs := [2918, 3013] } :: (segment_000223_pm_nodes.drop 7)) 2995
      (by native_decide) (by native_decide)
  have hout : (segment_000223_pm_final pmStore) 2918 = (bw_matmul ((segment_000223_pm_final pmStore) 3014) ((segment_000223_pm_final pmStore) 2903) ((segment_000223_pm_final pmStore) 2995)).1 := by
    calc
      _ = (bw_matmul (((segment_000223_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 3014) (((segment_000223_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2903) (((segment_000223_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2995)).1 := hout_prefix
      _ = (bw_matmul ((segment_000223_pm_final pmStore) 3014) ((segment_000223_pm_final pmStore) 2903) ((segment_000223_pm_final pmStore) 2995)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000223_hMatmulPm0_3(pmStore:Store):(segment_000223_pm_final pmStore) 2920=(bw_matmul ((segment_000223_pm_final pmStore) 3016) ((segment_000223_pm_final pmStore) 2904) ((segment_000223_pm_final pmStore) 2996)).1:=by
  have hfinal:(segment_000223_pm_final pmStore)=segment_000223_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000223_pm_final;rfl
  have hout_nodes : segment_000223_pm_nodes = (segment_000223_pm_nodes.take 7) ++ [{ rank := 3, op := "OpName.BW_matmul", ins := [3016, 2904, 2996], outs := [2920, 3015] }] ++ (segment_000223_pm_nodes.drop 8) := by
    native_decide
  have hout_prefix : (segment_000223_pm_final pmStore) 2920 = (bw_matmul (((segment_000223_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 3016) (((segment_000223_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2904) (((segment_000223_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2996)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 7) (segment_000223_pm_nodes.drop 8)
      { rank := 3, op := "OpName.BW_matmul", ins := [3016, 2904, 2996], outs := [2920, 3015] } 2920
      (fun t => (bw_matmul (t 3016) (t 2904) (t 2996)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out TrainVerify.Denote.Generated.pm t 3 3016 2904 2996 2920 3015 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000223_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 3016 = (segment_000223_pm_final pmStore) 3016 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_matmul", ins := [3016, 2904, 2996], outs := [2920, 3015] } :: (segment_000223_pm_nodes.drop 8)) 3016
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000223_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2904 = (segment_000223_pm_final pmStore) 2904 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_matmul", ins := [3016, 2904, 2996], outs := [2920, 3015] } :: (segment_000223_pm_nodes.drop 8)) 2904
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000223_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2996 = (segment_000223_pm_final pmStore) 2996 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_matmul", ins := [3016, 2904, 2996], outs := [2920, 3015] } :: (segment_000223_pm_nodes.drop 8)) 2996
      (by native_decide) (by native_decide)
  have hout : (segment_000223_pm_final pmStore) 2920 = (bw_matmul ((segment_000223_pm_final pmStore) 3016) ((segment_000223_pm_final pmStore) 2904) ((segment_000223_pm_final pmStore) 2996)).1 := by
    calc
      _ = (bw_matmul (((segment_000223_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 3016) (((segment_000223_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2904) (((segment_000223_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2996)).1 := hout_prefix
      _ = (bw_matmul ((segment_000223_pm_final pmStore) 3016) ((segment_000223_pm_final pmStore) 2904) ((segment_000223_pm_final pmStore) 2996)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000223_hMatmulPm1_0(pmStore:Store):(segment_000223_pm_final pmStore) 3009=(bw_matmul ((segment_000223_pm_final pmStore) 3010) ((segment_000223_pm_final pmStore) 2901) ((segment_000223_pm_final pmStore) 2993)).2:=by
  have hfinal:(segment_000223_pm_final pmStore)=segment_000223_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000223_pm_final;rfl
  have hout_nodes : segment_000223_pm_nodes = (segment_000223_pm_nodes.take 4) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [3010, 2901, 2993], outs := [2914, 3009] }] ++ (segment_000223_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000223_pm_final pmStore) 3009 = (bw_matmul (((segment_000223_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 3010) (((segment_000223_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2901) (((segment_000223_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2993)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 4) (segment_000223_pm_nodes.drop 5)
      { rank := 0, op := "OpName.BW_matmul", ins := [3010, 2901, 2993], outs := [2914, 3009] } 3009
      (fun t => (bw_matmul (t 3010) (t 2901) (t 2993)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out TrainVerify.Denote.Generated.pm t 0 3010 2901 2993 2914 3009 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000223_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 3010 = (segment_000223_pm_final pmStore) 3010 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 4) ({ rank := 0, op := "OpName.BW_matmul", ins := [3010, 2901, 2993], outs := [2914, 3009] } :: (segment_000223_pm_nodes.drop 5)) 3010
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000223_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2901 = (segment_000223_pm_final pmStore) 2901 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 4) ({ rank := 0, op := "OpName.BW_matmul", ins := [3010, 2901, 2993], outs := [2914, 3009] } :: (segment_000223_pm_nodes.drop 5)) 2901
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000223_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2993 = (segment_000223_pm_final pmStore) 2993 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 4) ({ rank := 0, op := "OpName.BW_matmul", ins := [3010, 2901, 2993], outs := [2914, 3009] } :: (segment_000223_pm_nodes.drop 5)) 2993
      (by native_decide) (by native_decide)
  have hout : (segment_000223_pm_final pmStore) 3009 = (bw_matmul ((segment_000223_pm_final pmStore) 3010) ((segment_000223_pm_final pmStore) 2901) ((segment_000223_pm_final pmStore) 2993)).2 := by
    calc
      _ = (bw_matmul (((segment_000223_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 3010) (((segment_000223_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2901) (((segment_000223_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2993)).2 := hout_prefix
      _ = (bw_matmul ((segment_000223_pm_final pmStore) 3010) ((segment_000223_pm_final pmStore) 2901) ((segment_000223_pm_final pmStore) 2993)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000223_hMatmulPm1_1(pmStore:Store):(segment_000223_pm_final pmStore) 3011=(bw_matmul ((segment_000223_pm_final pmStore) 3012) ((segment_000223_pm_final pmStore) 2902) ((segment_000223_pm_final pmStore) 2994)).2:=by
  have hfinal:(segment_000223_pm_final pmStore)=segment_000223_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000223_pm_final;rfl
  have hout_nodes : segment_000223_pm_nodes = (segment_000223_pm_nodes.take 5) ++ [{ rank := 1, op := "OpName.BW_matmul", ins := [3012, 2902, 2994], outs := [2916, 3011] }] ++ (segment_000223_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000223_pm_final pmStore) 3011 = (bw_matmul (((segment_000223_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 3012) (((segment_000223_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2902) (((segment_000223_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2994)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 5) (segment_000223_pm_nodes.drop 6)
      { rank := 1, op := "OpName.BW_matmul", ins := [3012, 2902, 2994], outs := [2916, 3011] } 3011
      (fun t => (bw_matmul (t 3012) (t 2902) (t 2994)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out TrainVerify.Denote.Generated.pm t 1 3012 2902 2994 2916 3011 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000223_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 3012 = (segment_000223_pm_final pmStore) 3012 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 5) ({ rank := 1, op := "OpName.BW_matmul", ins := [3012, 2902, 2994], outs := [2916, 3011] } :: (segment_000223_pm_nodes.drop 6)) 3012
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000223_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2902 = (segment_000223_pm_final pmStore) 2902 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 5) ({ rank := 1, op := "OpName.BW_matmul", ins := [3012, 2902, 2994], outs := [2916, 3011] } :: (segment_000223_pm_nodes.drop 6)) 2902
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000223_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2994 = (segment_000223_pm_final pmStore) 2994 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 5) ({ rank := 1, op := "OpName.BW_matmul", ins := [3012, 2902, 2994], outs := [2916, 3011] } :: (segment_000223_pm_nodes.drop 6)) 2994
      (by native_decide) (by native_decide)
  have hout : (segment_000223_pm_final pmStore) 3011 = (bw_matmul ((segment_000223_pm_final pmStore) 3012) ((segment_000223_pm_final pmStore) 2902) ((segment_000223_pm_final pmStore) 2994)).2 := by
    calc
      _ = (bw_matmul (((segment_000223_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 3012) (((segment_000223_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2902) (((segment_000223_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2994)).2 := hout_prefix
      _ = (bw_matmul ((segment_000223_pm_final pmStore) 3012) ((segment_000223_pm_final pmStore) 2902) ((segment_000223_pm_final pmStore) 2994)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000223_hMatmulPm1_2(pmStore:Store):(segment_000223_pm_final pmStore) 3013=(bw_matmul ((segment_000223_pm_final pmStore) 3014) ((segment_000223_pm_final pmStore) 2903) ((segment_000223_pm_final pmStore) 2995)).2:=by
  have hfinal:(segment_000223_pm_final pmStore)=segment_000223_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000223_pm_final;rfl
  have hout_nodes : segment_000223_pm_nodes = (segment_000223_pm_nodes.take 6) ++ [{ rank := 2, op := "OpName.BW_matmul", ins := [3014, 2903, 2995], outs := [2918, 3013] }] ++ (segment_000223_pm_nodes.drop 7) := by
    native_decide
  have hout_prefix : (segment_000223_pm_final pmStore) 3013 = (bw_matmul (((segment_000223_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 3014) (((segment_000223_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2903) (((segment_000223_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2995)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 6) (segment_000223_pm_nodes.drop 7)
      { rank := 2, op := "OpName.BW_matmul", ins := [3014, 2903, 2995], outs := [2918, 3013] } 3013
      (fun t => (bw_matmul (t 3014) (t 2903) (t 2995)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out TrainVerify.Denote.Generated.pm t 2 3014 2903 2995 2918 3013 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000223_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 3014 = (segment_000223_pm_final pmStore) 3014 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 6) ({ rank := 2, op := "OpName.BW_matmul", ins := [3014, 2903, 2995], outs := [2918, 3013] } :: (segment_000223_pm_nodes.drop 7)) 3014
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000223_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2903 = (segment_000223_pm_final pmStore) 2903 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 6) ({ rank := 2, op := "OpName.BW_matmul", ins := [3014, 2903, 2995], outs := [2918, 3013] } :: (segment_000223_pm_nodes.drop 7)) 2903
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000223_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2995 = (segment_000223_pm_final pmStore) 2995 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 6) ({ rank := 2, op := "OpName.BW_matmul", ins := [3014, 2903, 2995], outs := [2918, 3013] } :: (segment_000223_pm_nodes.drop 7)) 2995
      (by native_decide) (by native_decide)
  have hout : (segment_000223_pm_final pmStore) 3013 = (bw_matmul ((segment_000223_pm_final pmStore) 3014) ((segment_000223_pm_final pmStore) 2903) ((segment_000223_pm_final pmStore) 2995)).2 := by
    calc
      _ = (bw_matmul (((segment_000223_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 3014) (((segment_000223_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2903) (((segment_000223_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2995)).2 := hout_prefix
      _ = (bw_matmul ((segment_000223_pm_final pmStore) 3014) ((segment_000223_pm_final pmStore) 2903) ((segment_000223_pm_final pmStore) 2995)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000223_hMatmulPm1_3(pmStore:Store):(segment_000223_pm_final pmStore) 3015=(bw_matmul ((segment_000223_pm_final pmStore) 3016) ((segment_000223_pm_final pmStore) 2904) ((segment_000223_pm_final pmStore) 2996)).2:=by
  have hfinal:(segment_000223_pm_final pmStore)=segment_000223_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000223_pm_final;rfl
  have hout_nodes : segment_000223_pm_nodes = (segment_000223_pm_nodes.take 7) ++ [{ rank := 3, op := "OpName.BW_matmul", ins := [3016, 2904, 2996], outs := [2920, 3015] }] ++ (segment_000223_pm_nodes.drop 8) := by
    native_decide
  have hout_prefix : (segment_000223_pm_final pmStore) 3015 = (bw_matmul (((segment_000223_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 3016) (((segment_000223_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2904) (((segment_000223_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2996)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 7) (segment_000223_pm_nodes.drop 8)
      { rank := 3, op := "OpName.BW_matmul", ins := [3016, 2904, 2996], outs := [2920, 3015] } 3015
      (fun t => (bw_matmul (t 3016) (t 2904) (t 2996)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out TrainVerify.Denote.Generated.pm t 3 3016 2904 2996 2920 3015 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000223_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 3016 = (segment_000223_pm_final pmStore) 3016 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_matmul", ins := [3016, 2904, 2996], outs := [2920, 3015] } :: (segment_000223_pm_nodes.drop 8)) 3016
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000223_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2904 = (segment_000223_pm_final pmStore) 2904 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_matmul", ins := [3016, 2904, 2996], outs := [2920, 3015] } :: (segment_000223_pm_nodes.drop 8)) 2904
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000223_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2996 = (segment_000223_pm_final pmStore) 2996 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000223_pm_nodes.take 7) ({ rank := 3, op := "OpName.BW_matmul", ins := [3016, 2904, 2996], outs := [2920, 3015] } :: (segment_000223_pm_nodes.drop 8)) 2996
      (by native_decide) (by native_decide)
  have hout : (segment_000223_pm_final pmStore) 3015 = (bw_matmul ((segment_000223_pm_final pmStore) 3016) ((segment_000223_pm_final pmStore) 2904) ((segment_000223_pm_final pmStore) 2996)).2 := by
    calc
      _ = (bw_matmul (((segment_000223_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 3016) (((segment_000223_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2904) (((segment_000223_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 2996)).2 := hout_prefix
      _ = (bw_matmul ((segment_000223_pm_final pmStore) 3016) ((segment_000223_pm_final pmStore) 2904) ((segment_000223_pm_final pmStore) 2996)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000223_sound(smStore pmStore:Store)(hstate:state_000223.Holds smStore pmStore): state_000224.Holds (segment_000223_sm_final smStore) (segment_000223_pm_final pmStore) := by
 let smFinal:=segment_000223_sm_final smStore
 let pmFinal:=segment_000223_pm_final pmStore
 have hframe:state_000223.Holds smFinal pmFinal:=by unfold smFinal pmFinal segment_000223_sm_final segment_000223_pm_final;apply RelationState.Holds.fold_frame segment_000223_sm_nodes segment_000223_pm_nodes smStore pmStore hstate <;> native_decide
 have hlg:fact_000229.Holds smFinal pmFinal:=hframe _ (by native_decide)
 change ShardedRel (smFinal 862) [pmFinal 2887, pmFinal 2890, pmFinal 2893, pmFinal 2896] 1 [1,8,32] [1,2,32] at hlg
 have hlgV:smFinal 862=allGatherPrimDimN 1 4 0 [pmFinal 2887, pmFinal 2890, pmFinal 2893, pmFinal 2896]:=by simpa only [List.length_cons,List.length_nil] using hlg.full_value
 have hlx:fact_000498.Holds smFinal pmFinal:=hframe _ (by native_decide)
 change ShardedRel (smFinal 1055) [pmFinal 2869, pmFinal 2870, pmFinal 2871, pmFinal 2872] 1 [1,8,32] [1,2,32] at hlx
 have hlxV:smFinal 1055=allGatherPrimDimN 1 4 0 [pmFinal 2869, pmFinal 2870, pmFinal 2871, pmFinal 2872]:=by simpa only [List.length_cons,List.length_nil] using hlx.full_value
 have hmg:fact_000228.Holds smFinal pmFinal:=hframe _ (by native_decide)
 change ShardedRel (smFinal 870) [pmFinal 3010, pmFinal 3012, pmFinal 3014, pmFinal 3016] 1 [1,4,8,8] [1,1,8,8] at hmg
 have hmgV:smFinal 870=allGatherPrimDimN 1 4 0 [pmFinal 3010, pmFinal 3012, pmFinal 3014, pmFinal 3016]:=by simpa only [List.length_cons,List.length_nil] using hmg.full_value
 have hmx:fact_000504.Holds smFinal pmFinal:=hframe _ (by native_decide)
 change ShardedRel (smFinal 683) [pmFinal 2901, pmFinal 2902, pmFinal 2903, pmFinal 2904] 1 [1,4,8,8] [1,1,8,8] at hmx
 have hmxV:smFinal 683=allGatherPrimDimN 1 4 0 [pmFinal 2901, pmFinal 2902, pmFinal 2903, pmFinal 2904]:=by simpa only [List.length_cons,List.length_nil] using hmx.full_value
 have hmy:fact_000510.Holds smFinal pmFinal:=hframe _ (by native_decide)
 change ShardedRel (smFinal 688) [pmFinal 2993, pmFinal 2994, pmFinal 2995, pmFinal 2996] 1 [1,4,8,8] [1,1,8,8] at hmy
 have hmyV:smFinal 688=allGatherPrimDimN 1 4 0 [pmFinal 2993, pmFinal 2994, pmFinal 2995, pmFinal 2996]:=by simpa only [List.length_cons,List.length_nil] using hmy.full_value
 have hlw:fact_000163.Holds smFinal pmFinal:=hframe _ (by native_decide)
 change ShardedRel (smFinal 680) [pmFinal 680] 0 [32,32] [32,32] at hlw
 have hlwEq : smFinal 680 = pmFinal 680 := by rw [hlw.full_value]; exact allGatherPrimDimN_singleton_eq 0 _ (by rw [hlw.shard_shapes _ (by simp)]; native_decide)
 have hLS:=segment_000223_hLinearSm smStore
 change smFinal 1056 = (bw_linear (smFinal 862) (smFinal 1055) (smFinal 680)).1 at hLS
 have hDS:=segment_000223_hLinearDwSm smStore
 change smFinal 861 = (bw_linear (smFinal 862) (smFinal 1055) (smFinal 680)).2 at hDS
 have hLP0:=segment_000223_hLinearPm0 pmStore
 change pmFinal 2885 = (bw_linear (pmFinal 2887) (pmFinal 2869) (pmFinal 680)).1 at hLP0
 have hDP0:=segment_000223_hLinearDwPm0 pmStore
 change pmFinal 2886 = (bw_linear (pmFinal 2887) (pmFinal 2869) (pmFinal 680)).2 at hDP0
 have hLP1:=segment_000223_hLinearPm1 pmStore
 change pmFinal 2888 = (bw_linear (pmFinal 2890) (pmFinal 2870) (pmFinal 680)).1 at hLP1
 have hDP1:=segment_000223_hLinearDwPm1 pmStore
 change pmFinal 2889 = (bw_linear (pmFinal 2890) (pmFinal 2870) (pmFinal 680)).2 at hDP1
 have hLP2:=segment_000223_hLinearPm2 pmStore
 change pmFinal 2891 = (bw_linear (pmFinal 2893) (pmFinal 2871) (pmFinal 680)).1 at hLP2
 have hDP2:=segment_000223_hLinearDwPm2 pmStore
 change pmFinal 2892 = (bw_linear (pmFinal 2893) (pmFinal 2871) (pmFinal 680)).2 at hDP2
 have hLP3:=segment_000223_hLinearPm3 pmStore
 change pmFinal 2894 = (bw_linear (pmFinal 2896) (pmFinal 2872) (pmFinal 680)).1 at hLP3
 have hDP3:=segment_000223_hLinearDwPm3 pmStore
 change pmFinal 2895 = (bw_linear (pmFinal 2896) (pmFinal 2872) (pmFinal 680)).2 at hDP3
 have hMS0:=segment_000223_hMatmulSm0 smStore
 change smFinal 864=batchedMatmul (smFinal 870) (transpose2d (smFinal 688)) at hMS0
 have hMP0_0:=segment_000223_hMatmulPm0_0 pmStore
 change pmFinal 2914=batchedMatmul (pmFinal 3010) (transpose2d (pmFinal 2993)) at hMP0_0
 have hMP0_1:=segment_000223_hMatmulPm0_1 pmStore
 change pmFinal 2916=batchedMatmul (pmFinal 3012) (transpose2d (pmFinal 2994)) at hMP0_1
 have hMP0_2:=segment_000223_hMatmulPm0_2 pmStore
 change pmFinal 2918=batchedMatmul (pmFinal 3014) (transpose2d (pmFinal 2995)) at hMP0_2
 have hMP0_3:=segment_000223_hMatmulPm0_3 pmStore
 change pmFinal 2920=batchedMatmul (pmFinal 3016) (transpose2d (pmFinal 2996)) at hMP0_3
 have hMS1:=segment_000223_hMatmulSm1 smStore
 change smFinal 869=batchedMatmul (transpose2d (smFinal 683)) (smFinal 870) at hMS1
 have hMP1_0:=segment_000223_hMatmulPm1_0 pmStore
 change pmFinal 3009=batchedMatmul (transpose2d (pmFinal 2901)) (pmFinal 3010) at hMP1_0
 have hMP1_1:=segment_000223_hMatmulPm1_1 pmStore
 change pmFinal 3011=batchedMatmul (transpose2d (pmFinal 2902)) (pmFinal 3012) at hMP1_1
 have hMP1_2:=segment_000223_hMatmulPm1_2 pmStore
 change pmFinal 3013=batchedMatmul (transpose2d (pmFinal 2903)) (pmFinal 3014) at hMP1_2
 have hMP1_3:=segment_000223_hMatmulPm1_3 pmStore
 change pmFinal 3015=batchedMatmul (transpose2d (pmFinal 2904)) (pmFinal 3016) at hMP1_3
 have hlxC0:chunkPrimDimN 1 4 0 (smFinal 1055)=pmFinal 2869:=by rw [hlxV];simpa [List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ] using (chunkPrimDimN_allGatherPrimDimN_dim1_4_1_2_32 [pmFinal 2869, pmFinal 2870, pmFinal 2871, pmFinal 2872] 0 (by omega) (by simp) (by intro z hz;exact hlx.shard_shapes z hz))
 have hlxC1:chunkPrimDimN 1 4 1 (smFinal 1055)=pmFinal 2870:=by rw [hlxV];simpa [List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ] using (chunkPrimDimN_allGatherPrimDimN_dim1_4_1_2_32 [pmFinal 2869, pmFinal 2870, pmFinal 2871, pmFinal 2872] 1 (by omega) (by simp) (by intro z hz;exact hlx.shard_shapes z hz))
 have hlxC2:chunkPrimDimN 1 4 2 (smFinal 1055)=pmFinal 2871:=by rw [hlxV];simpa [List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ] using (chunkPrimDimN_allGatherPrimDimN_dim1_4_1_2_32 [pmFinal 2869, pmFinal 2870, pmFinal 2871, pmFinal 2872] 2 (by omega) (by simp) (by intro z hz;exact hlx.shard_shapes z hz))
 have hlxC3:chunkPrimDimN 1 4 3 (smFinal 1055)=pmFinal 2872:=by rw [hlxV];simpa [List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ] using (chunkPrimDimN_allGatherPrimDimN_dim1_4_1_2_32 [pmFinal 2869, pmFinal 2870, pmFinal 2871, pmFinal 2872] 3 (by omega) (by simp) (by intro z hz;exact hlx.shard_shapes z hz))
 have hmgC0:chunkPrimDimN 1 4 0 (smFinal 870)=pmFinal 3010:=by rw [hmgV];simpa [List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ] using (chunk1_gather1_roundtrip_1_1_8_8 (pmFinal 3010) (pmFinal 3012) (pmFinal 3014) (pmFinal 3016) (hmg.shard_shapes _ (by simp)) (hmg.shard_shapes _ (by simp)) (hmg.shard_shapes _ (by simp)) (hmg.shard_shapes _ (by simp)) 0 (by omega))
 have hmgC1:chunkPrimDimN 1 4 1 (smFinal 870)=pmFinal 3012:=by rw [hmgV];simpa [List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ] using (chunk1_gather1_roundtrip_1_1_8_8 (pmFinal 3010) (pmFinal 3012) (pmFinal 3014) (pmFinal 3016) (hmg.shard_shapes _ (by simp)) (hmg.shard_shapes _ (by simp)) (hmg.shard_shapes _ (by simp)) (hmg.shard_shapes _ (by simp)) 1 (by omega))
 have hmgC2:chunkPrimDimN 1 4 2 (smFinal 870)=pmFinal 3014:=by rw [hmgV];simpa [List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ] using (chunk1_gather1_roundtrip_1_1_8_8 (pmFinal 3010) (pmFinal 3012) (pmFinal 3014) (pmFinal 3016) (hmg.shard_shapes _ (by simp)) (hmg.shard_shapes _ (by simp)) (hmg.shard_shapes _ (by simp)) (hmg.shard_shapes _ (by simp)) 2 (by omega))
 have hmgC3:chunkPrimDimN 1 4 3 (smFinal 870)=pmFinal 3016:=by rw [hmgV];simpa [List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ] using (chunk1_gather1_roundtrip_1_1_8_8 (pmFinal 3010) (pmFinal 3012) (pmFinal 3014) (pmFinal 3016) (hmg.shard_shapes _ (by simp)) (hmg.shard_shapes _ (by simp)) (hmg.shard_shapes _ (by simp)) (hmg.shard_shapes _ (by simp)) 3 (by omega))
 have hmxC0:chunkPrimDimN 1 4 0 (smFinal 683)=pmFinal 2901:=by rw [hmxV];simpa [List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ] using (chunk1_gather1_roundtrip_1_1_8_8 (pmFinal 2901) (pmFinal 2902) (pmFinal 2903) (pmFinal 2904) (hmx.shard_shapes _ (by simp)) (hmx.shard_shapes _ (by simp)) (hmx.shard_shapes _ (by simp)) (hmx.shard_shapes _ (by simp)) 0 (by omega))
 have hmxC1:chunkPrimDimN 1 4 1 (smFinal 683)=pmFinal 2902:=by rw [hmxV];simpa [List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ] using (chunk1_gather1_roundtrip_1_1_8_8 (pmFinal 2901) (pmFinal 2902) (pmFinal 2903) (pmFinal 2904) (hmx.shard_shapes _ (by simp)) (hmx.shard_shapes _ (by simp)) (hmx.shard_shapes _ (by simp)) (hmx.shard_shapes _ (by simp)) 1 (by omega))
 have hmxC2:chunkPrimDimN 1 4 2 (smFinal 683)=pmFinal 2903:=by rw [hmxV];simpa [List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ] using (chunk1_gather1_roundtrip_1_1_8_8 (pmFinal 2901) (pmFinal 2902) (pmFinal 2903) (pmFinal 2904) (hmx.shard_shapes _ (by simp)) (hmx.shard_shapes _ (by simp)) (hmx.shard_shapes _ (by simp)) (hmx.shard_shapes _ (by simp)) 2 (by omega))
 have hmxC3:chunkPrimDimN 1 4 3 (smFinal 683)=pmFinal 2904:=by rw [hmxV];simpa [List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ] using (chunk1_gather1_roundtrip_1_1_8_8 (pmFinal 2901) (pmFinal 2902) (pmFinal 2903) (pmFinal 2904) (hmx.shard_shapes _ (by simp)) (hmx.shard_shapes _ (by simp)) (hmx.shard_shapes _ (by simp)) (hmx.shard_shapes _ (by simp)) 3 (by omega))
 have hmyC0:chunkPrimDimN 1 4 0 (smFinal 688)=pmFinal 2993:=by rw [hmyV];simpa [List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ] using (chunk1_gather1_roundtrip_1_1_8_8 (pmFinal 2993) (pmFinal 2994) (pmFinal 2995) (pmFinal 2996) (hmy.shard_shapes _ (by simp)) (hmy.shard_shapes _ (by simp)) (hmy.shard_shapes _ (by simp)) (hmy.shard_shapes _ (by simp)) 0 (by omega))
 have hmyC1:chunkPrimDimN 1 4 1 (smFinal 688)=pmFinal 2994:=by rw [hmyV];simpa [List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ] using (chunk1_gather1_roundtrip_1_1_8_8 (pmFinal 2993) (pmFinal 2994) (pmFinal 2995) (pmFinal 2996) (hmy.shard_shapes _ (by simp)) (hmy.shard_shapes _ (by simp)) (hmy.shard_shapes _ (by simp)) (hmy.shard_shapes _ (by simp)) 1 (by omega))
 have hmyC2:chunkPrimDimN 1 4 2 (smFinal 688)=pmFinal 2995:=by rw [hmyV];simpa [List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ] using (chunk1_gather1_roundtrip_1_1_8_8 (pmFinal 2993) (pmFinal 2994) (pmFinal 2995) (pmFinal 2996) (hmy.shard_shapes _ (by simp)) (hmy.shard_shapes _ (by simp)) (hmy.shard_shapes _ (by simp)) (hmy.shard_shapes _ (by simp)) 2 (by omega))
 have hmyC3:chunkPrimDimN 1 4 3 (smFinal 688)=pmFinal 2996:=by rw [hmyV];simpa [List.getD,List.getElem?_cons_zero,List.getElem?_cons_succ] using (chunk1_gather1_roundtrip_1_1_8_8 (pmFinal 2993) (pmFinal 2994) (pmFinal 2995) (pmFinal 2996) (hmy.shard_shapes _ (by simp)) (hmy.shard_shapes _ (by simp)) (hmy.shard_shapes _ (by simp)) (hmy.shard_shapes _ (by simp)) 3 (by omega))
 have hLCraw:=TrainVerify.Denote.bw_linear_dx_sequence_allGather_rank3 4 1 2 32 32 [pmFinal 2887, pmFinal 2890, pmFinal 2893, pmFinal 2896] [pmFinal 2869, pmFinal 2870, pmFinal 2871, pmFinal 2872] (smFinal 1055) (pmFinal 680) (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl hlg.shard_shapes hlx.shard_shapes hlx.full_shape (hlw.shard_shapes _ (by simp))
 have hLC := hLCraw
 simp only [List.zipWith] at hLC
 have hLOV:smFinal 1056=allGatherPrimDimN 1 4 0 [pmFinal 2885, pmFinal 2888, pmFinal 2891, pmFinal 2894]:=by rw [hLS,hlgV,hlwEq,hLC];rw [←hLP0, ←hLP1, ←hLP2, ←hLP3]
 have hDC:=TrainVerify.Denote.bw_linear_dw_sequence_reduction_rank3 4 1 2 32 32 [pmFinal 2887, pmFinal 2890, pmFinal 2893, pmFinal 2896] [pmFinal 2869, pmFinal 2870, pmFinal 2871, pmFinal 2872] (pmFinal 680) (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl hlg.shard_shapes hlx.shard_shapes (hlw.shard_shapes _ (by simp))
 simp only [List.zipWith] at hDC
 have hDsum:smFinal 861=tensorSum [pmFinal 2886, pmFinal 2889, pmFinal 2892, pmFinal 2895]:=by rw [hDS,hlgV,hlxV,hlwEq,hDC];rw [←hDP0, ←hDP1, ←hDP2, ←hDP3]
 have hDReduce:smFinal 861=allReducePrim [pmFinal 2886, pmFinal 2889, pmFinal 2892, pmFinal 2895].length 0 [pmFinal 2886, pmFinal 2889, pmFinal 2892, pmFinal 2895]:=by rw [hDsum];rfl
 have hMF:=TrainVerify.Denote.bw_matmul_fst_head_gather_rank4 4 1 1 8 8 8 [pmFinal 3010, pmFinal 3012, pmFinal 3014, pmFinal 3016] [pmFinal 2901, pmFinal 2902, pmFinal 2903, pmFinal 2904] [pmFinal 2993, pmFinal 2994, pmFinal 2995, pmFinal 2996] (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl hmg.shard_shapes hmx.shard_shapes hmy.shard_shapes
 simp only [List.zipWith,bw_matmul,batchedMatmulBwd] at hMF
 have hMFV:smFinal 864=allGatherPrimDimN 1 4 0 [pmFinal 2914, pmFinal 2916, pmFinal 2918, pmFinal 2920]:=by rw [hMS0,hmgV,hmyV,hMF];rw [←hMP0_0, ←hMP0_1, ←hMP0_2, ←hMP0_3]
 have hMS:=TrainVerify.Denote.bw_matmul_snd_head_gather_rank4 4 1 1 8 8 8 [pmFinal 3010, pmFinal 3012, pmFinal 3014, pmFinal 3016] [pmFinal 2901, pmFinal 2902, pmFinal 2903, pmFinal 2904] [pmFinal 2993, pmFinal 2994, pmFinal 2995, pmFinal 2996] (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl rfl hmg.shard_shapes hmx.shard_shapes hmy.shard_shapes
 simp only [List.zipWith,bw_matmul,batchedMatmulBwd] at hMS
 have hMSV:smFinal 869=allGatherPrimDimN 1 4 0 [pmFinal 3009, pmFinal 3011, pmFinal 3013, pmFinal 3015]:=by rw [hMS1,hmxV,hmgV,hMS];rw [←hMP1_0, ←hMP1_1, ←hMP1_2, ←hMP1_3]
 have hLOVL:smFinal 1056=allGatherPrimDimN 1 [pmFinal 2885, pmFinal 2888, pmFinal 2891, pmFinal 2894].length 0 [pmFinal 2885, pmFinal 2888, pmFinal 2891, pmFinal 2894]:=by simpa only [List.length_cons,List.length_nil] using hLOV
 have houtLO:fact_000233.Holds smFinal pmFinal:=by
  change ShardedRel (smFinal 1056) [pmFinal 2885, pmFinal 2888, pmFinal 2891, pmFinal 2894] 1 [1,8,32] [1,2,32]
  refine {full_value:=hLOVL,full_shape:=?_,shards_nonempty:=by simp,gather_dim_lt:=by native_decide,shard_shapes:=?_,shape_contract:=by simp only [List.length_cons,List.length_nil];native_decide}
  · rw [hLS]; exact bw_linear_3d_fst_shape 1 8 32 32 _ _ _ hlg.full_shape hlx.full_shape hlw.full_shape
  · intro piece hp; simp only [List.mem_cons,List.not_mem_nil,or_false] at hp;rcases hp with h0|h1|h2|h3
    · subst piece
      rw [hLP0]; exact bw_linear_3d_fst_shape 1 2 32 32 _ _ _ (hlg.shard_shapes _ (by simp)) (hlx.shard_shapes _ (by simp)) (hlw.shard_shapes _ (by simp))
    · subst piece
      rw [hLP1]; exact bw_linear_3d_fst_shape 1 2 32 32 _ _ _ (hlg.shard_shapes _ (by simp)) (hlx.shard_shapes _ (by simp)) (hlw.shard_shapes _ (by simp))
    · subst piece
      rw [hLP2]; exact bw_linear_3d_fst_shape 1 2 32 32 _ _ _ (hlg.shard_shapes _ (by simp)) (hlx.shard_shapes _ (by simp)) (hlw.shard_shapes _ (by simp))
    · subst piece
      rw [hLP3]; exact bw_linear_3d_fst_shape 1 2 32 32 _ _ _ (hlg.shard_shapes _ (by simp)) (hlx.shard_shapes _ (by simp)) (hlw.shard_shapes _ (by simp))
 have hMFVL:smFinal 864=allGatherPrimDimN 1 [pmFinal 2914, pmFinal 2916, pmFinal 2918, pmFinal 2920].length 0 [pmFinal 2914, pmFinal 2916, pmFinal 2918, pmFinal 2920]:=by simpa only [List.length_cons,List.length_nil] using hMFV
 have houtMF:fact_000230.Holds smFinal pmFinal:=by
  change ShardedRel (smFinal 864) [pmFinal 2914, pmFinal 2916, pmFinal 2918, pmFinal 2920] 1 [1,4,8,8] [1,1,8,8]
  refine {full_value:=hMFVL,full_shape:=?_,shards_nonempty:=by simp,gather_dim_lt:=by native_decide,shard_shapes:=?_,shape_contract:=by simp only [List.length_cons,List.length_nil];native_decide}
  · rw [hMS0]; exact batchedMatmul_shape_1_4_8_8_1_4_8_8 _ _ hmg.full_shape (transpose2d_shape_1_4_8_8 _ hmy.full_shape)
  · intro piece hp; simp only [List.mem_cons,List.not_mem_nil,or_false] at hp;rcases hp with h0|h1|h2|h3
    · subst piece
      rw [hMP0_0]; exact fw_matmul_shape_1_1_8_8 _ _ (hmg.shard_shapes _ (by simp)) (transpose2d_shape_1_1_8_8 _ (hmy.shard_shapes _ (by simp)))
    · subst piece
      rw [hMP0_1]; exact fw_matmul_shape_1_1_8_8 _ _ (hmg.shard_shapes _ (by simp)) (transpose2d_shape_1_1_8_8 _ (hmy.shard_shapes _ (by simp)))
    · subst piece
      rw [hMP0_2]; exact fw_matmul_shape_1_1_8_8 _ _ (hmg.shard_shapes _ (by simp)) (transpose2d_shape_1_1_8_8 _ (hmy.shard_shapes _ (by simp)))
    · subst piece
      rw [hMP0_3]; exact fw_matmul_shape_1_1_8_8 _ _ (hmg.shard_shapes _ (by simp)) (transpose2d_shape_1_1_8_8 _ (hmy.shard_shapes _ (by simp)))
 have hMSVL:smFinal 869=allGatherPrimDimN 1 [pmFinal 3009, pmFinal 3011, pmFinal 3013, pmFinal 3015].length 0 [pmFinal 3009, pmFinal 3011, pmFinal 3013, pmFinal 3015]:=by simpa only [List.length_cons,List.length_nil] using hMSV
 have houtMS:fact_000231.Holds smFinal pmFinal:=by
  change ShardedRel (smFinal 869) [pmFinal 3009, pmFinal 3011, pmFinal 3013, pmFinal 3015] 1 [1,4,8,8] [1,1,8,8]
  refine {full_value:=hMSVL,full_shape:=?_,shards_nonempty:=by simp,gather_dim_lt:=by native_decide,shard_shapes:=?_,shape_contract:=by simp only [List.length_cons,List.length_nil];native_decide}
  · rw [hMS1]; exact batchedMatmul_shape_1_4_8_8_1_4_8_8 _ _ (transpose2d_shape_1_4_8_8 _ hmx.full_shape) hmg.full_shape
  · intro piece hp; simp only [List.mem_cons,List.not_mem_nil,or_false] at hp;rcases hp with h0|h1|h2|h3
    · subst piece
      rw [hMP1_0]; exact fw_matmul_shape_1_1_8_8 _ _ (transpose2d_shape_1_1_8_8 _ (hmx.shard_shapes _ (by simp))) (hmg.shard_shapes _ (by simp))
    · subst piece
      rw [hMP1_1]; exact fw_matmul_shape_1_1_8_8 _ _ (transpose2d_shape_1_1_8_8 _ (hmx.shard_shapes _ (by simp))) (hmg.shard_shapes _ (by simp))
    · subst piece
      rw [hMP1_2]; exact fw_matmul_shape_1_1_8_8 _ _ (transpose2d_shape_1_1_8_8 _ (hmx.shard_shapes _ (by simp))) (hmg.shard_shapes _ (by simp))
    · subst piece
      rw [hMP1_3]; exact fw_matmul_shape_1_1_8_8 _ _ (transpose2d_shape_1_1_8_8 _ (hmx.shard_shapes _ (by simp))) (hmg.shard_shapes _ (by simp))
 have hDFullShape:(smFinal 861).shape=[32,32]:=by rw [hDS];exact bw_linear_3d_snd_shape 1 8 32 32 _ _ _ hlg.full_shape hlx.full_shape hlw.full_shape
 have houtDW:test_dw_fact.Holds smFinal pmFinal:=by
  change ReductionRel (smFinal 861) [pmFinal 2886, pmFinal 2889, pmFinal 2892, pmFinal 2895] [32,32]
  refine {full_value:=hDReduce,full_shape:=hDFullShape,contributions_nonempty:=by simp,contribution_shapes:=?_,reduced_shape:=?_}
  · intro piece hp; simp only [List.mem_cons,List.not_mem_nil,or_false] at hp;rcases hp with h0|h1|h2|h3
    · subst piece
      rw [hDP0]
      exact bw_linear_3d_snd_shape 1 2 32 32 _ _ _ (hlg.shard_shapes _ (by simp)) (hlx.shard_shapes _ (by simp)) (hlw.shard_shapes _ (by simp))
    · subst piece
      rw [hDP1]
      exact bw_linear_3d_snd_shape 1 2 32 32 _ _ _ (hlg.shard_shapes _ (by simp)) (hlx.shard_shapes _ (by simp)) (hlw.shard_shapes _ (by simp))
    · subst piece
      rw [hDP2]
      exact bw_linear_3d_snd_shape 1 2 32 32 _ _ _ (hlg.shard_shapes _ (by simp)) (hlx.shard_shapes _ (by simp)) (hlw.shard_shapes _ (by simp))
    · subst piece
      rw [hDP3]
      exact bw_linear_3d_snd_shape 1 2 32 32 _ _ _ (hlg.shard_shapes _ (by simp)) (hlx.shard_shapes _ (by simp)) (hlw.shard_shapes _ (by simp))
  · rw [← hDReduce]
    exact hDFullShape
 intro fact hfact
 have covered:fact∈[fact_000233,test_dw_fact,fact_000230,fact_000231]++state_000223.facts:=by exact (show state_000224.facts⊆[fact_000233,test_dw_fact,fact_000230,fact_000231]++state_000223.facts by native_decide) hfact
 simp only [List.mem_append] at covered
 rcases covered with fresh|old
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh;rcases fresh with rfl|rfl|rfl|rfl
   · exact houtLO
   · exact houtDW
   · exact houtMF
   · exact houtMS
 · exact hframe fact old

set_option maxRecDepth 32768 in
private def segment_000223:ClosedDepSegmentCertificate TrainVerify.Denote.Generated.sm TrainVerify.Denote.Generated.pm state_000223 state_000224 where
 smNodes:=segment_000223_sm_nodes
 pmNodes:=segment_000223_pm_nodes
 sound:=by intro smStore pmStore hstate; have h:= segment_000223_sound smStore pmStore hstate; unfold segment_000223_sm_final segment_000223_pm_final at h; exact h

#print axioms segment_000223
end
end TrainVerify.Denote.SequenceDwMixedsegment_000223
