/- Preserved shuffle-free cut declaration for Goal 4 (tensor id: 4676).

   The canonical full Goal_4 graph now targets tensor 4929.  This module keeps
   the independently sound 25/55-node routing-stack cut used by Pattern_4; the
   graph names are cut-qualified so importing it beside Goal_4 is unambiguous. -/
import denote.GeneratedYOCOMoE

set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

def sm_goal_4_cut : GraphDecl := by
  refine { numRanks := 1, nodes := ?_ }
  exact [
    { rank := 0, op := "OpName.FW_topk_routing", ins := [4708], outs := [4709, 4710, 4711], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [4762], outs := [4763, 4764, 4765], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [4816], outs := [4817, 4818, 4819], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [4870], outs := [4871, 4872, 4873], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [4924], outs := [4925, 4926, 4927], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [4978], outs := [4979, 4980, 4981], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [5032], outs := [5033, 5034, 5035], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [5086], outs := [5087, 5088, 5089], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [5140], outs := [5141, 5142, 5143], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [5194], outs := [5195, 5196, 5197], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [5248], outs := [5249, 5250, 5251], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [5302], outs := [5303, 5304, 5305], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [5359], outs := [5360, 5361, 5362], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [5408], outs := [5409, 5410, 5411], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [5457], outs := [5458, 5459, 5460], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [5506], outs := [5507, 5508, 5509], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [5555], outs := [5556, 5557, 5558], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [5604], outs := [5605, 5606, 5607], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [5653], outs := [5654, 5655, 5656], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [5702], outs := [5703, 5704, 5705], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [5751], outs := [5752, 5753, 5754], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [5800], outs := [5801, 5802, 5803], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [5849], outs := [5850, 5851, 5852], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [5898], outs := [5899, 5900, 5901], params := [8] },
    { rank := 0, op := "OpName.FW_stack", ins := [4711, 4765, 4819, 4873, 4927, 4981, 5035, 5089, 5143, 5197, 5251, 5305, 5362, 5411, 5460, 5509, 5558, 5607, 5656, 5705, 5754, 5803, 5852, 5901], outs := [4676] },
  ]

def pm_goal_4_cut : GraphDecl := by
  refine { numRanks := 2, nodes := ?_ }
  exact [
    { rank := 0, op := "OpName.ChunkPrim", ins := [4708], outs := [7479], params := [0] },
    { rank := 1, op := "OpName.ChunkPrim", ins := [4708], outs := [7480], params := [0] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [7479], outs := [7481, 7483, 7485], params := [8] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [7480], outs := [7482, 7484, 7486], params := [8] },
    { rank := 0, op := "OpName.ChunkPrim", ins := [4762], outs := [7665], params := [0] },
    { rank := 1, op := "OpName.ChunkPrim", ins := [4762], outs := [7666], params := [0] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [7665], outs := [7667, 7669, 7671], params := [8] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [7666], outs := [7668, 7670, 7672], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [7851], outs := [7853, 7855, 7857], params := [8] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [7852], outs := [7854, 7856, 7858], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [8037], outs := [8039, 8041, 8043], params := [8] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [8038], outs := [8040, 8042, 8044], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [8223], outs := [8225, 8227, 8229], params := [8] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [8224], outs := [8226, 8228, 8230], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [8409], outs := [8411, 8413, 8415], params := [8] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [8410], outs := [8412, 8414, 8416], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [8595], outs := [8597, 8599, 8601], params := [8] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [8596], outs := [8598, 8600, 8602], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [8781], outs := [8783, 8785, 8787], params := [8] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [8782], outs := [8784, 8786, 8788], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [8967], outs := [8969, 8971, 8973], params := [8] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [8968], outs := [8970, 8972, 8974], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [9153], outs := [9155, 9157, 9159], params := [8] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [9154], outs := [9156, 9158, 9160], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [9339], outs := [9341, 9343, 9345], params := [8] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [9340], outs := [9342, 9344, 9346], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [9525], outs := [9527, 9529, 9531], params := [8] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [9526], outs := [9528, 9530, 9532], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [9729], outs := [9731, 9733, 9735], params := [8] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [9730], outs := [9732, 9734, 9736], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [9901], outs := [9903, 9905, 9907], params := [8] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [9902], outs := [9904, 9906, 9908], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [10073], outs := [10075, 10077, 10079], params := [8] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [10074], outs := [10076, 10078, 10080], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [10245], outs := [10247, 10249, 10251], params := [8] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [10246], outs := [10248, 10250, 10252], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [10417], outs := [10419, 10421, 10423], params := [8] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [10418], outs := [10420, 10422, 10424], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [10589], outs := [10591, 10593, 10595], params := [8] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [10590], outs := [10592, 10594, 10596], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [10761], outs := [10763, 10765, 10767], params := [8] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [10762], outs := [10764, 10766, 10768], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [10933], outs := [10935, 10937, 10939], params := [8] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [10934], outs := [10936, 10938, 10940], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [11105], outs := [11107, 11109, 11111], params := [8] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [11106], outs := [11108, 11110, 11112], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [11277], outs := [11279, 11281, 11283], params := [8] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [11278], outs := [11280, 11282, 11284], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [11449], outs := [11451, 11453, 11455], params := [8] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [11450], outs := [11452, 11454, 11456], params := [8] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [11621], outs := [11623, 11625, 11627], params := [8] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [11622], outs := [11624, 11626, 11628], params := [8] },
    { rank := 0, op := "OpName.FW_stack", ins := [7485, 7671, 7857, 8043, 8229, 8415, 8601, 8787, 8973, 9159, 9345, 9531, 9735, 9907, 10079, 10251, 10423, 10595, 10767, 10939, 11111, 11283, 11455, 11627], outs := [11781] },
    { rank := 1, op := "OpName.FW_stack", ins := [7486, 7672, 7858, 8044, 8230, 8416, 8602, 8788, 8974, 9160, 9346, 9532, 9736, 9908, 10080, 10252, 10424, 10596, 10768, 10940, 11112, 11284, 11456, 11628], outs := [11782] },
    { rank := 0, op := "OpName.AllGatherPrim", ins := [11781, 11782], outs := [4676], params := [1] },
  ]

def sm_goal_4_cutInitShapes : List (Tid × Shape) := [
  (4708, [4096, 64]),
  (4762, [4096, 64]),
  (4816, [4096, 64]),
  (4870, [4096, 64]),
  (4924, [4096, 64]),
  (4978, [4096, 64]),
  (5032, [4096, 64]),
  (5086, [4096, 64]),
  (5140, [4096, 64]),
  (5194, [4096, 64]),
  (5248, [4096, 64]),
  (5302, [4096, 64]),
  (5359, [4096, 64]),
  (5408, [4096, 64]),
  (5457, [4096, 64]),
  (5506, [4096, 64]),
  (5555, [4096, 64]),
  (5604, [4096, 64]),
  (5653, [4096, 64]),
  (5702, [4096, 64]),
  (5751, [4096, 64]),
  (5800, [4096, 64]),
  (5849, [4096, 64]),
  (5898, [4096, 64]),
]

def sm_goal_4_cutInitEnv : ShapeEnv := shapeEnvOfList sm_goal_4_cutInitShapes

def pm_goal_4_cutInitShapes : List (Tid × Shape) := [
  (4708, [4096, 64]),
  (4762, [4096, 64]),
  (7851, [2048, 64]),
  (7852, [2048, 64]),
  (8037, [2048, 64]),
  (8038, [2048, 64]),
  (8223, [2048, 64]),
  (8224, [2048, 64]),
  (8409, [2048, 64]),
  (8410, [2048, 64]),
  (8595, [2048, 64]),
  (8596, [2048, 64]),
  (8781, [2048, 64]),
  (8782, [2048, 64]),
  (8967, [2048, 64]),
  (8968, [2048, 64]),
  (9153, [2048, 64]),
  (9154, [2048, 64]),
  (9339, [2048, 64]),
  (9340, [2048, 64]),
  (9525, [2048, 64]),
  (9526, [2048, 64]),
  (9729, [2048, 64]),
  (9730, [2048, 64]),
  (9901, [2048, 64]),
  (9902, [2048, 64]),
  (10073, [2048, 64]),
  (10074, [2048, 64]),
  (10245, [2048, 64]),
  (10246, [2048, 64]),
  (10417, [2048, 64]),
  (10418, [2048, 64]),
  (10589, [2048, 64]),
  (10590, [2048, 64]),
  (10761, [2048, 64]),
  (10762, [2048, 64]),
  (10933, [2048, 64]),
  (10934, [2048, 64]),
  (11105, [2048, 64]),
  (11106, [2048, 64]),
  (11277, [2048, 64]),
  (11278, [2048, 64]),
  (11449, [2048, 64]),
  (11450, [2048, 64]),
  (11621, [2048, 64]),
  (11622, [2048, 64]),
]

def pm_goal_4_cutInitEnv : ShapeEnv := shapeEnvOfList pm_goal_4_cutInitShapes


/-! ### Shuffle-free cut boundary contracts

These records retain the old ordinary-gather boundary obligations ONLY inside
the sliced cut graph. They are false on the faithful full graph (the PM values
are zigzag-owned there), but sound and satisfiable as explicit caller contracts
for this ChunkPrim-only cut. Keeping them local prevents accidental reuse as
full-graph goals while preserving the original cut proof interface. -/

def goal4CutIntermediateGoal_4708 : LineageGoal :=
  { ts := 4708, tsShape := [4096, 64], tps := [{ rank := 0, tid := 4708 }], tpShapes := [[4096, 64]] }

def goal4CutIntermediateGoal_4762 : LineageGoal :=
  { ts := 4762, tsShape := [4096, 64], tps := [{ rank := 0, tid := 4762 }], tpShapes := [[4096, 64]] }

def goal4CutIntermediateGoal_4816 : LineageGoal :=
  { ts := 4816, tsShape := [4096, 64], tps := [{ rank := 0, tid := 7851 }, { rank := 1, tid := 7852 }], tpShapes := [[2048, 64], [2048, 64]] }

def goal4CutIntermediateGoal_4870 : LineageGoal :=
  { ts := 4870, tsShape := [4096, 64], tps := [{ rank := 0, tid := 8037 }, { rank := 1, tid := 8038 }], tpShapes := [[2048, 64], [2048, 64]] }

def goal4CutIntermediateGoal_4924 : LineageGoal :=
  { ts := 4924, tsShape := [4096, 64], tps := [{ rank := 0, tid := 8223 }, { rank := 1, tid := 8224 }], tpShapes := [[2048, 64], [2048, 64]] }

def goal4CutIntermediateGoal_4978 : LineageGoal :=
  { ts := 4978, tsShape := [4096, 64], tps := [{ rank := 0, tid := 8409 }, { rank := 1, tid := 8410 }], tpShapes := [[2048, 64], [2048, 64]] }

def goal4CutIntermediateGoal_5032 : LineageGoal :=
  { ts := 5032, tsShape := [4096, 64], tps := [{ rank := 0, tid := 8595 }, { rank := 1, tid := 8596 }], tpShapes := [[2048, 64], [2048, 64]] }

def goal4CutIntermediateGoal_5086 : LineageGoal :=
  { ts := 5086, tsShape := [4096, 64], tps := [{ rank := 0, tid := 8781 }, { rank := 1, tid := 8782 }], tpShapes := [[2048, 64], [2048, 64]] }

def goal4CutIntermediateGoal_5140 : LineageGoal :=
  { ts := 5140, tsShape := [4096, 64], tps := [{ rank := 0, tid := 8967 }, { rank := 1, tid := 8968 }], tpShapes := [[2048, 64], [2048, 64]] }

def goal4CutIntermediateGoal_5194 : LineageGoal :=
  { ts := 5194, tsShape := [4096, 64], tps := [{ rank := 0, tid := 9153 }, { rank := 1, tid := 9154 }], tpShapes := [[2048, 64], [2048, 64]] }

def goal4CutIntermediateGoal_5248 : LineageGoal :=
  { ts := 5248, tsShape := [4096, 64], tps := [{ rank := 0, tid := 9339 }, { rank := 1, tid := 9340 }], tpShapes := [[2048, 64], [2048, 64]] }

def goal4CutIntermediateGoal_5302 : LineageGoal :=
  { ts := 5302, tsShape := [4096, 64], tps := [{ rank := 0, tid := 9525 }, { rank := 1, tid := 9526 }], tpShapes := [[2048, 64], [2048, 64]] }

def goal4CutIntermediateGoal_5359 : LineageGoal :=
  { ts := 5359, tsShape := [4096, 64], tps := [{ rank := 0, tid := 9729 }, { rank := 1, tid := 9730 }], tpShapes := [[2048, 64], [2048, 64]] }

def goal4CutIntermediateGoal_5408 : LineageGoal :=
  { ts := 5408, tsShape := [4096, 64], tps := [{ rank := 0, tid := 9901 }, { rank := 1, tid := 9902 }], tpShapes := [[2048, 64], [2048, 64]] }

def goal4CutIntermediateGoal_5457 : LineageGoal :=
  { ts := 5457, tsShape := [4096, 64], tps := [{ rank := 0, tid := 10073 }, { rank := 1, tid := 10074 }], tpShapes := [[2048, 64], [2048, 64]] }

def goal4CutIntermediateGoal_5506 : LineageGoal :=
  { ts := 5506, tsShape := [4096, 64], tps := [{ rank := 0, tid := 10245 }, { rank := 1, tid := 10246 }], tpShapes := [[2048, 64], [2048, 64]] }

def goal4CutIntermediateGoal_5555 : LineageGoal :=
  { ts := 5555, tsShape := [4096, 64], tps := [{ rank := 0, tid := 10417 }, { rank := 1, tid := 10418 }], tpShapes := [[2048, 64], [2048, 64]] }

def goal4CutIntermediateGoal_5604 : LineageGoal :=
  { ts := 5604, tsShape := [4096, 64], tps := [{ rank := 0, tid := 10589 }, { rank := 1, tid := 10590 }], tpShapes := [[2048, 64], [2048, 64]] }

def goal4CutIntermediateGoal_5653 : LineageGoal :=
  { ts := 5653, tsShape := [4096, 64], tps := [{ rank := 0, tid := 10761 }, { rank := 1, tid := 10762 }], tpShapes := [[2048, 64], [2048, 64]] }

def goal4CutIntermediateGoal_5702 : LineageGoal :=
  { ts := 5702, tsShape := [4096, 64], tps := [{ rank := 0, tid := 10933 }, { rank := 1, tid := 10934 }], tpShapes := [[2048, 64], [2048, 64]] }

def goal4CutIntermediateGoal_5751 : LineageGoal :=
  { ts := 5751, tsShape := [4096, 64], tps := [{ rank := 0, tid := 11105 }, { rank := 1, tid := 11106 }], tpShapes := [[2048, 64], [2048, 64]] }

def goal4CutIntermediateGoal_5800 : LineageGoal :=
  { ts := 5800, tsShape := [4096, 64], tps := [{ rank := 0, tid := 11277 }, { rank := 1, tid := 11278 }], tpShapes := [[2048, 64], [2048, 64]] }

def goal4CutIntermediateGoal_5849 : LineageGoal :=
  { ts := 5849, tsShape := [4096, 64], tps := [{ rank := 0, tid := 11449 }, { rank := 1, tid := 11450 }], tpShapes := [[2048, 64], [2048, 64]] }

def goal4CutIntermediateGoal_5898 : LineageGoal :=
  { ts := 5898, tsShape := [4096, 64], tps := [{ rank := 0, tid := 11621 }, { rank := 1, tid := 11622 }], tpShapes := [[2048, 64], [2048, 64]] }

def goal_4_prereqs : List LineageGoal :=
  [goal4CutIntermediateGoal_4708, goal4CutIntermediateGoal_4762,
   goal4CutIntermediateGoal_4816, goal4CutIntermediateGoal_4870,
   goal4CutIntermediateGoal_4924, goal4CutIntermediateGoal_4978,
   goal4CutIntermediateGoal_5032, goal4CutIntermediateGoal_5086,
   goal4CutIntermediateGoal_5140, goal4CutIntermediateGoal_5194,
   goal4CutIntermediateGoal_5248, goal4CutIntermediateGoal_5302]

def goal_4_cut_initGoals : List LineageGoal :=
  goal_4_prereqs ++
    [goal4CutIntermediateGoal_5359, goal4CutIntermediateGoal_5408,
     goal4CutIntermediateGoal_5457, goal4CutIntermediateGoal_5506,
     goal4CutIntermediateGoal_5555, goal4CutIntermediateGoal_5604,
     goal4CutIntermediateGoal_5653, goal4CutIntermediateGoal_5702,
     goal4CutIntermediateGoal_5751, goal4CutIntermediateGoal_5800,
     goal4CutIntermediateGoal_5849, goal4CutIntermediateGoal_5898]

-- goal_4 has no global (full-graph) statement: its PM shards are CP
-- zigzag-owned, so an ordinary gather over them is false. See
-- trainverify/GOAL_3_4_LAYOUT_SPLIT.md: nnScaler's RVD model cannot express a
-- permuted sharding, so the runtime all_gather is a plain rank-order concat
-- that does not undo the zigzag. The CUT graph below is shuffle-free
-- (built from ChunkPrim), so this local obligation is sound and provable.
def goal_4_cut_goal : LineageGoal :=
  { ts := 4676, tsShape := [24, 4096, 64], tps := [{ rank := 0, tid := 4676 }], tpShapes := [[24, 4096, 64]] }

def goal_4_stmt_cut : Prop :=
  CoarseLineageHoldsWithInit sm_goal_4_cut pm_goal_4_cut goal_4_cut_goal sm_goal_4_cutInitEnv pm_goal_4_cutInitEnv goal_4_cut_initGoals

end TrainVerify.Denote.GeneratedGoals

