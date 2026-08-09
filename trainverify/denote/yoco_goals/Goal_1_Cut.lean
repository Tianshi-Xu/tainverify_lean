/- Preserved legacy cut declaration for Goal 1 (tensor id: 4673).

   The canonical Goal_1 module now contains the ancestry-closed full graph.
   This module keeps the independently sound 25/53-node cut used by the
   legacy Pattern_1 theorem; all graph and environment names are cut-qualified. -/
import denote.GeneratedYOCOMoE

set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

def sm_goal_1_cut : GraphDecl := by
  refine { numRanks := 1, nodes := ?_ }
  exact [
    { rank := 0, op := "OpName.FW_multiref", ins := [5893], outs := [8576, 8580], params := [2] },
    { rank := 0, op := "OpName.FW_multiref", ins := [5895], outs := [8587, 8591, 8595, 8599, 8603], params := [5] },
    { rank := 0, op := "OpName.FW_reshape", ins := [8595], outs := [5905] },
    { rank := 0, op := "OpName.FW_reshape", ins := [8599], outs := [5910] },
    { rank := 0, op := "OpName.FW_reshape", ins := [8603], outs := [5914] },
    { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5905, 5906], outs := [5907] },
    { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5910, 5911], outs := [5912] },
    { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5914, 5915], outs := [5916] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [5898], outs := [5899, 5900, 5901], params := [8, 64] },
    { rank := 0, op := "OpName.FW_view", ins := [5907], outs := [5908], params := [4096, 1] },
    { rank := 0, op := "OpName.FW_view", ins := [5912], outs := [5913], params := [4096, 512] },
    { rank := 0, op := "OpName.FW_view", ins := [5916], outs := [5917], params := [4096, 512] },
    { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8591, 5899, 5900, 5902, 5903], outs := [5904], params := [64, 0, 64, 8] },
    { rank := 0, op := "OpName.FW_sigmoid", ins := [5908], outs := [5909] },
    { rank := 0, op := "OpName.FW_swiglu", ins := [5913, 5917], outs := [5918] },
    { rank := 0, op := "OpName.FW_reshape", ins := [5918], outs := [5919] },
    { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5919, 5920], outs := [5921] },
    { rank := 0, op := "OpName.FW_view", ins := [5921], outs := [5922], params := [4096, 1024] },
    { rank := 0, op := "OpName.FW_mul", ins := [5909, 5922], outs := [5923] },
    { rank := 0, op := "OpName.FW_add", ins := [5904, 5923], outs := [5924] },
    { rank := 0, op := "OpName.FW_float", ins := [5924], outs := [5925] },
    { rank := 0, op := "OpName.FW_add", ins := [8580, 5925], outs := [5926] },
    { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5926, 5927], outs := [5928], params := [1, 0] },
    { rank := 0, op := "OpName.FW_rms_norm", ins := [5928, 5929], outs := [5930] },
    { rank := 0, op := "OpName.FW_inner_chunk_ce", ins := [5930, 5931, 4678], outs := [4673, 4674], params := [1024] },
  ]

def pm_goal_1_cut : GraphDecl := by
  refine { numRanks := 2, nodes := ?_ }
  exact [
    { rank := 0, op := "OpName.ChunkPrim", ins := [4678], outs := [11835], params := [0] },
    { rank := 1, op := "OpName.ChunkPrim", ins := [4678], outs := [11836], params := [0] },
    { rank := 0, op := "OpName.FW_multiref", ins := [11609], outs := [16843, 16847], params := [2] },
    { rank := 1, op := "OpName.FW_multiref", ins := [11610], outs := [16851, 16855], params := [2] },
    { rank := 0, op := "OpName.FW_multiref", ins := [11613], outs := [16862, 16866, 16870, 16874, 16878], params := [5] },
    { rank := 1, op := "OpName.FW_multiref", ins := [11614], outs := [16885, 16889, 16893, 16897, 16901], params := [5] },
    { rank := 0, op := "OpName.FW_reshape", ins := [16870], outs := [11635] },
    { rank := 0, op := "OpName.FW_reshape", ins := [16874], outs := [11649] },
    { rank := 0, op := "OpName.FW_reshape", ins := [16878], outs := [11667] },
    { rank := 1, op := "OpName.FW_reshape", ins := [16893], outs := [11636] },
    { rank := 1, op := "OpName.FW_reshape", ins := [16897], outs := [11650] },
    { rank := 1, op := "OpName.FW_reshape", ins := [16901], outs := [11668] },
    { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11635, 5906], outs := [11639] },
    { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11649, 5911], outs := [11653] },
    { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11667, 5915], outs := [11671] },
    { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11636, 5906], outs := [11640] },
    { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11650, 5911], outs := [11654] },
    { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11668, 5915], outs := [11672] },
    { rank := 0, op := "OpName.FW_topk_routing", ins := [11621], outs := [11623, 11625, 11627], params := [8, 64] },
    { rank := 0, op := "OpName.FW_view", ins := [11639], outs := [11645], params := [2048, 1] },
    { rank := 0, op := "OpName.FW_view", ins := [11653], outs := [11663], params := [2048, 512] },
    { rank := 0, op := "OpName.FW_view", ins := [11671], outs := [11681], params := [2048, 512] },
    { rank := 1, op := "OpName.FW_topk_routing", ins := [11622], outs := [11624, 11626, 11628], params := [8, 64] },
    { rank := 1, op := "OpName.FW_view", ins := [11640], outs := [11646], params := [2048, 1] },
    { rank := 1, op := "OpName.FW_view", ins := [11654], outs := [11664], params := [2048, 512] },
    { rank := 1, op := "OpName.FW_view", ins := [11672], outs := [11682], params := [2048, 512] },
    { rank := 0, op := "OpName.FW_all2all_moe_gmm_full", ins := [16866, 11623, 11625, 11629, 11630, 11631, 11632], outs := [11633], params := [64, 8] },
    { rank := 0, op := "OpName.FW_sigmoid", ins := [11645], outs := [11647] },
    { rank := 0, op := "OpName.FW_swiglu", ins := [11663, 11681], outs := [11685] },
    { rank := 1, op := "OpName.FW_all2all_moe_gmm_full", ins := [16889, 11624, 11626, 11629, 11630, 11631, 11632], outs := [11634], params := [64, 8] },
    { rank := 1, op := "OpName.FW_sigmoid", ins := [11646], outs := [11648] },
    { rank := 1, op := "OpName.FW_swiglu", ins := [11664, 11682], outs := [11686] },
    { rank := 0, op := "OpName.FW_reshape", ins := [11685], outs := [11687] },
    { rank := 1, op := "OpName.FW_reshape", ins := [11686], outs := [11688] },
    { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11687, 5920], outs := [11693] },
    { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11688, 5920], outs := [11694] },
    { rank := 0, op := "OpName.FW_view", ins := [11693], outs := [11703], params := [2048, 1024] },
    { rank := 1, op := "OpName.FW_view", ins := [11694], outs := [11704], params := [2048, 1024] },
    { rank := 0, op := "OpName.FW_mul", ins := [11647, 11703], outs := [11707] },
    { rank := 1, op := "OpName.FW_mul", ins := [11648, 11704], outs := [11708] },
    { rank := 0, op := "OpName.FW_add", ins := [11633, 11707], outs := [11711] },
    { rank := 1, op := "OpName.FW_add", ins := [11634, 11708], outs := [11712] },
    { rank := 0, op := "OpName.FW_float", ins := [11711], outs := [11717] },
    { rank := 1, op := "OpName.FW_float", ins := [11712], outs := [11718] },
    { rank := 0, op := "OpName.FW_add", ins := [16847, 11717], outs := [11721] },
    { rank := 1, op := "OpName.FW_add", ins := [16855, 11718], outs := [11722] },
    { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11721, 5927], outs := [11727], params := [2, 0] },
    { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11722, 5927], outs := [11728], params := [2, 1] },
    { rank := 0, op := "OpName.FW_rms_norm", ins := [11727, 5929], outs := [11833] },
    { rank := 1, op := "OpName.FW_rms_norm", ins := [11728, 5929], outs := [11834] },
    { rank := 0, op := "OpName.FW_inner_chunk_ce", ins := [11833, 5931, 11835], outs := [11837, 11839], params := [1024] },
    { rank := 1, op := "OpName.FW_inner_chunk_ce", ins := [11834, 5931, 11836], outs := [11838, 11840], params := [1024] },
    { rank := 0, op := "OpName.AllGatherPrim", ins := [11837, 11838], outs := [4673], params := [0] },
  ]

def sm_goal_1_cutInitShapes : List (Tid × Shape) := [
  (4678, [4096]),
  (5893, [4096, 1024]),
  (5895, [4096, 1024]),
  (5898, [4096, 64]),
  (5902, [64, 1024, 1024]),
  (5903, [64, 1024, 512]),
  (5906, [1, 1024]),
  (5911, [512, 1024]),
  (5915, [512, 1024]),
  (5920, [1024, 512]),
  (5927, [2]),
  (5929, [1024]),
  (5931, [154880, 1024]),
]

def sm_goal_1_cutInitEnv : ShapeEnv := shapeEnvOfList sm_goal_1_cutInitShapes

def pm_goal_1_cutInitShapes : List (Tid × Shape) := [
  (4678, [4096]),
  (5906, [1, 1024]),
  (5911, [512, 1024]),
  (5915, [512, 1024]),
  (5920, [1024, 512]),
  (5927, [2]),
  (5929, [1024]),
  (5931, [154880, 1024]),
  (11609, [2048, 1024]),
  (11610, [2048, 1024]),
  (11613, [2048, 1024]),
  (11614, [2048, 1024]),
  (11621, [2048, 64]),
  (11622, [2048, 64]),
  (11629, [32, 1024, 1024]),
  (11630, [32, 1024, 1024]),
  (11631, [32, 1024, 512]),
  (11632, [32, 1024, 512]),
]

def pm_goal_1_cutInitEnv : ShapeEnv := shapeEnvOfList pm_goal_1_cutInitShapes


/-! ### Shuffle-free cut boundary contracts

These records retain the old ordinary-gather boundary obligations ONLY inside
the sliced cut graph. They are false on the faithful full graph (the PM values
are zigzag-owned there), but sound and satisfiable as explicit caller contracts
for this ChunkPrim-only cut. Keeping them local prevents accidental reuse as
full-graph goals while preserving the original cut proof interface. -/

def goal1CutIntermediateGoal_5893 : LineageGoal :=
  { ts := 5893, tsShape := [4096, 1024], tps := [{ rank := 0, tid := 11609 }, { rank := 1, tid := 11610 }], tpShapes := [[2048, 1024], [2048, 1024]] }

def goal1CutIntermediateGoal_5895 : LineageGoal :=
  { ts := 5895, tsShape := [4096, 1024], tps := [{ rank := 0, tid := 11613 }, { rank := 1, tid := 11614 }], tpShapes := [[2048, 1024], [2048, 1024]] }

def goal1CutIntermediateGoal_5898 : LineageGoal :=
  { ts := 5898, tsShape := [4096, 64], tps := [{ rank := 0, tid := 11621 }, { rank := 1, tid := 11622 }], tpShapes := [[2048, 64], [2048, 64]] }

def goal1CutInitGoal_4678 : LineageGoal :=
  { ts := 4678, tsShape := [4096], tps := [{ rank := 0, tid := 4678 }], tpShapes := [[4096]] }

def goal1CutInitGoal_5902 : LineageGoal :=
  { ts := 5902, tsShape := [64, 1024, 1024], tps := [{ rank := 0, tid := 11629 }, { rank := 1, tid := 11630 }], tpShapes := [[32, 1024, 1024], [32, 1024, 1024]] }

def goal1CutInitGoal_5903 : LineageGoal :=
  { ts := 5903, tsShape := [64, 1024, 512], tps := [{ rank := 0, tid := 11631 }, { rank := 1, tid := 11632 }], tpShapes := [[32, 1024, 512], [32, 1024, 512]] }

def goal1CutInitGoal_5906 : LineageGoal :=
  { ts := 5906, tsShape := [1, 1024], tps := [{ rank := 0, tid := 5906 }], tpShapes := [[1, 1024]] }

def goal1CutInitGoal_5911 : LineageGoal :=
  { ts := 5911, tsShape := [512, 1024], tps := [{ rank := 0, tid := 5911 }], tpShapes := [[512, 1024]] }

def goal1CutInitGoal_5915 : LineageGoal :=
  { ts := 5915, tsShape := [512, 1024], tps := [{ rank := 0, tid := 5915 }], tpShapes := [[512, 1024]] }

def goal1CutInitGoal_5920 : LineageGoal :=
  { ts := 5920, tsShape := [1024, 512], tps := [{ rank := 0, tid := 5920 }], tpShapes := [[1024, 512]] }

def goal1CutInitGoal_5927 : LineageGoal :=
  { ts := 5927, tsShape := [2], tps := [{ rank := 0, tid := 5927 }], tpShapes := [[2]] }

def goal1CutInitGoal_5929 : LineageGoal :=
  { ts := 5929, tsShape := [1024], tps := [{ rank := 0, tid := 5929 }], tpShapes := [[1024]] }

def goal1CutInitGoal_5931 : LineageGoal :=
  { ts := 5931, tsShape := [154880, 1024], tps := [{ rank := 0, tid := 5931 }], tpShapes := [[154880, 1024]] }

def goal_1_cut_initGoals : List LineageGoal :=
  [goal1CutInitGoal_4678, goal1CutInitGoal_5902, goal1CutInitGoal_5903,
   goal1CutInitGoal_5906, goal1CutInitGoal_5911, goal1CutInitGoal_5915,
   goal1CutInitGoal_5920, goal1CutInitGoal_5927, goal1CutInitGoal_5929,
   goal1CutInitGoal_5931, goal1CutIntermediateGoal_5893,
   goal1CutIntermediateGoal_5895, goal1CutIntermediateGoal_5898]

def goal_1_cut_goal : LineageGoal :=
  { ts := 4673, tsShape := [4096], tps := [{ rank := 0, tid := 4673 }],
    tpShapes := [[4096]] }

def goal_1_stmt_cut : Prop :=
  CoarseLineageHoldsWithInit sm_goal_1_cut pm_goal_1_cut goal_1_cut_goal sm_goal_1_cutInitEnv pm_goal_1_cutInitEnv goal_1_cut_initGoals

end TrainVerify.Denote.GeneratedGoals