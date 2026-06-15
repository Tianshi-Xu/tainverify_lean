/- MAIN THEOREM SKELETON: GPT-2 ly4 parallel-training correctness.

   `gpt_main_all_goals : all_goals_stmt` assembles all 312 per-goal correctness
   statements into the full top-level theorem. Two proof layers:
     1. cut-form per goal (`prove_goal_N_cut`, in Goal_N.lean)
     2. cut->full bridge (`goal_N_cut_to_full`)
   Live progress is NOT tracked in this comment (it drifts). Query it instead:
     cut-form proven:  grep -lc 'prove_goal_.*_cut' denote/gpt_ly4_regen/Goal_*.lean | grep -c ':1' (and confirm 0 sorry)
     bridges proven:   inspect goal_N_cut_to_full sites that are not `sorry`
   The THEOREM STRUCTURE (chunk decomposition + combiner) type-checks; remaining
   work = discharge the per-goal sorries (cut proofs + bridges). -/
import denote.gpt_ly4_regen.GeneratedData
import denote.gpt_ly4_regen.Goal_1
import denote.gpt_ly4_regen.Goal_2
import denote.gpt_ly4_regen.Goal_3
import denote.gpt_ly4_regen.Goal_4
import denote.gpt_ly4_regen.Goal_5
import denote.gpt_ly4_regen.Goal_6
import denote.gpt_ly4_regen.Goal_7
import denote.gpt_ly4_regen.Goal_8
import denote.gpt_ly4_regen.Goal_9
import denote.gpt_ly4_regen.Goal_10
import denote.gpt_ly4_regen.Goal_11
import denote.gpt_ly4_regen.Goal_12
import denote.gpt_ly4_regen.Goal_13
import denote.gpt_ly4_regen.Goal_14
import denote.gpt_ly4_regen.Goal_15
import denote.gpt_ly4_regen.Goal_16
import denote.gpt_ly4_regen.Goal_17
import denote.gpt_ly4_regen.Goal_18
import denote.gpt_ly4_regen.Goal_19
import denote.gpt_ly4_regen.Goal_20
import denote.gpt_ly4_regen.Goal_21
import denote.gpt_ly4_regen.Goal_22
import denote.gpt_ly4_regen.Goal_23
import denote.gpt_ly4_regen.Goal_24
import denote.gpt_ly4_regen.Goal_25
import denote.gpt_ly4_regen.Goal_26
import denote.gpt_ly4_regen.Goal_27
import denote.gpt_ly4_regen.Goal_28
import denote.gpt_ly4_regen.Goal_29
import denote.gpt_ly4_regen.Goal_30
import denote.gpt_ly4_regen.Goal_31
import denote.gpt_ly4_regen.Goal_32
import denote.gpt_ly4_regen.Goal_33
import denote.gpt_ly4_regen.Goal_34
import denote.gpt_ly4_regen.Goal_35
import denote.gpt_ly4_regen.Goal_36
import denote.gpt_ly4_regen.Goal_37
import denote.gpt_ly4_regen.Goal_38
import denote.gpt_ly4_regen.Goal_39
import denote.gpt_ly4_regen.Goal_40
import denote.gpt_ly4_regen.Goal_41
import denote.gpt_ly4_regen.Goal_42
import denote.gpt_ly4_regen.Goal_43
import denote.gpt_ly4_regen.Goal_44
import denote.gpt_ly4_regen.Goal_45
import denote.gpt_ly4_regen.Goal_46
import denote.gpt_ly4_regen.Goal_47
import denote.gpt_ly4_regen.Goal_48
import denote.gpt_ly4_regen.Goal_49
import denote.gpt_ly4_regen.Goal_50
import denote.gpt_ly4_regen.Goal_51
import denote.gpt_ly4_regen.Goal_52
import denote.gpt_ly4_regen.Goal_53
import denote.gpt_ly4_regen.Goal_54
import denote.gpt_ly4_regen.Goal_55
import denote.gpt_ly4_regen.Goal_56
import denote.gpt_ly4_regen.Goal_57
import denote.gpt_ly4_regen.Goal_58
import denote.gpt_ly4_regen.Goal_59
import denote.gpt_ly4_regen.Goal_60
import denote.gpt_ly4_regen.Goal_61
import denote.gpt_ly4_regen.Goal_62
import denote.gpt_ly4_regen.Goal_63
import denote.gpt_ly4_regen.Goal_64
import denote.gpt_ly4_regen.Goal_65
import denote.gpt_ly4_regen.Goal_66
import denote.gpt_ly4_regen.Goal_67
import denote.gpt_ly4_regen.Goal_68
import denote.gpt_ly4_regen.Goal_69
import denote.gpt_ly4_regen.Goal_70
import denote.gpt_ly4_regen.Goal_71
import denote.gpt_ly4_regen.Goal_72
import denote.gpt_ly4_regen.Goal_73
import denote.gpt_ly4_regen.Goal_74
import denote.gpt_ly4_regen.Goal_75
import denote.gpt_ly4_regen.Goal_76
import denote.gpt_ly4_regen.Goal_77
import denote.gpt_ly4_regen.Goal_78
import denote.gpt_ly4_regen.Goal_79
import denote.gpt_ly4_regen.Goal_80
import denote.gpt_ly4_regen.Goal_81
import denote.gpt_ly4_regen.Goal_82
import denote.gpt_ly4_regen.Goal_83
import denote.gpt_ly4_regen.Goal_84
import denote.gpt_ly4_regen.Goal_85
import denote.gpt_ly4_regen.Goal_86
import denote.gpt_ly4_regen.Goal_87
import denote.gpt_ly4_regen.Goal_88
import denote.gpt_ly4_regen.Goal_89
import denote.gpt_ly4_regen.Goal_90
import denote.gpt_ly4_regen.Goal_91
import denote.gpt_ly4_regen.Goal_92
import denote.gpt_ly4_regen.Goal_93
import denote.gpt_ly4_regen.Goal_94
import denote.gpt_ly4_regen.Goal_95
import denote.gpt_ly4_regen.Goal_96
import denote.gpt_ly4_regen.Goal_97
import denote.gpt_ly4_regen.Goal_98
import denote.gpt_ly4_regen.Goal_99
import denote.gpt_ly4_regen.Goal_100
import denote.gpt_ly4_regen.Goal_101
import denote.gpt_ly4_regen.Goal_102
import denote.gpt_ly4_regen.Goal_103
import denote.gpt_ly4_regen.Goal_104
import denote.gpt_ly4_regen.Goal_105
import denote.gpt_ly4_regen.Goal_106
import denote.gpt_ly4_regen.Goal_107
import denote.gpt_ly4_regen.Goal_108
import denote.gpt_ly4_regen.Goal_109
import denote.gpt_ly4_regen.Goal_110
import denote.gpt_ly4_regen.Goal_111
import denote.gpt_ly4_regen.Goal_112
import denote.gpt_ly4_regen.Goal_113
import denote.gpt_ly4_regen.Goal_114
import denote.gpt_ly4_regen.Goal_115
import denote.gpt_ly4_regen.Goal_116
import denote.gpt_ly4_regen.Goal_117
import denote.gpt_ly4_regen.Goal_118
import denote.gpt_ly4_regen.Goal_119
import denote.gpt_ly4_regen.Goal_120
import denote.gpt_ly4_regen.Goal_121
import denote.gpt_ly4_regen.Goal_122
import denote.gpt_ly4_regen.Goal_123
import denote.gpt_ly4_regen.Goal_124
import denote.gpt_ly4_regen.Goal_125
import denote.gpt_ly4_regen.Goal_126
import denote.gpt_ly4_regen.Goal_127
import denote.gpt_ly4_regen.Goal_128
import denote.gpt_ly4_regen.Goal_129
import denote.gpt_ly4_regen.Goal_130
import denote.gpt_ly4_regen.Goal_131
import denote.gpt_ly4_regen.Goal_132
import denote.gpt_ly4_regen.Goal_133
import denote.gpt_ly4_regen.Goal_134
import denote.gpt_ly4_regen.Goal_135
import denote.gpt_ly4_regen.Goal_136
import denote.gpt_ly4_regen.Goal_137
import denote.gpt_ly4_regen.Goal_138
import denote.gpt_ly4_regen.Goal_139
import denote.gpt_ly4_regen.Goal_140
import denote.gpt_ly4_regen.Goal_141
import denote.gpt_ly4_regen.Goal_142
import denote.gpt_ly4_regen.Goal_143
import denote.gpt_ly4_regen.Goal_144
import denote.gpt_ly4_regen.Goal_145
import denote.gpt_ly4_regen.Goal_146
import denote.gpt_ly4_regen.Goal_147
import denote.gpt_ly4_regen.Goal_148
import denote.gpt_ly4_regen.Goal_149
import denote.gpt_ly4_regen.Goal_150
import denote.gpt_ly4_regen.Goal_151
import denote.gpt_ly4_regen.Goal_152
import denote.gpt_ly4_regen.Goal_153
import denote.gpt_ly4_regen.Goal_154
import denote.gpt_ly4_regen.Goal_155
import denote.gpt_ly4_regen.Goal_156
import denote.gpt_ly4_regen.Goal_157
import denote.gpt_ly4_regen.Goal_158
import denote.gpt_ly4_regen.Goal_159
import denote.gpt_ly4_regen.Goal_160
import denote.gpt_ly4_regen.Goal_161
import denote.gpt_ly4_regen.Goal_162
import denote.gpt_ly4_regen.Goal_163
import denote.gpt_ly4_regen.Goal_164
import denote.gpt_ly4_regen.Goal_165
import denote.gpt_ly4_regen.Goal_166
import denote.gpt_ly4_regen.Goal_167
import denote.gpt_ly4_regen.Goal_168
import denote.gpt_ly4_regen.Goal_169
import denote.gpt_ly4_regen.Goal_170
import denote.gpt_ly4_regen.Goal_171
import denote.gpt_ly4_regen.Goal_172
import denote.gpt_ly4_regen.Goal_173
import denote.gpt_ly4_regen.Goal_174
import denote.gpt_ly4_regen.Goal_175
import denote.gpt_ly4_regen.Goal_176
import denote.gpt_ly4_regen.Goal_177
import denote.gpt_ly4_regen.Goal_178
import denote.gpt_ly4_regen.Goal_179
import denote.gpt_ly4_regen.Goal_180
import denote.gpt_ly4_regen.Goal_181
import denote.gpt_ly4_regen.Goal_182
import denote.gpt_ly4_regen.Goal_183
import denote.gpt_ly4_regen.Goal_184
import denote.gpt_ly4_regen.Goal_185
import denote.gpt_ly4_regen.Goal_186
import denote.gpt_ly4_regen.Goal_187
import denote.gpt_ly4_regen.Goal_188
import denote.gpt_ly4_regen.Goal_189
import denote.gpt_ly4_regen.Goal_190
import denote.gpt_ly4_regen.Goal_191
import denote.gpt_ly4_regen.Goal_192
import denote.gpt_ly4_regen.Goal_193
import denote.gpt_ly4_regen.Goal_194
import denote.gpt_ly4_regen.Goal_195
import denote.gpt_ly4_regen.Goal_196
import denote.gpt_ly4_regen.Goal_197
import denote.gpt_ly4_regen.Goal_198
import denote.gpt_ly4_regen.Goal_199
import denote.gpt_ly4_regen.Goal_200
import denote.gpt_ly4_regen.Goal_201
import denote.gpt_ly4_regen.Goal_202
import denote.gpt_ly4_regen.Goal_203
import denote.gpt_ly4_regen.Goal_204
import denote.gpt_ly4_regen.Goal_205
import denote.gpt_ly4_regen.Goal_206
import denote.gpt_ly4_regen.Goal_207
import denote.gpt_ly4_regen.Goal_208
import denote.gpt_ly4_regen.Goal_209
import denote.gpt_ly4_regen.Goal_210
import denote.gpt_ly4_regen.Goal_211
import denote.gpt_ly4_regen.Goal_212
import denote.gpt_ly4_regen.Goal_213
import denote.gpt_ly4_regen.Goal_214
import denote.gpt_ly4_regen.Goal_215
import denote.gpt_ly4_regen.Goal_216
import denote.gpt_ly4_regen.Goal_217
import denote.gpt_ly4_regen.Goal_218
import denote.gpt_ly4_regen.Goal_219
import denote.gpt_ly4_regen.Goal_220
import denote.gpt_ly4_regen.Goal_221
import denote.gpt_ly4_regen.Goal_222
import denote.gpt_ly4_regen.Goal_223
import denote.gpt_ly4_regen.Goal_224
import denote.gpt_ly4_regen.Goal_225
import denote.gpt_ly4_regen.Goal_226
import denote.gpt_ly4_regen.Goal_227
import denote.gpt_ly4_regen.Goal_228
import denote.gpt_ly4_regen.Goal_229
import denote.gpt_ly4_regen.Goal_230
import denote.gpt_ly4_regen.Goal_231
import denote.gpt_ly4_regen.Goal_232
import denote.gpt_ly4_regen.Goal_233
import denote.gpt_ly4_regen.Goal_234
import denote.gpt_ly4_regen.Goal_235
import denote.gpt_ly4_regen.Goal_236
import denote.gpt_ly4_regen.Goal_237
import denote.gpt_ly4_regen.Goal_238
import denote.gpt_ly4_regen.Goal_239
import denote.gpt_ly4_regen.Goal_240
import denote.gpt_ly4_regen.Goal_241
import denote.gpt_ly4_regen.Goal_242
import denote.gpt_ly4_regen.Goal_243
import denote.gpt_ly4_regen.Goal_244
import denote.gpt_ly4_regen.Goal_245
import denote.gpt_ly4_regen.Goal_246
import denote.gpt_ly4_regen.Goal_247
import denote.gpt_ly4_regen.Goal_248
import denote.gpt_ly4_regen.Goal_249
import denote.gpt_ly4_regen.Goal_250
import denote.gpt_ly4_regen.Goal_251
import denote.gpt_ly4_regen.Goal_252
import denote.gpt_ly4_regen.Goal_253
import denote.gpt_ly4_regen.Goal_254
import denote.gpt_ly4_regen.Goal_255
import denote.gpt_ly4_regen.Goal_256
import denote.gpt_ly4_regen.Goal_257
import denote.gpt_ly4_regen.Goal_258
import denote.gpt_ly4_regen.Goal_259
import denote.gpt_ly4_regen.Goal_260
import denote.gpt_ly4_regen.Goal_261
import denote.gpt_ly4_regen.Goal_262
import denote.gpt_ly4_regen.Goal_263
import denote.gpt_ly4_regen.Goal_264
import denote.gpt_ly4_regen.Goal_265
import denote.gpt_ly4_regen.Goal_266
import denote.gpt_ly4_regen.Goal_267
import denote.gpt_ly4_regen.Goal_268
import denote.gpt_ly4_regen.Goal_269
import denote.gpt_ly4_regen.Goal_270
import denote.gpt_ly4_regen.Goal_271
import denote.gpt_ly4_regen.Goal_272
import denote.gpt_ly4_regen.Goal_273
import denote.gpt_ly4_regen.Goal_274
import denote.gpt_ly4_regen.Goal_275
import denote.gpt_ly4_regen.Goal_276
import denote.gpt_ly4_regen.Goal_277
import denote.gpt_ly4_regen.Goal_278
import denote.gpt_ly4_regen.Goal_279
import denote.gpt_ly4_regen.Goal_280
import denote.gpt_ly4_regen.Goal_281
import denote.gpt_ly4_regen.Goal_282
import denote.gpt_ly4_regen.Goal_283
import denote.gpt_ly4_regen.Goal_284
import denote.gpt_ly4_regen.Goal_285
import denote.gpt_ly4_regen.Goal_286
import denote.gpt_ly4_regen.Goal_287
import denote.gpt_ly4_regen.Goal_288
import denote.gpt_ly4_regen.Goal_289
import denote.gpt_ly4_regen.Goal_290
import denote.gpt_ly4_regen.Goal_291
import denote.gpt_ly4_regen.Goal_292
import denote.gpt_ly4_regen.Goal_293
import denote.gpt_ly4_regen.Goal_294
import denote.gpt_ly4_regen.Goal_295
import denote.gpt_ly4_regen.Goal_296
import denote.gpt_ly4_regen.Goal_297
import denote.gpt_ly4_regen.Goal_298
import denote.gpt_ly4_regen.Goal_299
import denote.gpt_ly4_regen.Goal_300
import denote.gpt_ly4_regen.Goal_301
import denote.gpt_ly4_regen.Goal_302
import denote.gpt_ly4_regen.Goal_303
import denote.gpt_ly4_regen.Goal_304
import denote.gpt_ly4_regen.Goal_305
import denote.gpt_ly4_regen.Goal_306
import denote.gpt_ly4_regen.Goal_307
import denote.gpt_ly4_regen.Goal_308
import denote.gpt_ly4_regen.Goal_309
import denote.gpt_ly4_regen.Goal_310
import denote.gpt_ly4_regen.Goal_311
import denote.gpt_ly4_regen.Goal_312
import denote.gpt_ly4_regen.SpikeBridge   -- goal_2_cut_to_full (proven)
import denote.gpt_ly4_regen.Goal3Bridge    -- goal_3_cut_to_full (proven)
import denote.gpt_ly4_regen.Goal4Bridge    -- goal_4_cut_to_full (proven, topological induction)
import denote.gpt_ly4_regen.Goal257Bridge  -- goal_257_cut_to_full (proven)
import denote.gpt_ly4_regen.Goal259Bridge  -- goal_259_cut_to_full (proven)
import denote.gpt_ly4_regen.Goal5Bridge    -- goal_5_cut_to_full (proven, bridge slot)
import denote.gpt_ly4_regen.Goal261Bridge  -- goal_261_cut_to_full (proven)
import denote.gpt_ly4_regen.Goal263Bridge  -- goal_263_cut_to_full (proven)
import denote.gpt_ly4_regen.Goal265Bridge  -- goal_265_cut_to_full (proven)

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedGoals

/-! ## cut->full bridges for the 200 cut-proven goals
    goal_2/goal_3 imported (proven). Rest are `sorry` placeholders. -/

theorem goal_1_cut_to_full : goal_1_stmt_cut → goal_1_stmt := by sorry
-- goal_2_cut_to_full : imported (proven)
-- goal_3_cut_to_full : imported (proven)
-- goal_4_cut_to_full : imported (proven, Goal4Bridge)
-- goal_5_cut_to_full : imported (proven, Goal5Bridge)
theorem goal_6_cut_to_full : goal_6_stmt_cut → goal_6_stmt := by sorry
theorem goal_7_cut_to_full : goal_7_stmt_cut → goal_7_stmt := by sorry
theorem goal_8_cut_to_full : goal_8_stmt_cut → goal_8_stmt := by sorry
theorem goal_9_cut_to_full : goal_9_stmt_cut → goal_9_stmt := by sorry
theorem goal_10_cut_to_full : goal_10_stmt_cut → goal_10_stmt := by sorry
theorem goal_11_cut_to_full : goal_11_stmt_cut → goal_11_stmt := by sorry
theorem goal_12_cut_to_full : goal_12_stmt_cut → goal_12_stmt := by sorry
theorem goal_13_cut_to_full : goal_13_stmt_cut → goal_13_stmt := by sorry
theorem goal_14_cut_to_full : goal_14_stmt_cut → goal_14_stmt := by sorry
theorem goal_15_cut_to_full : goal_15_stmt_cut → goal_15_stmt := by sorry
theorem goal_16_cut_to_full : goal_16_stmt_cut → goal_16_stmt := by sorry
theorem goal_19_cut_to_full : goal_19_stmt_cut → goal_19_stmt := by sorry
theorem goal_20_cut_to_full : goal_20_stmt_cut → goal_20_stmt := by sorry
theorem goal_22_cut_to_full : goal_22_stmt_cut → goal_22_stmt := by sorry
theorem goal_23_cut_to_full : goal_23_stmt_cut → goal_23_stmt := by sorry
theorem goal_24_cut_to_full : goal_24_stmt_cut → goal_24_stmt := by sorry
theorem goal_25_cut_to_full : goal_25_stmt_cut → goal_25_stmt := by sorry
theorem goal_26_cut_to_full : goal_26_stmt_cut → goal_26_stmt := by sorry
theorem goal_27_cut_to_full : goal_27_stmt_cut → goal_27_stmt := by sorry
theorem goal_28_cut_to_full : goal_28_stmt_cut → goal_28_stmt := by sorry
theorem goal_29_cut_to_full : goal_29_stmt_cut → goal_29_stmt := by sorry
theorem goal_30_cut_to_full : goal_30_stmt_cut → goal_30_stmt := by sorry
theorem goal_31_cut_to_full : goal_31_stmt_cut → goal_31_stmt := by sorry
theorem goal_32_cut_to_full : goal_32_stmt_cut → goal_32_stmt := by sorry
theorem goal_33_cut_to_full : goal_33_stmt_cut → goal_33_stmt := by sorry
theorem goal_34_cut_to_full : goal_34_stmt_cut → goal_34_stmt := by sorry
theorem goal_35_cut_to_full : goal_35_stmt_cut → goal_35_stmt := by sorry
theorem goal_36_cut_to_full : goal_36_stmt_cut → goal_36_stmt := by sorry
theorem goal_37_cut_to_full : goal_37_stmt_cut → goal_37_stmt := by sorry
theorem goal_38_cut_to_full : goal_38_stmt_cut → goal_38_stmt := by sorry
theorem goal_39_cut_to_full : goal_39_stmt_cut → goal_39_stmt := by sorry
theorem goal_40_cut_to_full : goal_40_stmt_cut → goal_40_stmt := by sorry
theorem goal_41_cut_to_full : goal_41_stmt_cut → goal_41_stmt := by sorry
theorem goal_45_cut_to_full : goal_45_stmt_cut → goal_45_stmt := by sorry
theorem goal_47_cut_to_full : goal_47_stmt_cut → goal_47_stmt := by sorry
theorem goal_48_cut_to_full : goal_48_stmt_cut → goal_48_stmt := by sorry
theorem goal_49_cut_to_full : goal_49_stmt_cut → goal_49_stmt := by sorry
theorem goal_50_cut_to_full : goal_50_stmt_cut → goal_50_stmt := by sorry
theorem goal_51_cut_to_full : goal_51_stmt_cut → goal_51_stmt := by sorry
theorem goal_52_cut_to_full : goal_52_stmt_cut → goal_52_stmt := by sorry
theorem goal_53_cut_to_full : goal_53_stmt_cut → goal_53_stmt := by sorry
theorem goal_54_cut_to_full : goal_54_stmt_cut → goal_54_stmt := by sorry
theorem goal_55_cut_to_full : goal_55_stmt_cut → goal_55_stmt := by sorry
theorem goal_56_cut_to_full : goal_56_stmt_cut → goal_56_stmt := by sorry
theorem goal_57_cut_to_full : goal_57_stmt_cut → goal_57_stmt := by sorry
theorem goal_58_cut_to_full : goal_58_stmt_cut → goal_58_stmt := by sorry
theorem goal_59_cut_to_full : goal_59_stmt_cut → goal_59_stmt := by sorry
theorem goal_60_cut_to_full : goal_60_stmt_cut → goal_60_stmt := by sorry
theorem goal_61_cut_to_full : goal_61_stmt_cut → goal_61_stmt := by sorry
theorem goal_62_cut_to_full : goal_62_stmt_cut → goal_62_stmt := by sorry
theorem goal_63_cut_to_full : goal_63_stmt_cut → goal_63_stmt := by sorry
theorem goal_64_cut_to_full : goal_64_stmt_cut → goal_64_stmt := by sorry
theorem goal_65_cut_to_full : goal_65_stmt_cut → goal_65_stmt := by sorry
theorem goal_70_cut_to_full : goal_70_stmt_cut → goal_70_stmt := by sorry
theorem goal_72_cut_to_full : goal_72_stmt_cut → goal_72_stmt := by sorry
theorem goal_73_cut_to_full : goal_73_stmt_cut → goal_73_stmt := by sorry
theorem goal_74_cut_to_full : goal_74_stmt_cut → goal_74_stmt := by sorry
theorem goal_75_cut_to_full : goal_75_stmt_cut → goal_75_stmt := by sorry
theorem goal_76_cut_to_full : goal_76_stmt_cut → goal_76_stmt := by sorry
theorem goal_78_cut_to_full : goal_78_stmt_cut → goal_78_stmt := by sorry
theorem goal_79_cut_to_full : goal_79_stmt_cut → goal_79_stmt := by sorry
theorem goal_80_cut_to_full : goal_80_stmt_cut → goal_80_stmt := by sorry
theorem goal_81_cut_to_full : goal_81_stmt_cut → goal_81_stmt := by sorry
theorem goal_82_cut_to_full : goal_82_stmt_cut → goal_82_stmt := by sorry
theorem goal_83_cut_to_full : goal_83_stmt_cut → goal_83_stmt := by sorry
theorem goal_84_cut_to_full : goal_84_stmt_cut → goal_84_stmt := by sorry
theorem goal_85_cut_to_full : goal_85_stmt_cut → goal_85_stmt := by sorry
theorem goal_86_cut_to_full : goal_86_stmt_cut → goal_86_stmt := by sorry
theorem goal_87_cut_to_full : goal_87_stmt_cut → goal_87_stmt := by sorry
theorem goal_88_cut_to_full : goal_88_stmt_cut → goal_88_stmt := by sorry
theorem goal_89_cut_to_full : goal_89_stmt_cut → goal_89_stmt := by sorry
theorem goal_90_cut_to_full : goal_90_stmt_cut → goal_90_stmt := by sorry
theorem goal_95_cut_to_full : goal_95_stmt_cut → goal_95_stmt := by sorry
theorem goal_97_cut_to_full : goal_97_stmt_cut → goal_97_stmt := by sorry
theorem goal_98_cut_to_full : goal_98_stmt_cut → goal_98_stmt := by sorry
theorem goal_99_cut_to_full : goal_99_stmt_cut → goal_99_stmt := by sorry
theorem goal_100_cut_to_full : goal_100_stmt_cut → goal_100_stmt := by sorry
theorem goal_101_cut_to_full : goal_101_stmt_cut → goal_101_stmt := by sorry
theorem goal_102_cut_to_full : goal_102_stmt_cut → goal_102_stmt := by sorry
theorem goal_103_cut_to_full : goal_103_stmt_cut → goal_103_stmt := by sorry
theorem goal_104_cut_to_full : goal_104_stmt_cut → goal_104_stmt := by sorry
theorem goal_105_cut_to_full : goal_105_stmt_cut → goal_105_stmt := by sorry
theorem goal_106_cut_to_full : goal_106_stmt_cut → goal_106_stmt := by sorry
theorem goal_107_cut_to_full : goal_107_stmt_cut → goal_107_stmt := by sorry
theorem goal_108_cut_to_full : goal_108_stmt_cut → goal_108_stmt := by sorry
theorem goal_109_cut_to_full : goal_109_stmt_cut → goal_109_stmt := by sorry
theorem goal_111_cut_to_full : goal_111_stmt_cut → goal_111_stmt := by sorry
theorem goal_112_cut_to_full : goal_112_stmt_cut → goal_112_stmt := by sorry
theorem goal_113_cut_to_full : goal_113_stmt_cut → goal_113_stmt := by sorry
theorem goal_115_cut_to_full : goal_115_stmt_cut → goal_115_stmt := by sorry
theorem goal_116_cut_to_full : goal_116_stmt_cut → goal_116_stmt := by sorry
theorem goal_117_cut_to_full : goal_117_stmt_cut → goal_117_stmt := by sorry
theorem goal_118_cut_to_full : goal_118_stmt_cut → goal_118_stmt := by sorry
theorem goal_119_cut_to_full : goal_119_stmt_cut → goal_119_stmt := by sorry
theorem goal_120_cut_to_full : goal_120_stmt_cut → goal_120_stmt := by sorry
theorem goal_121_cut_to_full : goal_121_stmt_cut → goal_121_stmt := by sorry
theorem goal_122_cut_to_full : goal_122_stmt_cut → goal_122_stmt := by sorry
theorem goal_123_cut_to_full : goal_123_stmt_cut → goal_123_stmt := by sorry
theorem goal_124_cut_to_full : goal_124_stmt_cut → goal_124_stmt := by sorry
theorem goal_125_cut_to_full : goal_125_stmt_cut → goal_125_stmt := by sorry
theorem goal_126_cut_to_full : goal_126_stmt_cut → goal_126_stmt := by sorry
theorem goal_127_cut_to_full : goal_127_stmt_cut → goal_127_stmt := by sorry
theorem goal_130_cut_to_full : goal_130_stmt_cut → goal_130_stmt := by sorry
theorem goal_131_cut_to_full : goal_131_stmt_cut → goal_131_stmt := by sorry
theorem goal_133_cut_to_full : goal_133_stmt_cut → goal_133_stmt := by sorry
theorem goal_134_cut_to_full : goal_134_stmt_cut → goal_134_stmt := by sorry
theorem goal_135_cut_to_full : goal_135_stmt_cut → goal_135_stmt := by sorry
theorem goal_138_cut_to_full : goal_138_stmt_cut → goal_138_stmt := by sorry
theorem goal_139_cut_to_full : goal_139_stmt_cut → goal_139_stmt := by sorry
theorem goal_140_cut_to_full : goal_140_stmt_cut → goal_140_stmt := by sorry
theorem goal_141_cut_to_full : goal_141_stmt_cut → goal_141_stmt := by sorry
theorem goal_142_cut_to_full : goal_142_stmt_cut → goal_142_stmt := by sorry
theorem goal_147_cut_to_full : goal_147_stmt_cut → goal_147_stmt := by sorry
theorem goal_148_cut_to_full : goal_148_stmt_cut → goal_148_stmt := by sorry
theorem goal_150_cut_to_full : goal_150_stmt_cut → goal_150_stmt := by sorry
theorem goal_151_cut_to_full : goal_151_stmt_cut → goal_151_stmt := by sorry
theorem goal_152_cut_to_full : goal_152_stmt_cut → goal_152_stmt := by sorry
theorem goal_153_cut_to_full : goal_153_stmt_cut → goal_153_stmt := by sorry
theorem goal_154_cut_to_full : goal_154_stmt_cut → goal_154_stmt := by sorry
theorem goal_155_cut_to_full : goal_155_stmt_cut → goal_155_stmt := by sorry
theorem goal_156_cut_to_full : goal_156_stmt_cut → goal_156_stmt := by sorry
theorem goal_157_cut_to_full : goal_157_stmt_cut → goal_157_stmt := by sorry
theorem goal_158_cut_to_full : goal_158_stmt_cut → goal_158_stmt := by sorry
theorem goal_159_cut_to_full : goal_159_stmt_cut → goal_159_stmt := by sorry
theorem goal_160_cut_to_full : goal_160_stmt_cut → goal_160_stmt := by sorry
theorem goal_161_cut_to_full : goal_161_stmt_cut → goal_161_stmt := by sorry
theorem goal_162_cut_to_full : goal_162_stmt_cut → goal_162_stmt := by sorry
theorem goal_165_cut_to_full : goal_165_stmt_cut → goal_165_stmt := by sorry
theorem goal_166_cut_to_full : goal_166_stmt_cut → goal_166_stmt := by sorry
theorem goal_168_cut_to_full : goal_168_stmt_cut → goal_168_stmt := by sorry
theorem goal_169_cut_to_full : goal_169_stmt_cut → goal_169_stmt := by sorry
theorem goal_170_cut_to_full : goal_170_stmt_cut → goal_170_stmt := by sorry
theorem goal_173_cut_to_full : goal_173_stmt_cut → goal_173_stmt := by sorry
theorem goal_174_cut_to_full : goal_174_stmt_cut → goal_174_stmt := by sorry
theorem goal_175_cut_to_full : goal_175_stmt_cut → goal_175_stmt := by sorry
theorem goal_176_cut_to_full : goal_176_stmt_cut → goal_176_stmt := by sorry
theorem goal_177_cut_to_full : goal_177_stmt_cut → goal_177_stmt := by sorry
theorem goal_178_cut_to_full : goal_178_stmt_cut → goal_178_stmt := by sorry
theorem goal_179_cut_to_full : goal_179_stmt_cut → goal_179_stmt := by sorry
theorem goal_182_cut_to_full : goal_182_stmt_cut → goal_182_stmt := by sorry
theorem goal_183_cut_to_full : goal_183_stmt_cut → goal_183_stmt := by sorry
theorem goal_185_cut_to_full : goal_185_stmt_cut → goal_185_stmt := by sorry
theorem goal_186_cut_to_full : goal_186_stmt_cut → goal_186_stmt := by sorry
theorem goal_187_cut_to_full : goal_187_stmt_cut → goal_187_stmt := by sorry
theorem goal_188_cut_to_full : goal_188_stmt_cut → goal_188_stmt := by sorry
theorem goal_189_cut_to_full : goal_189_stmt_cut → goal_189_stmt := by sorry
theorem goal_190_cut_to_full : goal_190_stmt_cut → goal_190_stmt := by sorry
theorem goal_191_cut_to_full : goal_191_stmt_cut → goal_191_stmt := by sorry
theorem goal_193_cut_to_full : goal_193_stmt_cut → goal_193_stmt := by sorry
theorem goal_194_cut_to_full : goal_194_stmt_cut → goal_194_stmt := by sorry
theorem goal_195_cut_to_full : goal_195_stmt_cut → goal_195_stmt := by sorry
theorem goal_201_cut_to_full : goal_201_stmt_cut → goal_201_stmt := by sorry
theorem goal_203_cut_to_full : goal_203_stmt_cut → goal_203_stmt := by sorry
theorem goal_204_cut_to_full : goal_204_stmt_cut → goal_204_stmt := by sorry
theorem goal_205_cut_to_full : goal_205_stmt_cut → goal_205_stmt := by sorry
theorem goal_208_cut_to_full : goal_208_stmt_cut → goal_208_stmt := by sorry
theorem goal_209_cut_to_full : goal_209_stmt_cut → goal_209_stmt := by sorry
theorem goal_212_cut_to_full : goal_212_stmt_cut → goal_212_stmt := by sorry
theorem goal_217_cut_to_full : goal_217_stmt_cut → goal_217_stmt := by sorry
theorem goal_218_cut_to_full : goal_218_stmt_cut → goal_218_stmt := by sorry
theorem goal_220_cut_to_full : goal_220_stmt_cut → goal_220_stmt := by sorry
theorem goal_221_cut_to_full : goal_221_stmt_cut → goal_221_stmt := by sorry
theorem goal_222_cut_to_full : goal_222_stmt_cut → goal_222_stmt := by sorry
theorem goal_223_cut_to_full : goal_223_stmt_cut → goal_223_stmt := by sorry
theorem goal_224_cut_to_full : goal_224_stmt_cut → goal_224_stmt := by sorry
theorem goal_225_cut_to_full : goal_225_stmt_cut → goal_225_stmt := by sorry
theorem goal_226_cut_to_full : goal_226_stmt_cut → goal_226_stmt := by sorry
theorem goal_228_cut_to_full : goal_228_stmt_cut → goal_228_stmt := by sorry
theorem goal_229_cut_to_full : goal_229_stmt_cut → goal_229_stmt := by sorry
theorem goal_230_cut_to_full : goal_230_stmt_cut → goal_230_stmt := by sorry
theorem goal_236_cut_to_full : goal_236_stmt_cut → goal_236_stmt := by sorry
theorem goal_238_cut_to_full : goal_238_stmt_cut → goal_238_stmt := by sorry
theorem goal_239_cut_to_full : goal_239_stmt_cut → goal_239_stmt := by sorry
theorem goal_240_cut_to_full : goal_240_stmt_cut → goal_240_stmt := by sorry
theorem goal_243_cut_to_full : goal_243_stmt_cut → goal_243_stmt := by sorry
theorem goal_244_cut_to_full : goal_244_stmt_cut → goal_244_stmt := by sorry
theorem goal_247_cut_to_full : goal_247_stmt_cut → goal_247_stmt := by sorry
theorem goal_251_cut_to_full : goal_251_stmt_cut → goal_251_stmt := by sorry
theorem goal_252_cut_to_full : goal_252_stmt_cut → goal_252_stmt := by sorry
theorem goal_253_cut_to_full : goal_253_stmt_cut → goal_253_stmt := by sorry
theorem goal_254_cut_to_full : goal_254_stmt_cut → goal_254_stmt := by sorry
theorem goal_255_cut_to_full : goal_255_stmt_cut → goal_255_stmt := by sorry
theorem goal_256_cut_to_full : goal_256_stmt_cut → goal_256_stmt := by sorry
theorem goal_258_cut_to_full : goal_258_stmt_cut → goal_258_stmt := by sorry
theorem goal_262_cut_to_full : goal_262_stmt_cut → goal_262_stmt := by sorry
theorem goal_264_cut_to_full : goal_264_stmt_cut → goal_264_stmt := by sorry
theorem goal_266_cut_to_full : goal_266_stmt_cut → goal_266_stmt := by sorry
theorem goal_268_cut_to_full : goal_268_stmt_cut → goal_268_stmt := by sorry
theorem goal_272_cut_to_full : goal_272_stmt_cut → goal_272_stmt := by sorry
theorem goal_276_cut_to_full : goal_276_stmt_cut → goal_276_stmt := by sorry
theorem goal_278_cut_to_full : goal_278_stmt_cut → goal_278_stmt := by sorry
theorem goal_280_cut_to_full : goal_280_stmt_cut → goal_280_stmt := by sorry
theorem goal_282_cut_to_full : goal_282_stmt_cut → goal_282_stmt := by sorry
theorem goal_290_cut_to_full : goal_290_stmt_cut → goal_290_stmt := by sorry
theorem goal_296_cut_to_full : goal_296_stmt_cut → goal_296_stmt := by sorry

/-! ## Full-form proofs for all 312 goals -/

theorem goal_1_full : goal_1_stmt := goal_1_cut_to_full prove_goal_1_cut
theorem goal_2_full : goal_2_stmt := goal_2_cut_to_full prove_goal_2_cut
theorem goal_3_full : goal_3_stmt := goal_3_cut_to_full prove_goal_3_cut
theorem goal_4_full : goal_4_stmt := goal_4_cut_to_full prove_goal_4_cut
theorem goal_5_full : goal_5_stmt := goal_5_cut_to_full prove_goal_5_cut
theorem goal_6_full : goal_6_stmt := goal_6_cut_to_full prove_goal_6_cut
theorem goal_7_full : goal_7_stmt := goal_7_cut_to_full prove_goal_7_cut
theorem goal_8_full : goal_8_stmt := goal_8_cut_to_full prove_goal_8_cut
theorem goal_9_full : goal_9_stmt := goal_9_cut_to_full prove_goal_9_cut
theorem goal_10_full : goal_10_stmt := goal_10_cut_to_full prove_goal_10_cut
theorem goal_11_full : goal_11_stmt := goal_11_cut_to_full prove_goal_11_cut
theorem goal_12_full : goal_12_stmt := goal_12_cut_to_full prove_goal_12_cut
theorem goal_13_full : goal_13_stmt := goal_13_cut_to_full prove_goal_13_cut
theorem goal_14_full : goal_14_stmt := goal_14_cut_to_full prove_goal_14_cut
theorem goal_15_full : goal_15_stmt := goal_15_cut_to_full prove_goal_15_cut
theorem goal_16_full : goal_16_stmt := goal_16_cut_to_full prove_goal_16_cut
theorem goal_17_full : goal_17_stmt := by sorry  -- cut-form not yet proven
theorem goal_18_full : goal_18_stmt := by sorry  -- cut-form not yet proven
theorem goal_19_full : goal_19_stmt := goal_19_cut_to_full prove_goal_19_cut
theorem goal_20_full : goal_20_stmt := goal_20_cut_to_full prove_goal_20_cut
theorem goal_21_full : goal_21_stmt := by sorry  -- cut-form not yet proven
theorem goal_22_full : goal_22_stmt := goal_22_cut_to_full prove_goal_22_cut
theorem goal_23_full : goal_23_stmt := goal_23_cut_to_full prove_goal_23_cut
theorem goal_24_full : goal_24_stmt := goal_24_cut_to_full prove_goal_24_cut
theorem goal_25_full : goal_25_stmt := goal_25_cut_to_full prove_goal_25_cut
theorem goal_26_full : goal_26_stmt := goal_26_cut_to_full prove_goal_26_cut
theorem goal_27_full : goal_27_stmt := goal_27_cut_to_full prove_goal_27_cut
theorem goal_28_full : goal_28_stmt := goal_28_cut_to_full prove_goal_28_cut
theorem goal_29_full : goal_29_stmt := goal_29_cut_to_full prove_goal_29_cut
theorem goal_30_full : goal_30_stmt := goal_30_cut_to_full prove_goal_30_cut
theorem goal_31_full : goal_31_stmt := goal_31_cut_to_full prove_goal_31_cut
theorem goal_32_full : goal_32_stmt := goal_32_cut_to_full prove_goal_32_cut
theorem goal_33_full : goal_33_stmt := goal_33_cut_to_full prove_goal_33_cut
theorem goal_34_full : goal_34_stmt := goal_34_cut_to_full prove_goal_34_cut
theorem goal_35_full : goal_35_stmt := goal_35_cut_to_full prove_goal_35_cut
theorem goal_36_full : goal_36_stmt := goal_36_cut_to_full prove_goal_36_cut
theorem goal_37_full : goal_37_stmt := goal_37_cut_to_full prove_goal_37_cut
theorem goal_38_full : goal_38_stmt := goal_38_cut_to_full prove_goal_38_cut
theorem goal_39_full : goal_39_stmt := goal_39_cut_to_full prove_goal_39_cut
theorem goal_40_full : goal_40_stmt := goal_40_cut_to_full prove_goal_40_cut
theorem goal_41_full : goal_41_stmt := goal_41_cut_to_full prove_goal_41_cut
theorem goal_42_full : goal_42_stmt := by sorry  -- cut-form not yet proven
theorem goal_43_full : goal_43_stmt := by sorry  -- cut-form not yet proven
theorem goal_44_full : goal_44_stmt := by sorry  -- cut-form not yet proven
theorem goal_45_full : goal_45_stmt := goal_45_cut_to_full prove_goal_45_cut
theorem goal_46_full : goal_46_stmt := by sorry  -- cut-form not yet proven
theorem goal_47_full : goal_47_stmt := goal_47_cut_to_full prove_goal_47_cut
theorem goal_48_full : goal_48_stmt := goal_48_cut_to_full prove_goal_48_cut
theorem goal_49_full : goal_49_stmt := goal_49_cut_to_full prove_goal_49_cut
theorem goal_50_full : goal_50_stmt := goal_50_cut_to_full prove_goal_50_cut
theorem goal_51_full : goal_51_stmt := goal_51_cut_to_full prove_goal_51_cut
theorem goal_52_full : goal_52_stmt := goal_52_cut_to_full prove_goal_52_cut
theorem goal_53_full : goal_53_stmt := goal_53_cut_to_full prove_goal_53_cut
theorem goal_54_full : goal_54_stmt := goal_54_cut_to_full prove_goal_54_cut
theorem goal_55_full : goal_55_stmt := goal_55_cut_to_full prove_goal_55_cut
theorem goal_56_full : goal_56_stmt := goal_56_cut_to_full prove_goal_56_cut
theorem goal_57_full : goal_57_stmt := goal_57_cut_to_full prove_goal_57_cut
theorem goal_58_full : goal_58_stmt := goal_58_cut_to_full prove_goal_58_cut
theorem goal_59_full : goal_59_stmt := goal_59_cut_to_full prove_goal_59_cut
theorem goal_60_full : goal_60_stmt := goal_60_cut_to_full prove_goal_60_cut
theorem goal_61_full : goal_61_stmt := goal_61_cut_to_full prove_goal_61_cut
theorem goal_62_full : goal_62_stmt := goal_62_cut_to_full prove_goal_62_cut
theorem goal_63_full : goal_63_stmt := goal_63_cut_to_full prove_goal_63_cut
theorem goal_64_full : goal_64_stmt := goal_64_cut_to_full prove_goal_64_cut
theorem goal_65_full : goal_65_stmt := goal_65_cut_to_full prove_goal_65_cut
theorem goal_66_full : goal_66_stmt := by sorry  -- cut-form not yet proven
theorem goal_67_full : goal_67_stmt := by sorry  -- cut-form not yet proven
theorem goal_68_full : goal_68_stmt := by sorry  -- cut-form not yet proven
theorem goal_69_full : goal_69_stmt := by sorry  -- cut-form not yet proven
theorem goal_70_full : goal_70_stmt := goal_70_cut_to_full prove_goal_70_cut
theorem goal_71_full : goal_71_stmt := by sorry  -- cut-form not yet proven
theorem goal_72_full : goal_72_stmt := goal_72_cut_to_full prove_goal_72_cut
theorem goal_73_full : goal_73_stmt := goal_73_cut_to_full prove_goal_73_cut
theorem goal_74_full : goal_74_stmt := goal_74_cut_to_full prove_goal_74_cut
theorem goal_75_full : goal_75_stmt := goal_75_cut_to_full prove_goal_75_cut
theorem goal_76_full : goal_76_stmt := goal_76_cut_to_full prove_goal_76_cut
theorem goal_77_full : goal_77_stmt := by sorry  -- cut-form not yet proven
theorem goal_78_full : goal_78_stmt := goal_78_cut_to_full prove_goal_78_cut
theorem goal_79_full : goal_79_stmt := goal_79_cut_to_full prove_goal_79_cut
theorem goal_80_full : goal_80_stmt := goal_80_cut_to_full prove_goal_80_cut
theorem goal_81_full : goal_81_stmt := goal_81_cut_to_full prove_goal_81_cut
theorem goal_82_full : goal_82_stmt := goal_82_cut_to_full prove_goal_82_cut
theorem goal_83_full : goal_83_stmt := goal_83_cut_to_full prove_goal_83_cut
theorem goal_84_full : goal_84_stmt := goal_84_cut_to_full prove_goal_84_cut
theorem goal_85_full : goal_85_stmt := goal_85_cut_to_full prove_goal_85_cut
theorem goal_86_full : goal_86_stmt := goal_86_cut_to_full prove_goal_86_cut
theorem goal_87_full : goal_87_stmt := goal_87_cut_to_full prove_goal_87_cut
theorem goal_88_full : goal_88_stmt := goal_88_cut_to_full prove_goal_88_cut
theorem goal_89_full : goal_89_stmt := goal_89_cut_to_full prove_goal_89_cut
theorem goal_90_full : goal_90_stmt := goal_90_cut_to_full prove_goal_90_cut
theorem goal_91_full : goal_91_stmt := by sorry  -- cut-form not yet proven
theorem goal_92_full : goal_92_stmt := by sorry  -- cut-form not yet proven
theorem goal_93_full : goal_93_stmt := by sorry  -- cut-form not yet proven
theorem goal_94_full : goal_94_stmt := by sorry  -- cut-form not yet proven
theorem goal_95_full : goal_95_stmt := goal_95_cut_to_full prove_goal_95_cut
theorem goal_96_full : goal_96_stmt := by sorry  -- cut-form not yet proven
theorem goal_97_full : goal_97_stmt := goal_97_cut_to_full prove_goal_97_cut
theorem goal_98_full : goal_98_stmt := goal_98_cut_to_full prove_goal_98_cut
theorem goal_99_full : goal_99_stmt := goal_99_cut_to_full prove_goal_99_cut
theorem goal_100_full : goal_100_stmt := goal_100_cut_to_full prove_goal_100_cut
theorem goal_101_full : goal_101_stmt := goal_101_cut_to_full prove_goal_101_cut
theorem goal_102_full : goal_102_stmt := goal_102_cut_to_full prove_goal_102_cut
theorem goal_103_full : goal_103_stmt := goal_103_cut_to_full prove_goal_103_cut
theorem goal_104_full : goal_104_stmt := goal_104_cut_to_full prove_goal_104_cut
theorem goal_105_full : goal_105_stmt := goal_105_cut_to_full prove_goal_105_cut
theorem goal_106_full : goal_106_stmt := goal_106_cut_to_full prove_goal_106_cut
theorem goal_107_full : goal_107_stmt := goal_107_cut_to_full prove_goal_107_cut
theorem goal_108_full : goal_108_stmt := goal_108_cut_to_full prove_goal_108_cut
theorem goal_109_full : goal_109_stmt := goal_109_cut_to_full prove_goal_109_cut
theorem goal_110_full : goal_110_stmt := by sorry  -- cut-form not yet proven
theorem goal_111_full : goal_111_stmt := goal_111_cut_to_full prove_goal_111_cut
theorem goal_112_full : goal_112_stmt := goal_112_cut_to_full prove_goal_112_cut
theorem goal_113_full : goal_113_stmt := goal_113_cut_to_full prove_goal_113_cut
theorem goal_114_full : goal_114_stmt := by sorry  -- cut-form not yet proven
theorem goal_115_full : goal_115_stmt := goal_115_cut_to_full prove_goal_115_cut
theorem goal_116_full : goal_116_stmt := goal_116_cut_to_full prove_goal_116_cut
theorem goal_117_full : goal_117_stmt := goal_117_cut_to_full prove_goal_117_cut
theorem goal_118_full : goal_118_stmt := goal_118_cut_to_full prove_goal_118_cut
theorem goal_119_full : goal_119_stmt := goal_119_cut_to_full prove_goal_119_cut
theorem goal_120_full : goal_120_stmt := goal_120_cut_to_full prove_goal_120_cut
theorem goal_121_full : goal_121_stmt := goal_121_cut_to_full prove_goal_121_cut
theorem goal_122_full : goal_122_stmt := goal_122_cut_to_full prove_goal_122_cut
theorem goal_123_full : goal_123_stmt := goal_123_cut_to_full prove_goal_123_cut
theorem goal_124_full : goal_124_stmt := goal_124_cut_to_full prove_goal_124_cut
theorem goal_125_full : goal_125_stmt := goal_125_cut_to_full prove_goal_125_cut
theorem goal_126_full : goal_126_stmt := goal_126_cut_to_full prove_goal_126_cut
theorem goal_127_full : goal_127_stmt := goal_127_cut_to_full prove_goal_127_cut
theorem goal_128_full : goal_128_stmt := by sorry  -- cut-form not yet proven
theorem goal_129_full : goal_129_stmt := by sorry  -- cut-form not yet proven
theorem goal_130_full : goal_130_stmt := goal_130_cut_to_full prove_goal_130_cut
theorem goal_131_full : goal_131_stmt := goal_131_cut_to_full prove_goal_131_cut
theorem goal_132_full : goal_132_stmt := by sorry  -- cut-form not yet proven
theorem goal_133_full : goal_133_stmt := goal_133_cut_to_full prove_goal_133_cut
theorem goal_134_full : goal_134_stmt := goal_134_cut_to_full prove_goal_134_cut
theorem goal_135_full : goal_135_stmt := goal_135_cut_to_full prove_goal_135_cut
theorem goal_136_full : goal_136_stmt := by sorry  -- cut-form not yet proven
theorem goal_137_full : goal_137_stmt := by sorry  -- cut-form not yet proven
theorem goal_138_full : goal_138_stmt := goal_138_cut_to_full prove_goal_138_cut
theorem goal_139_full : goal_139_stmt := goal_139_cut_to_full prove_goal_139_cut
theorem goal_140_full : goal_140_stmt := goal_140_cut_to_full prove_goal_140_cut
theorem goal_141_full : goal_141_stmt := goal_141_cut_to_full prove_goal_141_cut
theorem goal_142_full : goal_142_stmt := goal_142_cut_to_full prove_goal_142_cut
theorem goal_143_full : goal_143_stmt := by sorry  -- cut-form not yet proven
theorem goal_144_full : goal_144_stmt := by sorry  -- cut-form not yet proven
theorem goal_145_full : goal_145_stmt := by sorry  -- cut-form not yet proven
theorem goal_146_full : goal_146_stmt := by sorry  -- cut-form not yet proven
theorem goal_147_full : goal_147_stmt := goal_147_cut_to_full prove_goal_147_cut
theorem goal_148_full : goal_148_stmt := goal_148_cut_to_full prove_goal_148_cut
theorem goal_149_full : goal_149_stmt := by sorry  -- cut-form not yet proven
theorem goal_150_full : goal_150_stmt := goal_150_cut_to_full prove_goal_150_cut
theorem goal_151_full : goal_151_stmt := goal_151_cut_to_full prove_goal_151_cut
theorem goal_152_full : goal_152_stmt := goal_152_cut_to_full prove_goal_152_cut
theorem goal_153_full : goal_153_stmt := goal_153_cut_to_full prove_goal_153_cut
theorem goal_154_full : goal_154_stmt := goal_154_cut_to_full prove_goal_154_cut
theorem goal_155_full : goal_155_stmt := goal_155_cut_to_full prove_goal_155_cut
theorem goal_156_full : goal_156_stmt := goal_156_cut_to_full prove_goal_156_cut
theorem goal_157_full : goal_157_stmt := goal_157_cut_to_full prove_goal_157_cut
theorem goal_158_full : goal_158_stmt := goal_158_cut_to_full prove_goal_158_cut
theorem goal_159_full : goal_159_stmt := goal_159_cut_to_full prove_goal_159_cut
theorem goal_160_full : goal_160_stmt := goal_160_cut_to_full prove_goal_160_cut
theorem goal_161_full : goal_161_stmt := goal_161_cut_to_full prove_goal_161_cut
theorem goal_162_full : goal_162_stmt := goal_162_cut_to_full prove_goal_162_cut
theorem goal_163_full : goal_163_stmt := by sorry  -- cut-form not yet proven
theorem goal_164_full : goal_164_stmt := by sorry  -- cut-form not yet proven
theorem goal_165_full : goal_165_stmt := goal_165_cut_to_full prove_goal_165_cut
theorem goal_166_full : goal_166_stmt := goal_166_cut_to_full prove_goal_166_cut
theorem goal_167_full : goal_167_stmt := by sorry  -- cut-form not yet proven
theorem goal_168_full : goal_168_stmt := goal_168_cut_to_full prove_goal_168_cut
theorem goal_169_full : goal_169_stmt := goal_169_cut_to_full prove_goal_169_cut
theorem goal_170_full : goal_170_stmt := goal_170_cut_to_full prove_goal_170_cut
theorem goal_171_full : goal_171_stmt := by sorry  -- cut-form not yet proven
theorem goal_172_full : goal_172_stmt := by sorry  -- cut-form not yet proven
theorem goal_173_full : goal_173_stmt := goal_173_cut_to_full prove_goal_173_cut
theorem goal_174_full : goal_174_stmt := goal_174_cut_to_full prove_goal_174_cut
theorem goal_175_full : goal_175_stmt := goal_175_cut_to_full prove_goal_175_cut
theorem goal_176_full : goal_176_stmt := goal_176_cut_to_full prove_goal_176_cut
theorem goal_177_full : goal_177_stmt := goal_177_cut_to_full prove_goal_177_cut
theorem goal_178_full : goal_178_stmt := goal_178_cut_to_full prove_goal_178_cut
theorem goal_179_full : goal_179_stmt := goal_179_cut_to_full prove_goal_179_cut
theorem goal_180_full : goal_180_stmt := by sorry  -- cut-form not yet proven
theorem goal_181_full : goal_181_stmt := by sorry  -- cut-form not yet proven
theorem goal_182_full : goal_182_stmt := goal_182_cut_to_full prove_goal_182_cut
theorem goal_183_full : goal_183_stmt := goal_183_cut_to_full prove_goal_183_cut
theorem goal_184_full : goal_184_stmt := by sorry  -- cut-form not yet proven
theorem goal_185_full : goal_185_stmt := goal_185_cut_to_full prove_goal_185_cut
theorem goal_186_full : goal_186_stmt := goal_186_cut_to_full prove_goal_186_cut
theorem goal_187_full : goal_187_stmt := goal_187_cut_to_full prove_goal_187_cut
theorem goal_188_full : goal_188_stmt := goal_188_cut_to_full prove_goal_188_cut
theorem goal_189_full : goal_189_stmt := goal_189_cut_to_full prove_goal_189_cut
theorem goal_190_full : goal_190_stmt := goal_190_cut_to_full prove_goal_190_cut
theorem goal_191_full : goal_191_stmt := goal_191_cut_to_full prove_goal_191_cut
theorem goal_192_full : goal_192_stmt := by sorry  -- cut-form not yet proven
theorem goal_193_full : goal_193_stmt := goal_193_cut_to_full prove_goal_193_cut
theorem goal_194_full : goal_194_stmt := goal_194_cut_to_full prove_goal_194_cut
theorem goal_195_full : goal_195_stmt := goal_195_cut_to_full prove_goal_195_cut
theorem goal_196_full : goal_196_stmt := by sorry  -- cut-form not yet proven
theorem goal_197_full : goal_197_stmt := by sorry  -- cut-form not yet proven
theorem goal_198_full : goal_198_stmt := by sorry  -- cut-form not yet proven
theorem goal_199_full : goal_199_stmt := by sorry  -- cut-form not yet proven
theorem goal_200_full : goal_200_stmt := by sorry  -- cut-form not yet proven
theorem goal_201_full : goal_201_stmt := goal_201_cut_to_full prove_goal_201_cut
theorem goal_202_full : goal_202_stmt := by sorry  -- cut-form not yet proven
theorem goal_203_full : goal_203_stmt := goal_203_cut_to_full prove_goal_203_cut
theorem goal_204_full : goal_204_stmt := goal_204_cut_to_full prove_goal_204_cut
theorem goal_205_full : goal_205_stmt := goal_205_cut_to_full prove_goal_205_cut
theorem goal_206_full : goal_206_stmt := by sorry  -- cut-form not yet proven
theorem goal_207_full : goal_207_stmt := by sorry  -- cut-form not yet proven
theorem goal_208_full : goal_208_stmt := goal_208_cut_to_full prove_goal_208_cut
theorem goal_209_full : goal_209_stmt := goal_209_cut_to_full prove_goal_209_cut
theorem goal_210_full : goal_210_stmt := by sorry  -- cut-form not yet proven
theorem goal_211_full : goal_211_stmt := by sorry  -- cut-form not yet proven
theorem goal_212_full : goal_212_stmt := goal_212_cut_to_full prove_goal_212_cut
theorem goal_213_full : goal_213_stmt := by sorry  -- cut-form not yet proven
theorem goal_214_full : goal_214_stmt := by sorry  -- cut-form not yet proven
theorem goal_215_full : goal_215_stmt := by sorry  -- cut-form not yet proven
theorem goal_216_full : goal_216_stmt := by sorry  -- cut-form not yet proven
theorem goal_217_full : goal_217_stmt := goal_217_cut_to_full prove_goal_217_cut
theorem goal_218_full : goal_218_stmt := goal_218_cut_to_full prove_goal_218_cut
theorem goal_219_full : goal_219_stmt := by sorry  -- cut-form not yet proven
theorem goal_220_full : goal_220_stmt := goal_220_cut_to_full prove_goal_220_cut
theorem goal_221_full : goal_221_stmt := goal_221_cut_to_full prove_goal_221_cut
theorem goal_222_full : goal_222_stmt := goal_222_cut_to_full prove_goal_222_cut
theorem goal_223_full : goal_223_stmt := goal_223_cut_to_full prove_goal_223_cut
theorem goal_224_full : goal_224_stmt := goal_224_cut_to_full prove_goal_224_cut
theorem goal_225_full : goal_225_stmt := goal_225_cut_to_full prove_goal_225_cut
theorem goal_226_full : goal_226_stmt := goal_226_cut_to_full prove_goal_226_cut
theorem goal_227_full : goal_227_stmt := by sorry  -- cut-form not yet proven
theorem goal_228_full : goal_228_stmt := goal_228_cut_to_full prove_goal_228_cut
theorem goal_229_full : goal_229_stmt := goal_229_cut_to_full prove_goal_229_cut
theorem goal_230_full : goal_230_stmt := goal_230_cut_to_full prove_goal_230_cut
theorem goal_231_full : goal_231_stmt := by sorry  -- cut-form not yet proven
theorem goal_232_full : goal_232_stmt := by sorry  -- cut-form not yet proven
theorem goal_233_full : goal_233_stmt := by sorry  -- cut-form not yet proven
theorem goal_234_full : goal_234_stmt := by sorry  -- cut-form not yet proven
theorem goal_235_full : goal_235_stmt := by sorry  -- cut-form not yet proven
theorem goal_236_full : goal_236_stmt := goal_236_cut_to_full prove_goal_236_cut
theorem goal_237_full : goal_237_stmt := by sorry  -- cut-form not yet proven
theorem goal_238_full : goal_238_stmt := goal_238_cut_to_full prove_goal_238_cut
theorem goal_239_full : goal_239_stmt := goal_239_cut_to_full prove_goal_239_cut
theorem goal_240_full : goal_240_stmt := goal_240_cut_to_full prove_goal_240_cut
theorem goal_241_full : goal_241_stmt := by sorry  -- cut-form not yet proven
theorem goal_242_full : goal_242_stmt := by sorry  -- cut-form not yet proven
theorem goal_243_full : goal_243_stmt := goal_243_cut_to_full prove_goal_243_cut
theorem goal_244_full : goal_244_stmt := goal_244_cut_to_full prove_goal_244_cut
theorem goal_245_full : goal_245_stmt := by sorry  -- cut-form not yet proven
theorem goal_246_full : goal_246_stmt := by sorry  -- cut-form not yet proven
theorem goal_247_full : goal_247_stmt := goal_247_cut_to_full prove_goal_247_cut
theorem goal_248_full : goal_248_stmt := by sorry  -- cut-form not yet proven
theorem goal_249_full : goal_249_stmt := by sorry  -- cut-form not yet proven
theorem goal_250_full : goal_250_stmt := by sorry  -- cut-form not yet proven
theorem goal_251_full : goal_251_stmt := goal_251_cut_to_full prove_goal_251_cut
theorem goal_252_full : goal_252_stmt := goal_252_cut_to_full prove_goal_252_cut
theorem goal_253_full : goal_253_stmt := goal_253_cut_to_full prove_goal_253_cut
theorem goal_254_full : goal_254_stmt := goal_254_cut_to_full prove_goal_254_cut
theorem goal_255_full : goal_255_stmt := goal_255_cut_to_full prove_goal_255_cut
theorem goal_256_full : goal_256_stmt := goal_256_cut_to_full prove_goal_256_cut
theorem goal_257_full : goal_257_stmt := goal_257_cut_to_full prove_goal_257_cut
theorem goal_258_full : goal_258_stmt := goal_258_cut_to_full prove_goal_258_cut
theorem goal_259_full : goal_259_stmt := goal_259_cut_to_full prove_goal_259_cut
theorem goal_260_full : goal_260_stmt := by sorry  -- cut-form not yet proven
theorem goal_261_full : goal_261_stmt := goal_261_cut_to_full prove_goal_261_cut
theorem goal_262_full : goal_262_stmt := goal_262_cut_to_full prove_goal_262_cut
theorem goal_263_full : goal_263_stmt := goal_263_cut_to_full prove_goal_263_cut
theorem goal_264_full : goal_264_stmt := goal_264_cut_to_full prove_goal_264_cut
theorem goal_265_full : goal_265_stmt := goal_265_cut_to_full prove_goal_265_cut
theorem goal_266_full : goal_266_stmt := goal_266_cut_to_full prove_goal_266_cut
theorem goal_267_full : goal_267_stmt := by sorry  -- cut-form not yet proven
theorem goal_268_full : goal_268_stmt := goal_268_cut_to_full prove_goal_268_cut
theorem goal_269_full : goal_269_stmt := by sorry  -- cut-form not yet proven
theorem goal_270_full : goal_270_stmt := by sorry  -- cut-form not yet proven
theorem goal_271_full : goal_271_stmt := by sorry  -- cut-form not yet proven
theorem goal_272_full : goal_272_stmt := goal_272_cut_to_full prove_goal_272_cut
theorem goal_273_full : goal_273_stmt := by sorry  -- cut-form not yet proven
theorem goal_274_full : goal_274_stmt := by sorry  -- cut-form not yet proven
theorem goal_275_full : goal_275_stmt := by sorry  -- cut-form not yet proven
theorem goal_276_full : goal_276_stmt := goal_276_cut_to_full prove_goal_276_cut
theorem goal_277_full : goal_277_stmt := by sorry  -- cut-form not yet proven
theorem goal_278_full : goal_278_stmt := goal_278_cut_to_full prove_goal_278_cut
theorem goal_279_full : goal_279_stmt := by sorry  -- cut-form not yet proven
theorem goal_280_full : goal_280_stmt := goal_280_cut_to_full prove_goal_280_cut
theorem goal_281_full : goal_281_stmt := by sorry  -- cut-form not yet proven
theorem goal_282_full : goal_282_stmt := goal_282_cut_to_full prove_goal_282_cut
theorem goal_283_full : goal_283_stmt := by sorry  -- cut-form not yet proven
theorem goal_284_full : goal_284_stmt := by sorry  -- cut-form not yet proven
theorem goal_285_full : goal_285_stmt := by sorry  -- cut-form not yet proven
theorem goal_286_full : goal_286_stmt := by sorry  -- cut-form not yet proven
theorem goal_287_full : goal_287_stmt := by sorry  -- cut-form not yet proven
theorem goal_288_full : goal_288_stmt := by sorry  -- cut-form not yet proven
theorem goal_289_full : goal_289_stmt := by sorry  -- cut-form not yet proven
theorem goal_290_full : goal_290_stmt := goal_290_cut_to_full prove_goal_290_cut
theorem goal_291_full : goal_291_stmt := by sorry  -- cut-form not yet proven
theorem goal_292_full : goal_292_stmt := by sorry  -- cut-form not yet proven
theorem goal_293_full : goal_293_stmt := by sorry  -- cut-form not yet proven
theorem goal_294_full : goal_294_stmt := by sorry  -- cut-form not yet proven
theorem goal_295_full : goal_295_stmt := by sorry  -- cut-form not yet proven
theorem goal_296_full : goal_296_stmt := goal_296_cut_to_full prove_goal_296_cut
theorem goal_297_full : goal_297_stmt := by sorry  -- cut-form not yet proven
theorem goal_298_full : goal_298_stmt := by sorry  -- cut-form not yet proven
theorem goal_299_full : goal_299_stmt := by sorry  -- cut-form not yet proven
theorem goal_300_full : goal_300_stmt := by sorry  -- cut-form not yet proven
theorem goal_301_full : goal_301_stmt := by sorry  -- cut-form not yet proven
theorem goal_302_full : goal_302_stmt := by sorry  -- cut-form not yet proven
theorem goal_303_full : goal_303_stmt := by sorry  -- cut-form not yet proven
theorem goal_304_full : goal_304_stmt := by sorry  -- cut-form not yet proven
theorem goal_305_full : goal_305_stmt := by sorry  -- cut-form not yet proven
theorem goal_306_full : goal_306_stmt := by sorry  -- cut-form not yet proven
theorem goal_307_full : goal_307_stmt := by sorry  -- cut-form not yet proven
theorem goal_308_full : goal_308_stmt := by sorry  -- cut-form not yet proven
theorem goal_309_full : goal_309_stmt := by sorry  -- cut-form not yet proven
theorem goal_310_full : goal_310_stmt := by sorry  -- cut-form not yet proven
theorem goal_311_full : goal_311_stmt := by sorry  -- cut-form not yet proven
theorem goal_312_full : goal_312_stmt := by sorry  -- cut-form not yet proven

/-! ## Per-goal predicate + per-chunk lemmas (8 goals each, 39 chunks) -/
abbrev P (g : LineageGoal) : Prop := CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals

theorem chunk_1_holds : ∀ g ∈ goalChunk_1, P g := by
  intro g hg
  simp only [goalChunk_1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_1_full
  · exact goal_2_full
  · exact goal_3_full
  · exact goal_4_full
  · exact goal_5_full
  · exact goal_6_full
  · exact goal_7_full
  · exact goal_8_full
theorem chunk_2_holds : ∀ g ∈ goalChunk_2, P g := by
  intro g hg
  simp only [goalChunk_2, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_9_full
  · exact goal_10_full
  · exact goal_11_full
  · exact goal_12_full
  · exact goal_13_full
  · exact goal_14_full
  · exact goal_15_full
  · exact goal_16_full
theorem chunk_3_holds : ∀ g ∈ goalChunk_3, P g := by
  intro g hg
  simp only [goalChunk_3, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_17_full
  · exact goal_18_full
  · exact goal_19_full
  · exact goal_20_full
  · exact goal_21_full
  · exact goal_22_full
  · exact goal_23_full
  · exact goal_24_full
theorem chunk_4_holds : ∀ g ∈ goalChunk_4, P g := by
  intro g hg
  simp only [goalChunk_4, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_25_full
  · exact goal_26_full
  · exact goal_27_full
  · exact goal_28_full
  · exact goal_29_full
  · exact goal_30_full
  · exact goal_31_full
  · exact goal_32_full
theorem chunk_5_holds : ∀ g ∈ goalChunk_5, P g := by
  intro g hg
  simp only [goalChunk_5, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_33_full
  · exact goal_34_full
  · exact goal_35_full
  · exact goal_36_full
  · exact goal_37_full
  · exact goal_38_full
  · exact goal_39_full
  · exact goal_40_full
theorem chunk_6_holds : ∀ g ∈ goalChunk_6, P g := by
  intro g hg
  simp only [goalChunk_6, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_41_full
  · exact goal_42_full
  · exact goal_43_full
  · exact goal_44_full
  · exact goal_45_full
  · exact goal_46_full
  · exact goal_47_full
  · exact goal_48_full
theorem chunk_7_holds : ∀ g ∈ goalChunk_7, P g := by
  intro g hg
  simp only [goalChunk_7, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_49_full
  · exact goal_50_full
  · exact goal_51_full
  · exact goal_52_full
  · exact goal_53_full
  · exact goal_54_full
  · exact goal_55_full
  · exact goal_56_full
theorem chunk_8_holds : ∀ g ∈ goalChunk_8, P g := by
  intro g hg
  simp only [goalChunk_8, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_57_full
  · exact goal_58_full
  · exact goal_59_full
  · exact goal_60_full
  · exact goal_61_full
  · exact goal_62_full
  · exact goal_63_full
  · exact goal_64_full
theorem chunk_9_holds : ∀ g ∈ goalChunk_9, P g := by
  intro g hg
  simp only [goalChunk_9, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_65_full
  · exact goal_66_full
  · exact goal_67_full
  · exact goal_68_full
  · exact goal_69_full
  · exact goal_70_full
  · exact goal_71_full
  · exact goal_72_full
theorem chunk_10_holds : ∀ g ∈ goalChunk_10, P g := by
  intro g hg
  simp only [goalChunk_10, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_73_full
  · exact goal_74_full
  · exact goal_75_full
  · exact goal_76_full
  · exact goal_77_full
  · exact goal_78_full
  · exact goal_79_full
  · exact goal_80_full
theorem chunk_11_holds : ∀ g ∈ goalChunk_11, P g := by
  intro g hg
  simp only [goalChunk_11, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_81_full
  · exact goal_82_full
  · exact goal_83_full
  · exact goal_84_full
  · exact goal_85_full
  · exact goal_86_full
  · exact goal_87_full
  · exact goal_88_full
theorem chunk_12_holds : ∀ g ∈ goalChunk_12, P g := by
  intro g hg
  simp only [goalChunk_12, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_89_full
  · exact goal_90_full
  · exact goal_91_full
  · exact goal_92_full
  · exact goal_93_full
  · exact goal_94_full
  · exact goal_95_full
  · exact goal_96_full
theorem chunk_13_holds : ∀ g ∈ goalChunk_13, P g := by
  intro g hg
  simp only [goalChunk_13, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_97_full
  · exact goal_98_full
  · exact goal_99_full
  · exact goal_100_full
  · exact goal_101_full
  · exact goal_102_full
  · exact goal_103_full
  · exact goal_104_full
theorem chunk_14_holds : ∀ g ∈ goalChunk_14, P g := by
  intro g hg
  simp only [goalChunk_14, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_105_full
  · exact goal_106_full
  · exact goal_107_full
  · exact goal_108_full
  · exact goal_109_full
  · exact goal_110_full
  · exact goal_111_full
  · exact goal_112_full
theorem chunk_15_holds : ∀ g ∈ goalChunk_15, P g := by
  intro g hg
  simp only [goalChunk_15, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_113_full
  · exact goal_114_full
  · exact goal_115_full
  · exact goal_116_full
  · exact goal_117_full
  · exact goal_118_full
  · exact goal_119_full
  · exact goal_120_full
theorem chunk_16_holds : ∀ g ∈ goalChunk_16, P g := by
  intro g hg
  simp only [goalChunk_16, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_121_full
  · exact goal_122_full
  · exact goal_123_full
  · exact goal_124_full
  · exact goal_125_full
  · exact goal_126_full
  · exact goal_127_full
  · exact goal_128_full
theorem chunk_17_holds : ∀ g ∈ goalChunk_17, P g := by
  intro g hg
  simp only [goalChunk_17, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_129_full
  · exact goal_130_full
  · exact goal_131_full
  · exact goal_132_full
  · exact goal_133_full
  · exact goal_134_full
  · exact goal_135_full
  · exact goal_136_full
theorem chunk_18_holds : ∀ g ∈ goalChunk_18, P g := by
  intro g hg
  simp only [goalChunk_18, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_137_full
  · exact goal_138_full
  · exact goal_139_full
  · exact goal_140_full
  · exact goal_141_full
  · exact goal_142_full
  · exact goal_143_full
  · exact goal_144_full
theorem chunk_19_holds : ∀ g ∈ goalChunk_19, P g := by
  intro g hg
  simp only [goalChunk_19, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_145_full
  · exact goal_146_full
  · exact goal_147_full
  · exact goal_148_full
  · exact goal_149_full
  · exact goal_150_full
  · exact goal_151_full
  · exact goal_152_full
theorem chunk_20_holds : ∀ g ∈ goalChunk_20, P g := by
  intro g hg
  simp only [goalChunk_20, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_153_full
  · exact goal_154_full
  · exact goal_155_full
  · exact goal_156_full
  · exact goal_157_full
  · exact goal_158_full
  · exact goal_159_full
  · exact goal_160_full
theorem chunk_21_holds : ∀ g ∈ goalChunk_21, P g := by
  intro g hg
  simp only [goalChunk_21, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_161_full
  · exact goal_162_full
  · exact goal_163_full
  · exact goal_164_full
  · exact goal_165_full
  · exact goal_166_full
  · exact goal_167_full
  · exact goal_168_full
theorem chunk_22_holds : ∀ g ∈ goalChunk_22, P g := by
  intro g hg
  simp only [goalChunk_22, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_169_full
  · exact goal_170_full
  · exact goal_171_full
  · exact goal_172_full
  · exact goal_173_full
  · exact goal_174_full
  · exact goal_175_full
  · exact goal_176_full
theorem chunk_23_holds : ∀ g ∈ goalChunk_23, P g := by
  intro g hg
  simp only [goalChunk_23, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_177_full
  · exact goal_178_full
  · exact goal_179_full
  · exact goal_180_full
  · exact goal_181_full
  · exact goal_182_full
  · exact goal_183_full
  · exact goal_184_full
theorem chunk_24_holds : ∀ g ∈ goalChunk_24, P g := by
  intro g hg
  simp only [goalChunk_24, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_185_full
  · exact goal_186_full
  · exact goal_187_full
  · exact goal_188_full
  · exact goal_189_full
  · exact goal_190_full
  · exact goal_191_full
  · exact goal_192_full
theorem chunk_25_holds : ∀ g ∈ goalChunk_25, P g := by
  intro g hg
  simp only [goalChunk_25, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_193_full
  · exact goal_194_full
  · exact goal_195_full
  · exact goal_196_full
  · exact goal_197_full
  · exact goal_198_full
  · exact goal_199_full
  · exact goal_200_full
theorem chunk_26_holds : ∀ g ∈ goalChunk_26, P g := by
  intro g hg
  simp only [goalChunk_26, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_201_full
  · exact goal_202_full
  · exact goal_203_full
  · exact goal_204_full
  · exact goal_205_full
  · exact goal_206_full
  · exact goal_207_full
  · exact goal_208_full
theorem chunk_27_holds : ∀ g ∈ goalChunk_27, P g := by
  intro g hg
  simp only [goalChunk_27, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_209_full
  · exact goal_210_full
  · exact goal_211_full
  · exact goal_212_full
  · exact goal_213_full
  · exact goal_214_full
  · exact goal_215_full
  · exact goal_216_full
theorem chunk_28_holds : ∀ g ∈ goalChunk_28, P g := by
  intro g hg
  simp only [goalChunk_28, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_217_full
  · exact goal_218_full
  · exact goal_219_full
  · exact goal_220_full
  · exact goal_221_full
  · exact goal_222_full
  · exact goal_223_full
  · exact goal_224_full
theorem chunk_29_holds : ∀ g ∈ goalChunk_29, P g := by
  intro g hg
  simp only [goalChunk_29, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_225_full
  · exact goal_226_full
  · exact goal_227_full
  · exact goal_228_full
  · exact goal_229_full
  · exact goal_230_full
  · exact goal_231_full
  · exact goal_232_full
theorem chunk_30_holds : ∀ g ∈ goalChunk_30, P g := by
  intro g hg
  simp only [goalChunk_30, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_233_full
  · exact goal_234_full
  · exact goal_235_full
  · exact goal_236_full
  · exact goal_237_full
  · exact goal_238_full
  · exact goal_239_full
  · exact goal_240_full
theorem chunk_31_holds : ∀ g ∈ goalChunk_31, P g := by
  intro g hg
  simp only [goalChunk_31, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_241_full
  · exact goal_242_full
  · exact goal_243_full
  · exact goal_244_full
  · exact goal_245_full
  · exact goal_246_full
  · exact goal_247_full
  · exact goal_248_full
theorem chunk_32_holds : ∀ g ∈ goalChunk_32, P g := by
  intro g hg
  simp only [goalChunk_32, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_249_full
  · exact goal_250_full
  · exact goal_251_full
  · exact goal_252_full
  · exact goal_253_full
  · exact goal_254_full
  · exact goal_255_full
  · exact goal_256_full
theorem chunk_33_holds : ∀ g ∈ goalChunk_33, P g := by
  intro g hg
  simp only [goalChunk_33, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_257_full
  · exact goal_258_full
  · exact goal_259_full
  · exact goal_260_full
  · exact goal_261_full
  · exact goal_262_full
  · exact goal_263_full
  · exact goal_264_full
theorem chunk_34_holds : ∀ g ∈ goalChunk_34, P g := by
  intro g hg
  simp only [goalChunk_34, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_265_full
  · exact goal_266_full
  · exact goal_267_full
  · exact goal_268_full
  · exact goal_269_full
  · exact goal_270_full
  · exact goal_271_full
  · exact goal_272_full
theorem chunk_35_holds : ∀ g ∈ goalChunk_35, P g := by
  intro g hg
  simp only [goalChunk_35, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_273_full
  · exact goal_274_full
  · exact goal_275_full
  · exact goal_276_full
  · exact goal_277_full
  · exact goal_278_full
  · exact goal_279_full
  · exact goal_280_full
theorem chunk_36_holds : ∀ g ∈ goalChunk_36, P g := by
  intro g hg
  simp only [goalChunk_36, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_281_full
  · exact goal_282_full
  · exact goal_283_full
  · exact goal_284_full
  · exact goal_285_full
  · exact goal_286_full
  · exact goal_287_full
  · exact goal_288_full
theorem chunk_37_holds : ∀ g ∈ goalChunk_37, P g := by
  intro g hg
  simp only [goalChunk_37, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_289_full
  · exact goal_290_full
  · exact goal_291_full
  · exact goal_292_full
  · exact goal_293_full
  · exact goal_294_full
  · exact goal_295_full
  · exact goal_296_full
theorem chunk_38_holds : ∀ g ∈ goalChunk_38, P g := by
  intro g hg
  simp only [goalChunk_38, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_297_full
  · exact goal_298_full
  · exact goal_299_full
  · exact goal_300_full
  · exact goal_301_full
  · exact goal_302_full
  · exact goal_303_full
  · exact goal_304_full
theorem chunk_39_holds : ∀ g ∈ goalChunk_39, P g := by
  intro g hg
  simp only [goalChunk_39, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goal_305_full
  · exact goal_306_full
  · exact goal_307_full
  · exact goal_308_full
  · exact goal_309_full
  · exact goal_310_full
  · exact goal_311_full
  · exact goal_312_full

/-! ## Main theorem -/
theorem gpt_main_all_goals : all_goals_stmt := by
  show ∀ g ∈ goals, P g
  rw [show goals = (goalChunk_1 ++ goalChunk_2 ++ goalChunk_3 ++ goalChunk_4 ++ goalChunk_5 ++ goalChunk_6 ++ goalChunk_7 ++ goalChunk_8 ++ goalChunk_9 ++ goalChunk_10 ++ goalChunk_11 ++ goalChunk_12 ++ goalChunk_13 ++ goalChunk_14 ++ goalChunk_15 ++ goalChunk_16 ++ goalChunk_17 ++ goalChunk_18 ++ goalChunk_19 ++ goalChunk_20 ++ goalChunk_21 ++ goalChunk_22 ++ goalChunk_23 ++ goalChunk_24 ++ goalChunk_25 ++ goalChunk_26 ++ goalChunk_27 ++ goalChunk_28 ++ goalChunk_29 ++ goalChunk_30 ++ goalChunk_31 ++ goalChunk_32 ++ goalChunk_33 ++ goalChunk_34 ++ goalChunk_35 ++ goalChunk_36 ++ goalChunk_37 ++ goalChunk_38 ++ goalChunk_39) from rfl]
  simp only [List.forall_mem_append, and_assoc]
  exact ⟨chunk_1_holds, chunk_2_holds, chunk_3_holds, chunk_4_holds, chunk_5_holds, chunk_6_holds, chunk_7_holds, chunk_8_holds, chunk_9_holds, chunk_10_holds, chunk_11_holds, chunk_12_holds, chunk_13_holds, chunk_14_holds, chunk_15_holds, chunk_16_holds, chunk_17_holds, chunk_18_holds, chunk_19_holds, chunk_20_holds, chunk_21_holds, chunk_22_holds, chunk_23_holds, chunk_24_holds, chunk_25_holds, chunk_26_holds, chunk_27_holds, chunk_28_holds, chunk_29_holds, chunk_30_holds, chunk_31_holds, chunk_32_holds, chunk_33_holds, chunk_34_holds, chunk_35_holds, chunk_36_holds, chunk_37_holds, chunk_38_holds, chunk_39_holds⟩

end TrainVerify.Denote.GeneratedGoals
