/- Auto-generated human proof obligation index.

This is the intended entry point for human proof work.
Files imported here contain the reusable theorems whose bodies still need proofs.
`Instances.lean` projects Pattern_N proofs to concrete goals, and
`MainTheorem.lean` composes those projections into `all_goals_stmt`.

Optional segment proof packages, not needed for all_goals_stmt:
  - SegmentPattern_1.lean: prove_segment_pattern_1  -- instances=4, goals/instance=8, ops/instance: SM=8, PM=48, ops=[OpName.FW_add, OpName.AllReducePrim, OpName.ChunkPrim, OpName.AllToAllPrim, OpName.FW_layernorm, OpName.FW_linear, OpName.AllGatherPrim, OpName.FW_view, ...]
  - SegmentPattern_2.lean: prove_segment_pattern_2  -- instances=4, goals/instance=8, ops/instance: SM=8, PM=55, ops=[OpName.FW_transpose, OpName.ChunkPrim, OpName.FW_view, OpName.AllToAllPrim, OpName.FW_matmul, OpName.AllReducePrim, OpName.FW_div, OpName.FW_softmax, ...]
  - SegmentPattern_3.lean: prove_segment_pattern_3  -- instances=4, goals/instance=8, ops/instance: SM=8, PM=38, ops=[OpName.FW_transpose, OpName.FW_contiguous, OpName.AllToAllPrim, OpName.AllGatherPrim, OpName.FW_view, OpName.FW_linear, OpName.FW_add, OpName.FW_layernorm, ...]
  - SegmentPattern_4.lean: prove_segment_pattern_4  -- instances=4, goals/instance=8, ops/instance: SM=8, PM=66, ops=[OpName.BW_add, OpName.AllReducePrim, OpName.ChunkPrim, OpName.AllToAllPrim, OpName.BW_multiref, OpName.BW_layernorm, OpName.CROSS_DP_WRED, OpName.BW_linear, ...]
  - SegmentPattern_5.lean: prove_segment_pattern_5  -- instances=4, goals/instance=8, ops/instance: SM=8, PM=59, ops=[OpName.BW_view, OpName.BW_linear, OpName.ChunkPrim, OpName.BW_transpose, OpName.AllGatherPrim, OpName.BW_matmul, OpName.AllToAllPrim]
  - SegmentPattern_6.lean: prove_segment_pattern_6  -- instances=4, goals/instance=8, ops/instance: SM=8, PM=63, ops=[OpName.BW_matmul, OpName.BW_div, OpName.AllReducePrim, OpName.ChunkPrim, OpName.AllGatherPrim, OpName.BW_softmax, OpName.AllToAllPrim, OpName.BW_transpose, ...]
  - SegmentPattern_7.lean: prove_segment_pattern_7  -- instances=4, goals/instance=8, ops/instance: SM=8, PM=44, ops=[OpName.BW_linear, OpName.AllReducePrim, OpName.BW_add, OpName.BW_multiref, OpName.AllToAllPrim, OpName.BW_layernorm, OpName.CROSS_DP_WRED, OpName.ChunkPrim]
  - SegmentPattern_8.lean: prove_segment_pattern_8  -- instances=4, goals/instance=3, ops/instance: SM=3, PM=25, ops=[OpName.BW_gelu, OpName.BW_linear, OpName.AllToAllPrim, OpName.CROSS_DP_WRED]
  - SegmentPattern_9.lean: prove_segment_pattern_9  -- instances=4, goals/instance=8, ops/instance: SM=8, PM=44, ops=[OpName.FW_multiref, OpName.AllToAllPrim, OpName.BW_layernorm, OpName.BW_add, OpName.BW_linear, OpName.ChunkPrim]
  - SegmentPattern_10.lean: prove_segment_pattern_10  -- instances=4, goals/instance=6, ops/instance: SM=6, PM=38, ops=[OpName.FW_multiref, OpName.AllGatherPrim, OpName.BW_linear, OpName.ChunkPrim, OpName.AllReducePrim, OpName.AllToAllPrim, OpName.BW_layernorm, OpName.BW_add]

Pattern proof obligations for all_goals_stmt:
  - Pattern_1.lean: prove_pattern_1  -- instances=1, ops/instance: SM=1, PM=5, ops=[OpName.FW_sum, OpName.AllReducePrim]; concrete goals: 1
  - Pattern_2.lean: prove_pattern_2  -- instances=1, ops/instance: SM=1, PM=5, ops=[OpName.FW_embedding, OpName.AllReducePrim]; concrete goals: 2
  - Pattern_3.lean: prove_pattern_3  -- instances=1, ops/instance: SM=1, PM=8, ops=[OpName.FW_embedding, OpName.ChunkPrim]; concrete goals: 3
  - Pattern_4.lean: prove_pattern_4  -- instances=1, ops/instance: SM=1, PM=13, ops=[OpName.FW_add, OpName.AllReducePrim, OpName.ChunkPrim, OpName.AllToAllPrim]; concrete goals: 4
  - Pattern_5.lean: prove_pattern_5  -- instances=6, ops/instance: SM=1, PM=4, ops=[OpName.FW_layernorm]; concrete goals: 5, 30, 55, 75, 80, 100
  - Pattern_6.lean: prove_pattern_6  -- instances=5, ops/instance: SM=1, PM=5, ops=[OpName.FW_linear, OpName.AllGatherPrim]; concrete goals: 6, 7, 32, 58, 83
  - Pattern_7.lean: prove_pattern_7  -- instances=3, ops/instance: SM=1, PM=5, ops=[OpName.FW_linear, OpName.AllGatherPrim]; concrete goals: 8, 56, 57
  - Pattern_8.lean: prove_pattern_8  -- instances=12, ops/instance: SM=1, PM=4, ops=[OpName.FW_view]; concrete goals: 9, 11, 13, 34, 36, 38, 59, 61, 63, 84, 86, 88
  - Pattern_9.lean: prove_pattern_9  -- instances=5, ops/instance: SM=1, PM=8, ops=[OpName.FW_transpose, OpName.ChunkPrim]; concrete goals: 10, 14, 39, 62, 87
  - Pattern_10.lean: prove_pattern_10  -- instances=4, ops/instance: SM=1, PM=8, ops=[OpName.FW_transpose, OpName.ChunkPrim]; concrete goals: 12, 37, 60, 85
  - Pattern_11.lean: prove_pattern_11  -- instances=1, ops/instance: SM=1, PM=8, ops=[OpName.FW_transpose, OpName.AllToAllPrim]; concrete goals: 15
  - Pattern_12.lean: prove_pattern_12  -- instances=1, ops/instance: SM=1, PM=5, ops=[OpName.FW_matmul, OpName.AllReducePrim]; concrete goals: 16
  - Pattern_13.lean: prove_pattern_13  -- instances=1, ops/instance: SM=1, PM=9, ops=[OpName.FW_div, OpName.AllReducePrim, OpName.ChunkPrim]; concrete goals: 17
  - Pattern_14.lean: prove_pattern_14  -- instances=1, ops/instance: SM=1, PM=9, ops=[OpName.FW_softmax, OpName.AllToAllPrim, OpName.AllGatherPrim]; concrete goals: 18
  - Pattern_15.lean: prove_pattern_15  -- instances=1, ops/instance: SM=1, PM=4, ops=[OpName.FW_matmul]; concrete goals: 19
  - Pattern_16.lean: prove_pattern_16  -- instances=1, ops/instance: SM=1, PM=4, ops=[OpName.FW_transpose]; concrete goals: 20
  - Pattern_17.lean: prove_pattern_17  -- instances=1, ops/instance: SM=1, PM=9, ops=[OpName.FW_contiguous, OpName.AllToAllPrim, OpName.AllGatherPrim]; concrete goals: 21
  - Pattern_18.lean: prove_pattern_18  -- instances=4, ops/instance: SM=1, PM=4, ops=[OpName.FW_view]; concrete goals: 22, 47, 72, 97
  - Pattern_19.lean: prove_pattern_19  -- instances=5, ops/instance: SM=1, PM=4, ops=[OpName.FW_linear]; concrete goals: 23, 26, 51, 53, 106
  - Pattern_20.lean: prove_pattern_20  -- instances=1, ops/instance: SM=1, PM=4, ops=[OpName.FW_add]; concrete goals: 24
  - Pattern_21.lean: prove_pattern_21  -- instances=3, ops/instance: SM=1, PM=5, ops=[OpName.FW_layernorm, OpName.AllGatherPrim]; concrete goals: 25, 50, 105
  - Pattern_22.lean: prove_pattern_22  -- instances=1, ops/instance: SM=1, PM=4, ops=[OpName.FW_gelu]; concrete goals: 27
  - Pattern_23.lean: prove_pattern_23  -- instances=1, ops/instance: SM=1, PM=8, ops=[OpName.FW_linear, OpName.AllToAllPrim]; concrete goals: 28
  - Pattern_24.lean: prove_pattern_24  -- instances=2, ops/instance: SM=1, PM=8, ops=[OpName.FW_add, OpName.AllToAllPrim]; concrete goals: 29, 49
  - Pattern_25.lean: prove_pattern_25  -- instances=4, ops/instance: SM=1, PM=5, ops=[OpName.FW_linear, OpName.AllReducePrim]; concrete goals: 31, 33, 81, 82
  - Pattern_26.lean: prove_pattern_26  -- instances=3, ops/instance: SM=1, PM=8, ops=[OpName.FW_transpose, OpName.ChunkPrim]; concrete goals: 35, 64, 89
  - Pattern_27.lean: prove_pattern_27  -- instances=1, ops/instance: SM=1, PM=8, ops=[OpName.FW_transpose, OpName.AllToAllPrim]; concrete goals: 40
  - Pattern_28.lean: prove_pattern_28  -- instances=1, ops/instance: SM=1, PM=12, ops=[OpName.FW_matmul, OpName.AllToAllPrim]; concrete goals: 41
  - Pattern_29.lean: prove_pattern_29  -- instances=2, ops/instance: SM=1, PM=8, ops=[OpName.FW_div, OpName.AllToAllPrim]; concrete goals: 42, 92
  - Pattern_30.lean: prove_pattern_30  -- instances=2, ops/instance: SM=1, PM=4, ops=[OpName.FW_softmax]; concrete goals: 43, 68
  - Pattern_31.lean: prove_pattern_31  -- instances=1, ops/instance: SM=1, PM=13, ops=[OpName.FW_matmul, OpName.AllToAllPrim, OpName.AllReducePrim]; concrete goals: 44
  - Pattern_32.lean: prove_pattern_32  -- instances=1, ops/instance: SM=1, PM=9, ops=[OpName.FW_transpose, OpName.AllReducePrim, OpName.ChunkPrim]; concrete goals: 45
  - Pattern_33.lean: prove_pattern_33  -- instances=1, ops/instance: SM=1, PM=9, ops=[OpName.FW_contiguous, OpName.AllToAllPrim, OpName.AllGatherPrim]; concrete goals: 46
  - Pattern_34.lean: prove_pattern_34  -- instances=1, ops/instance: SM=1, PM=8, ops=[OpName.FW_linear, OpName.ChunkPrim]; concrete goals: 48
  - Pattern_35.lean: prove_pattern_35  -- instances=1, ops/instance: SM=1, PM=9, ops=[OpName.FW_gelu, OpName.AllToAllPrim, OpName.AllGatherPrim]; concrete goals: 52
  - Pattern_36.lean: prove_pattern_36  -- instances=1, ops/instance: SM=1, PM=8, ops=[OpName.FW_add, OpName.AllToAllPrim]; concrete goals: 54
  - Pattern_37.lean: prove_pattern_37  -- instances=1, ops/instance: SM=1, PM=9, ops=[OpName.FW_transpose, OpName.AllToAllPrim, OpName.AllGatherPrim]; concrete goals: 65
  - Pattern_38.lean: prove_pattern_38  -- instances=1, ops/instance: SM=1, PM=8, ops=[OpName.FW_matmul, OpName.AllToAllPrim]; concrete goals: 66
  - Pattern_39.lean: prove_pattern_39  -- instances=1, ops/instance: SM=1, PM=4, ops=[OpName.FW_div]; concrete goals: 67
  - Pattern_40.lean: prove_pattern_40  -- instances=1, ops/instance: SM=1, PM=12, ops=[OpName.FW_matmul, OpName.AllToAllPrim]; concrete goals: 69
  - Pattern_41.lean: prove_pattern_41  -- instances=1, ops/instance: SM=1, PM=8, ops=[OpName.FW_transpose, OpName.AllToAllPrim]; concrete goals: 70
  - Pattern_42.lean: prove_pattern_42  -- instances=1, ops/instance: SM=1, PM=9, ops=[OpName.FW_contiguous, OpName.AllToAllPrim, OpName.AllGatherPrim]; concrete goals: 71
  - Pattern_43.lean: prove_pattern_43  -- instances=2, ops/instance: SM=1, PM=9, ops=[OpName.FW_linear, OpName.ChunkPrim, OpName.AllReducePrim]; concrete goals: 73, 98
  - Pattern_44.lean: prove_pattern_44  -- instances=4, ops/instance: SM=1, PM=9, ops=[OpName.FW_add, OpName.AllReducePrim, OpName.ChunkPrim]; concrete goals: 74, 79, 99, 104
  - Pattern_45.lean: prove_pattern_45  -- instances=4, ops/instance: SM=1, PM=9, ops=[OpName.FW_linear, OpName.AllToAllPrim, OpName.AllReducePrim]; concrete goals: 76, 78, 101, 103
  - Pattern_46.lean: prove_pattern_46  -- instances=2, ops/instance: SM=1, PM=9, ops=[OpName.FW_gelu, OpName.AllReducePrim, OpName.ChunkPrim]; concrete goals: 77, 102
  - Pattern_47.lean: prove_pattern_47  -- instances=1, ops/instance: SM=1, PM=8, ops=[OpName.FW_transpose, OpName.AllToAllPrim]; concrete goals: 90
  - Pattern_48.lean: prove_pattern_48  -- instances=1, ops/instance: SM=1, PM=8, ops=[OpName.FW_matmul, OpName.AllToAllPrim]; concrete goals: 91
  - Pattern_49.lean: prove_pattern_49  -- instances=1, ops/instance: SM=1, PM=9, ops=[OpName.FW_softmax, OpName.AllToAllPrim, OpName.AllGatherPrim]; concrete goals: 93
  - Pattern_50.lean: prove_pattern_50  -- instances=1, ops/instance: SM=1, PM=8, ops=[OpName.FW_matmul, OpName.AllToAllPrim]; concrete goals: 94
  - Pattern_51.lean: prove_pattern_51  -- instances=1, ops/instance: SM=1, PM=8, ops=[OpName.FW_transpose, OpName.AllToAllPrim]; concrete goals: 95
  - Pattern_52.lean: prove_pattern_52  -- instances=1, ops/instance: SM=1, PM=9, ops=[OpName.FW_contiguous, OpName.AllToAllPrim, OpName.AllGatherPrim]; concrete goals: 96
  - Pattern_53.lean: prove_pattern_53  -- instances=1, ops/instance: SM=1, PM=4, ops=[OpName.BW_embedding]; concrete goals: 107
  - Pattern_54.lean: prove_pattern_54  -- instances=1, ops/instance: SM=1, PM=14, ops=[OpName.BW_add, OpName.AllReducePrim, OpName.ChunkPrim, OpName.AllToAllPrim, OpName.AllGatherPrim]; concrete goals: 108
  - Pattern_55.lean: prove_pattern_55  -- instances=1, ops/instance: SM=1, PM=9, ops=[OpName.BW_embedding, OpName.ChunkPrim, OpName.CROSS_DP_WRED]; concrete goals: 109
  - Pattern_56.lean: prove_pattern_56  -- instances=1, ops/instance: SM=1, PM=17, ops=[OpName.BW_add, OpName.AllReducePrim, OpName.ChunkPrim, OpName.AllToAllPrim]; concrete goals: 110
  - Pattern_57.lean: prove_pattern_57  -- instances=3, ops/instance: SM=1, PM=8, ops=[OpName.BW_multiref, OpName.AllToAllPrim]; concrete goals: 111, 137, 146
  - Pattern_58.lean: prove_pattern_58  -- instances=9, ops/instance: SM=1, PM=5, ops=[OpName.BW_layernorm, OpName.CROSS_DP_WRED]; concrete goals: 112, 138, 147, 173, 182, 208, 217, 243, 252
  - Pattern_59.lean: prove_pattern_59  -- instances=9, ops/instance: SM=1, PM=5, ops=[OpName.BW_layernorm, OpName.CROSS_DP_WRED]; concrete goals: 113, 139, 148, 174, 183, 209, 218, 244, 253
  - Pattern_60.lean: prove_pattern_60  -- instances=1, ops/instance: SM=1, PM=9, ops=[OpName.BW_multiref, OpName.AllReducePrim, OpName.ChunkPrim]; concrete goals: 114
  - Pattern_61.lean: prove_pattern_61  -- instances=5, ops/instance: SM=1, PM=9, ops=[OpName.BW_linear, OpName.ChunkPrim, OpName.CROSS_DP_WRED]; concrete goals: 115, 117, 152, 189, 224
  - Pattern_62.lean: prove_pattern_62  -- instances=12, ops/instance: SM=1, PM=4, ops=[OpName.BW_view]; concrete goals: 116, 118, 120, 151, 153, 155, 186, 188, 190, 221, 223, 225
  - Pattern_63.lean: prove_pattern_63  -- instances=3, ops/instance: SM=1, PM=8, ops=[OpName.BW_linear, OpName.ChunkPrim]; concrete goals: 119, 185, 187
  - Pattern_64.lean: prove_pattern_64  -- instances=5, ops/instance: SM=1, PM=9, ops=[OpName.BW_transpose, OpName.ChunkPrim, OpName.AllGatherPrim]; concrete goals: 121, 125, 160, 193, 228
  - Pattern_65.lean: prove_pattern_65  -- instances=2, ops/instance: SM=1, PM=4, ops=[OpName.BW_matmul]; concrete goals: 122, 127
  - Pattern_66.lean: prove_pattern_66  -- instances=4, ops/instance: SM=1, PM=9, ops=[OpName.BW_transpose, OpName.ChunkPrim, OpName.AllGatherPrim]; concrete goals: 123, 158, 191, 226
  - Pattern_67.lean: prove_pattern_67  -- instances=1, ops/instance: SM=1, PM=12, ops=[OpName.BW_transpose, OpName.AllToAllPrim]; concrete goals: 124
  - Pattern_68.lean: prove_pattern_68  -- instances=1, ops/instance: SM=1, PM=4, ops=[OpName.BW_matmul]; concrete goals: 126
  - Pattern_69.lean: prove_pattern_69  -- instances=1, ops/instance: SM=1, PM=10, ops=[OpName.BW_div, OpName.AllReducePrim, OpName.ChunkPrim, OpName.AllGatherPrim]; concrete goals: 128
  - Pattern_70.lean: prove_pattern_70  -- instances=1, ops/instance: SM=1, PM=12, ops=[OpName.BW_softmax, OpName.AllToAllPrim]; concrete goals: 129
  - Pattern_71.lean: prove_pattern_71  -- instances=1, ops/instance: SM=1, PM=9, ops=[OpName.BW_matmul, OpName.AllReducePrim, OpName.ChunkPrim]; concrete goals: 130
  - Pattern_72.lean: prove_pattern_72  -- instances=1, ops/instance: SM=1, PM=4, ops=[OpName.BW_transpose]; concrete goals: 131
  - Pattern_73.lean: prove_pattern_73  -- instances=1, ops/instance: SM=1, PM=16, ops=[OpName.BW_contiguous, OpName.AllToAllPrim, OpName.ChunkPrim]; concrete goals: 132
  - Pattern_74.lean: prove_pattern_74  -- instances=4, ops/instance: SM=1, PM=4, ops=[OpName.BW_view]; concrete goals: 133, 168, 203, 238
  - Pattern_75.lean: prove_pattern_75  -- instances=1, ops/instance: SM=1, PM=5, ops=[OpName.BW_linear, OpName.AllReducePrim]; concrete goals: 134
  - Pattern_76.lean: prove_pattern_76  -- instances=5, ops/instance: SM=1, PM=4, ops=[OpName.BW_linear]; concrete goals: 135, 141, 176, 179, 255
  - Pattern_77.lean: prove_pattern_77  -- instances=2, ops/instance: SM=1, PM=4, ops=[OpName.BW_add]; concrete goals: 136, 260
  - Pattern_78.lean: prove_pattern_78  -- instances=4, ops/instance: SM=1, PM=9, ops=[OpName.BW_linear, OpName.AllReducePrim, OpName.ChunkPrim]; concrete goals: 140, 175, 178, 254
  - Pattern_79.lean: prove_pattern_79  -- instances=1, ops/instance: SM=1, PM=4, ops=[OpName.BW_gelu]; concrete goals: 142
  - Pattern_80.lean: prove_pattern_80  -- instances=1, ops/instance: SM=1, PM=12, ops=[OpName.BW_linear, OpName.AllToAllPrim]; concrete goals: 143
  - Pattern_81.lean: prove_pattern_81  -- instances=1, ops/instance: SM=1, PM=9, ops=[OpName.BW_linear, OpName.AllToAllPrim, OpName.CROSS_DP_WRED]; concrete goals: 144
  - Pattern_82.lean: prove_pattern_82  -- instances=2, ops/instance: SM=1, PM=12, ops=[OpName.BW_add, OpName.AllToAllPrim]; concrete goals: 145, 171
  - Pattern_83.lean: prove_pattern_83  -- instances=1, ops/instance: SM=1, PM=12, ops=[OpName.BW_multiref, OpName.AllToAllPrim]; concrete goals: 149
  - Pattern_84.lean: prove_pattern_84  -- instances=8, ops/instance: SM=1, PM=4, ops=[OpName.BW_linear]; concrete goals: 150, 154, 220, 222, 276, 280, 304, 306
  - Pattern_85.lean: prove_pattern_85  -- instances=3, ops/instance: SM=1, PM=9, ops=[OpName.BW_transpose, OpName.ChunkPrim, OpName.AllGatherPrim]; concrete goals: 156, 195, 230
  - Pattern_86.lean: prove_pattern_86  -- instances=1, ops/instance: SM=1, PM=16, ops=[OpName.BW_matmul, OpName.AllToAllPrim]; concrete goals: 157
  - Pattern_87.lean: prove_pattern_87  -- instances=1, ops/instance: SM=1, PM=12, ops=[OpName.BW_transpose, OpName.AllToAllPrim]; concrete goals: 159
  - Pattern_88.lean: prove_pattern_88  -- instances=1, ops/instance: SM=1, PM=16, ops=[OpName.BW_matmul, OpName.AllToAllPrim]; concrete goals: 161
  - Pattern_89.lean: prove_pattern_89  -- instances=1, ops/instance: SM=1, PM=16, ops=[OpName.BW_matmul, OpName.AllToAllPrim]; concrete goals: 162
  - Pattern_90.lean: prove_pattern_90  -- instances=2, ops/instance: SM=1, PM=12, ops=[OpName.BW_div, OpName.AllToAllPrim]; concrete goals: 163, 233
  - Pattern_91.lean: prove_pattern_91  -- instances=2, ops/instance: SM=1, PM=4, ops=[OpName.BW_softmax]; concrete goals: 164, 199
  - Pattern_92.lean: prove_pattern_92  -- instances=1, ops/instance: SM=1, PM=16, ops=[OpName.BW_matmul, OpName.AllToAllPrim]; concrete goals: 165
  - Pattern_93.lean: prove_pattern_93  -- instances=1, ops/instance: SM=1, PM=10, ops=[OpName.BW_transpose, OpName.AllReducePrim, OpName.ChunkPrim, OpName.AllGatherPrim]; concrete goals: 166
  - Pattern_94.lean: prove_pattern_94  -- instances=1, ops/instance: SM=1, PM=16, ops=[OpName.BW_contiguous, OpName.AllToAllPrim, OpName.ChunkPrim]; concrete goals: 167
  - Pattern_95.lean: prove_pattern_95  -- instances=1, ops/instance: SM=1, PM=9, ops=[OpName.BW_linear, OpName.ChunkPrim, OpName.AllGatherPrim]; concrete goals: 169
  - Pattern_96.lean: prove_pattern_96  -- instances=1, ops/instance: SM=1, PM=9, ops=[OpName.BW_linear, OpName.ChunkPrim, OpName.CROSS_DP_WRED]; concrete goals: 170
  - Pattern_97.lean: prove_pattern_97  -- instances=1, ops/instance: SM=1, PM=12, ops=[OpName.BW_multiref, OpName.AllToAllPrim]; concrete goals: 172
  - Pattern_98.lean: prove_pattern_98  -- instances=1, ops/instance: SM=1, PM=12, ops=[OpName.BW_gelu, OpName.AllToAllPrim]; concrete goals: 177
  - Pattern_99.lean: prove_pattern_99  -- instances=1, ops/instance: SM=1, PM=12, ops=[OpName.BW_add, OpName.AllToAllPrim]; concrete goals: 180
  - Pattern_100.lean: prove_pattern_100  -- instances=4, ops/instance: SM=1, PM=4, ops=[OpName.BW_multiref]; concrete goals: 181, 207, 216, 242
  - Pattern_101.lean: prove_pattern_101  -- instances=1, ops/instance: SM=1, PM=14, ops=[OpName.BW_multiref, OpName.AllReducePrim, OpName.ChunkPrim]; concrete goals: 184
  - Pattern_102.lean: prove_pattern_102  -- instances=1, ops/instance: SM=1, PM=12, ops=[OpName.BW_matmul, OpName.AllToAllPrim]; concrete goals: 192
  - Pattern_103.lean: prove_pattern_103  -- instances=1, ops/instance: SM=1, PM=12, ops=[OpName.BW_transpose, OpName.AllToAllPrim]; concrete goals: 194
  - Pattern_104.lean: prove_pattern_104  -- instances=1, ops/instance: SM=1, PM=16, ops=[OpName.BW_matmul, OpName.AllToAllPrim]; concrete goals: 196
  - Pattern_105.lean: prove_pattern_105  -- instances=1, ops/instance: SM=1, PM=13, ops=[OpName.BW_matmul, OpName.AllToAllPrim, OpName.AllReducePrim, OpName.ChunkPrim]; concrete goals: 197
  - Pattern_106.lean: prove_pattern_106  -- instances=1, ops/instance: SM=1, PM=4, ops=[OpName.BW_div]; concrete goals: 198
  - Pattern_107.lean: prove_pattern_107  -- instances=1, ops/instance: SM=1, PM=16, ops=[OpName.BW_matmul, OpName.AllToAllPrim]; concrete goals: 200
  - Pattern_108.lean: prove_pattern_108  -- instances=1, ops/instance: SM=1, PM=12, ops=[OpName.BW_transpose, OpName.AllToAllPrim]; concrete goals: 201
  - Pattern_109.lean: prove_pattern_109  -- instances=1, ops/instance: SM=1, PM=16, ops=[OpName.BW_contiguous, OpName.AllToAllPrim, OpName.ChunkPrim]; concrete goals: 202
  - Pattern_110.lean: prove_pattern_110  -- instances=2, ops/instance: SM=1, PM=9, ops=[OpName.BW_linear, OpName.ChunkPrim, OpName.AllGatherPrim]; concrete goals: 204, 239
  - Pattern_111.lean: prove_pattern_111  -- instances=2, ops/instance: SM=1, PM=8, ops=[OpName.BW_linear, OpName.ChunkPrim]; concrete goals: 205, 240
  - Pattern_112.lean: prove_pattern_112  -- instances=4, ops/instance: SM=1, PM=10, ops=[OpName.BW_add, OpName.AllReducePrim, OpName.ChunkPrim, OpName.AllGatherPrim]; concrete goals: 206, 215, 241, 250
  - Pattern_113.lean: prove_pattern_113  -- instances=4, ops/instance: SM=1, PM=12, ops=[OpName.BW_linear, OpName.AllToAllPrim]; concrete goals: 210, 213, 245, 248
  - Pattern_114.lean: prove_pattern_114  -- instances=4, ops/instance: SM=1, PM=8, ops=[OpName.BW_linear, OpName.AllToAllPrim]; concrete goals: 211, 214, 246, 249
  - Pattern_115.lean: prove_pattern_115  -- instances=2, ops/instance: SM=1, PM=10, ops=[OpName.BW_gelu, OpName.AllReducePrim, OpName.ChunkPrim, OpName.AllGatherPrim]; concrete goals: 212, 247
  - Pattern_116.lean: prove_pattern_116  -- instances=1, ops/instance: SM=1, PM=12, ops=[OpName.BW_multiref, OpName.AllToAllPrim]; concrete goals: 219
  - Pattern_117.lean: prove_pattern_117  -- instances=1, ops/instance: SM=1, PM=8, ops=[OpName.BW_matmul, OpName.AllToAllPrim]; concrete goals: 227
  - Pattern_118.lean: prove_pattern_118  -- instances=1, ops/instance: SM=1, PM=12, ops=[OpName.BW_transpose, OpName.AllToAllPrim]; concrete goals: 229
  - Pattern_119.lean: prove_pattern_119  -- instances=1, ops/instance: SM=1, PM=12, ops=[OpName.BW_matmul, OpName.AllToAllPrim]; concrete goals: 231
  - Pattern_120.lean: prove_pattern_120  -- instances=1, ops/instance: SM=1, PM=12, ops=[OpName.BW_matmul, OpName.AllToAllPrim]; concrete goals: 232
  - Pattern_121.lean: prove_pattern_121  -- instances=1, ops/instance: SM=1, PM=12, ops=[OpName.BW_softmax, OpName.AllToAllPrim]; concrete goals: 234
  - Pattern_122.lean: prove_pattern_122  -- instances=1, ops/instance: SM=1, PM=13, ops=[OpName.BW_matmul, OpName.AllToAllPrim, OpName.AllReducePrim, OpName.ChunkPrim]; concrete goals: 235
  - Pattern_123.lean: prove_pattern_123  -- instances=1, ops/instance: SM=1, PM=12, ops=[OpName.BW_transpose, OpName.AllToAllPrim]; concrete goals: 236
  - Pattern_124.lean: prove_pattern_124  -- instances=1, ops/instance: SM=1, PM=16, ops=[OpName.BW_contiguous, OpName.AllToAllPrim, OpName.ChunkPrim]; concrete goals: 237
  - Pattern_125.lean: prove_pattern_125  -- instances=9, ops/instance: SM=1, PM=4, ops=[OpName.BW_layernorm]; concrete goals: 251, 258, 268, 272, 282, 286, 296, 300, 310
  - Pattern_126.lean: prove_pattern_126  -- instances=1, ops/instance: SM=1, PM=4, ops=[OpName.BW_sum]; concrete goals: 256
  - Pattern_127.lean: prove_pattern_127  -- instances=4, ops/instance: SM=1, PM=8, ops=[OpName.FW_multiref, OpName.AllToAllPrim]; concrete goals: 257, 267, 271, 281
  - Pattern_128.lean: prove_pattern_128  -- instances=11, ops/instance: SM=1, PM=4, ops=[OpName.FW_multiref]; concrete goals: 259, 269, 273, 285, 287, 295, 297, 299, 301, 309, 311
  - Pattern_129.lean: prove_pattern_129  -- instances=5, ops/instance: SM=1, PM=4, ops=[OpName.FW_multiref]; concrete goals: 261, 263, 277, 293, 307
  - Pattern_130.lean: prove_pattern_130  -- instances=5, ops/instance: SM=1, PM=8, ops=[OpName.BW_linear, OpName.ChunkPrim]; concrete goals: 262, 264, 278, 294, 308
  - Pattern_131.lean: prove_pattern_131  -- instances=1, ops/instance: SM=1, PM=5, ops=[OpName.FW_multiref, OpName.AllGatherPrim]; concrete goals: 265
  - Pattern_132.lean: prove_pattern_132  -- instances=3, ops/instance: SM=1, PM=9, ops=[OpName.BW_linear, OpName.ChunkPrim, OpName.AllReducePrim]; concrete goals: 266, 290, 292
  - Pattern_133.lean: prove_pattern_133  -- instances=2, ops/instance: SM=1, PM=8, ops=[OpName.BW_add, OpName.AllToAllPrim]; concrete goals: 270, 274
  - Pattern_134.lean: prove_pattern_134  -- instances=2, ops/instance: SM=1, PM=8, ops=[OpName.FW_multiref, OpName.AllToAllPrim]; concrete goals: 275, 303
  - Pattern_135.lean: prove_pattern_135  -- instances=1, ops/instance: SM=1, PM=8, ops=[OpName.FW_multiref, OpName.AllToAllPrim]; concrete goals: 279
  - Pattern_136.lean: prove_pattern_136  -- instances=1, ops/instance: SM=1, PM=8, ops=[OpName.FW_multiref, OpName.AllToAllPrim]; concrete goals: 283
  - Pattern_137.lean: prove_pattern_137  -- instances=1, ops/instance: SM=1, PM=8, ops=[OpName.BW_add, OpName.AllToAllPrim]; concrete goals: 284
  - Pattern_138.lean: prove_pattern_138  -- instances=4, ops/instance: SM=1, PM=9, ops=[OpName.BW_add, OpName.AllReducePrim, OpName.ChunkPrim]; concrete goals: 288, 298, 302, 312
  - Pattern_139.lean: prove_pattern_139  -- instances=1, ops/instance: SM=1, PM=5, ops=[OpName.FW_multiref, OpName.AllGatherPrim]; concrete goals: 289
  - Pattern_140.lean: prove_pattern_140  -- instances=1, ops/instance: SM=1, PM=5, ops=[OpName.FW_multiref, OpName.AllGatherPrim]; concrete goals: 291
  - Pattern_141.lean: prove_pattern_141  -- instances=1, ops/instance: SM=1, PM=8, ops=[OpName.FW_multiref, OpName.AllToAllPrim]; concrete goals: 305
-/
import denote.gpt_ly4_segments.Pattern_1
import denote.gpt_ly4_segments.Pattern_2
import denote.gpt_ly4_segments.Pattern_3
import denote.gpt_ly4_segments.Pattern_4
import denote.gpt_ly4_segments.Pattern_5
import denote.gpt_ly4_segments.Pattern_6
import denote.gpt_ly4_segments.Pattern_7
import denote.gpt_ly4_segments.Pattern_8
import denote.gpt_ly4_segments.Pattern_9
import denote.gpt_ly4_segments.Pattern_10
import denote.gpt_ly4_segments.Pattern_11
import denote.gpt_ly4_segments.Pattern_12
import denote.gpt_ly4_segments.Pattern_13
import denote.gpt_ly4_segments.Pattern_14
import denote.gpt_ly4_segments.Pattern_15
import denote.gpt_ly4_segments.Pattern_16
import denote.gpt_ly4_segments.Pattern_17
import denote.gpt_ly4_segments.Pattern_18
import denote.gpt_ly4_segments.Pattern_19
import denote.gpt_ly4_segments.Pattern_20
import denote.gpt_ly4_segments.Pattern_21
import denote.gpt_ly4_segments.Pattern_22
import denote.gpt_ly4_segments.Pattern_23
import denote.gpt_ly4_segments.Pattern_24
import denote.gpt_ly4_segments.Pattern_25
import denote.gpt_ly4_segments.Pattern_26
import denote.gpt_ly4_segments.Pattern_27
import denote.gpt_ly4_segments.Pattern_28
import denote.gpt_ly4_segments.Pattern_29
import denote.gpt_ly4_segments.Pattern_30
import denote.gpt_ly4_segments.Pattern_31
import denote.gpt_ly4_segments.Pattern_32
import denote.gpt_ly4_segments.Pattern_33
import denote.gpt_ly4_segments.Pattern_34
import denote.gpt_ly4_segments.Pattern_35
import denote.gpt_ly4_segments.Pattern_36
import denote.gpt_ly4_segments.Pattern_37
import denote.gpt_ly4_segments.Pattern_38
import denote.gpt_ly4_segments.Pattern_39
import denote.gpt_ly4_segments.Pattern_40
import denote.gpt_ly4_segments.Pattern_41
import denote.gpt_ly4_segments.Pattern_42
import denote.gpt_ly4_segments.Pattern_43
import denote.gpt_ly4_segments.Pattern_44
import denote.gpt_ly4_segments.Pattern_45
import denote.gpt_ly4_segments.Pattern_46
import denote.gpt_ly4_segments.Pattern_47
import denote.gpt_ly4_segments.Pattern_48
import denote.gpt_ly4_segments.Pattern_49
import denote.gpt_ly4_segments.Pattern_50
import denote.gpt_ly4_segments.Pattern_51
import denote.gpt_ly4_segments.Pattern_52
import denote.gpt_ly4_segments.Pattern_53
import denote.gpt_ly4_segments.Pattern_54
import denote.gpt_ly4_segments.Pattern_55
import denote.gpt_ly4_segments.Pattern_56
import denote.gpt_ly4_segments.Pattern_57
import denote.gpt_ly4_segments.Pattern_58
import denote.gpt_ly4_segments.Pattern_59
import denote.gpt_ly4_segments.Pattern_60
import denote.gpt_ly4_segments.Pattern_61
import denote.gpt_ly4_segments.Pattern_62
import denote.gpt_ly4_segments.Pattern_63
import denote.gpt_ly4_segments.Pattern_64
import denote.gpt_ly4_segments.Pattern_65
import denote.gpt_ly4_segments.Pattern_66
import denote.gpt_ly4_segments.Pattern_67
import denote.gpt_ly4_segments.Pattern_68
import denote.gpt_ly4_segments.Pattern_69
import denote.gpt_ly4_segments.Pattern_70
import denote.gpt_ly4_segments.Pattern_71
import denote.gpt_ly4_segments.Pattern_72
import denote.gpt_ly4_segments.Pattern_73
import denote.gpt_ly4_segments.Pattern_74
import denote.gpt_ly4_segments.Pattern_75
import denote.gpt_ly4_segments.Pattern_76
import denote.gpt_ly4_segments.Pattern_77
import denote.gpt_ly4_segments.Pattern_78
import denote.gpt_ly4_segments.Pattern_79
import denote.gpt_ly4_segments.Pattern_80
import denote.gpt_ly4_segments.Pattern_81
import denote.gpt_ly4_segments.Pattern_82
import denote.gpt_ly4_segments.Pattern_83
import denote.gpt_ly4_segments.Pattern_84
import denote.gpt_ly4_segments.Pattern_85
import denote.gpt_ly4_segments.Pattern_86
import denote.gpt_ly4_segments.Pattern_87
import denote.gpt_ly4_segments.Pattern_88
import denote.gpt_ly4_segments.Pattern_89
import denote.gpt_ly4_segments.Pattern_90
import denote.gpt_ly4_segments.Pattern_91
import denote.gpt_ly4_segments.Pattern_92
import denote.gpt_ly4_segments.Pattern_93
import denote.gpt_ly4_segments.Pattern_94
import denote.gpt_ly4_segments.Pattern_95
import denote.gpt_ly4_segments.Pattern_96
import denote.gpt_ly4_segments.Pattern_97
import denote.gpt_ly4_segments.Pattern_98
import denote.gpt_ly4_segments.Pattern_99
import denote.gpt_ly4_segments.Pattern_100
import denote.gpt_ly4_segments.Pattern_101
import denote.gpt_ly4_segments.Pattern_102
import denote.gpt_ly4_segments.Pattern_103
import denote.gpt_ly4_segments.Pattern_104
import denote.gpt_ly4_segments.Pattern_105
import denote.gpt_ly4_segments.Pattern_106
import denote.gpt_ly4_segments.Pattern_107
import denote.gpt_ly4_segments.Pattern_108
import denote.gpt_ly4_segments.Pattern_109
import denote.gpt_ly4_segments.Pattern_110
import denote.gpt_ly4_segments.Pattern_111
import denote.gpt_ly4_segments.Pattern_112
import denote.gpt_ly4_segments.Pattern_113
import denote.gpt_ly4_segments.Pattern_114
import denote.gpt_ly4_segments.Pattern_115
import denote.gpt_ly4_segments.Pattern_116
import denote.gpt_ly4_segments.Pattern_117
import denote.gpt_ly4_segments.Pattern_118
import denote.gpt_ly4_segments.Pattern_119
import denote.gpt_ly4_segments.Pattern_120
import denote.gpt_ly4_segments.Pattern_121
import denote.gpt_ly4_segments.Pattern_122
import denote.gpt_ly4_segments.Pattern_123
import denote.gpt_ly4_segments.Pattern_124
import denote.gpt_ly4_segments.Pattern_125
import denote.gpt_ly4_segments.Pattern_126
import denote.gpt_ly4_segments.Pattern_127
import denote.gpt_ly4_segments.Pattern_128
import denote.gpt_ly4_segments.Pattern_129
import denote.gpt_ly4_segments.Pattern_130
import denote.gpt_ly4_segments.Pattern_131
import denote.gpt_ly4_segments.Pattern_132
import denote.gpt_ly4_segments.Pattern_133
import denote.gpt_ly4_segments.Pattern_134
import denote.gpt_ly4_segments.Pattern_135
import denote.gpt_ly4_segments.Pattern_136
import denote.gpt_ly4_segments.Pattern_137
import denote.gpt_ly4_segments.Pattern_138
import denote.gpt_ly4_segments.Pattern_139
import denote.gpt_ly4_segments.Pattern_140
import denote.gpt_ly4_segments.Pattern_141

namespace TrainVerify.Denote.GeneratedProofObligations

def optionalSegmentProofPackageCount : Nat := 10
def humanPatternProofCount : Nat := 141
def humanProofObligationCount : Nat := 141

end TrainVerify.Denote.GeneratedProofObligations

