/- Auto-generated main composition skeleton.
   This file composes reusable pattern proofs into all_goals_stmt.
-/
import denote.gpt_ly4_segments.Instances

set_option maxRecDepth 100000
set_option linter.style.emptyLine false

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedPatternInstances

namespace TrainVerify.Denote.GeneratedMain

def fullGraphSegment : SegmentDecl :=
  { name := "full", sm := sm, pm := pm, goals := goals }

def graphSegments : List SegmentDecl := [fullGraphSegment]

theorem graphSegments_cover : GraphCoverage sm pm graphSegments := by
  unfold GraphCoverage concatSMGraph concatPMGraph graphSegments fullGraphSegment
  refine ⟨rfl, rfl⟩

theorem forall_mem_append_goal {xs ys : List LineageGoal}
    (hx : ∀ g ∈ xs, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals)
    (hy : ∀ g ∈ ys, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals) :
    ∀ g ∈ xs ++ ys, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  have h := List.mem_append.mp hg
  cases h with
  | inl h => exact hx g h
  | inr h => exact hy g h

/-- Main generated composition theorem.

Assuming every reusable Pattern_N proof is complete, this file instantiates
those proofs for every concrete goal and composes them into `all_goals_stmt`.
It deliberately stops at the lineage-goal layer rather than claiming a
stronger full-graph equivalence theorem.
-/

theorem gpt_goal_chunk_1_all : ∀ g ∈ goalChunk_1, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_1 at hg
  cases hg with
  | head =>
    exact prove_goal_1_from_pattern_1
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_2_from_pattern_2
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_3_from_pattern_3
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_4_from_pattern_4
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_5_from_pattern_5
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_6_from_pattern_6
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_7_from_pattern_6
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_8_from_pattern_7
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_2_all : ∀ g ∈ goalChunk_2, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_2 at hg
  cases hg with
  | head =>
    exact prove_goal_9_from_pattern_8
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_10_from_pattern_9
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_11_from_pattern_8
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_12_from_pattern_10
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_13_from_pattern_8
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_14_from_pattern_9
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_15_from_pattern_11
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_16_from_pattern_12
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_3_all : ∀ g ∈ goalChunk_3, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_3 at hg
  cases hg with
  | head =>
    exact prove_goal_17_from_pattern_13
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_18_from_pattern_14
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_19_from_pattern_15
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_20_from_pattern_16
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_21_from_pattern_17
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_22_from_pattern_18
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_23_from_pattern_19
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_24_from_pattern_20
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_4_all : ∀ g ∈ goalChunk_4, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_4 at hg
  cases hg with
  | head =>
    exact prove_goal_25_from_pattern_21
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_26_from_pattern_19
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_27_from_pattern_22
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_28_from_pattern_23
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_29_from_pattern_24
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_30_from_pattern_5
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_31_from_pattern_25
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_32_from_pattern_6
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_5_all : ∀ g ∈ goalChunk_5, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_5 at hg
  cases hg with
  | head =>
    exact prove_goal_33_from_pattern_25
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_34_from_pattern_8
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_35_from_pattern_26
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_36_from_pattern_8
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_37_from_pattern_10
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_38_from_pattern_8
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_39_from_pattern_9
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_40_from_pattern_27
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_6_all : ∀ g ∈ goalChunk_6, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_6 at hg
  cases hg with
  | head =>
    exact prove_goal_41_from_pattern_28
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_42_from_pattern_29
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_43_from_pattern_30
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_44_from_pattern_31
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_45_from_pattern_32
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_46_from_pattern_33
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_47_from_pattern_18
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_48_from_pattern_34
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_7_all : ∀ g ∈ goalChunk_7, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_7 at hg
  cases hg with
  | head =>
    exact prove_goal_49_from_pattern_24
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_50_from_pattern_21
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_51_from_pattern_19
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_52_from_pattern_35
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_53_from_pattern_19
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_54_from_pattern_36
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_55_from_pattern_5
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_56_from_pattern_7
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_8_all : ∀ g ∈ goalChunk_8, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_8 at hg
  cases hg with
  | head =>
    exact prove_goal_57_from_pattern_7
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_58_from_pattern_6
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_59_from_pattern_8
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_60_from_pattern_10
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_61_from_pattern_8
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_62_from_pattern_9
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_63_from_pattern_8
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_64_from_pattern_26
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_9_all : ∀ g ∈ goalChunk_9, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_9 at hg
  cases hg with
  | head =>
    exact prove_goal_65_from_pattern_37
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_66_from_pattern_38
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_67_from_pattern_39
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_68_from_pattern_30
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_69_from_pattern_40
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_70_from_pattern_41
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_71_from_pattern_42
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_72_from_pattern_18
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_10_all : ∀ g ∈ goalChunk_10, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_10 at hg
  cases hg with
  | head =>
    exact prove_goal_73_from_pattern_43
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_74_from_pattern_44
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_75_from_pattern_5
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_76_from_pattern_45
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_77_from_pattern_46
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_78_from_pattern_45
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_79_from_pattern_44
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_80_from_pattern_5
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_11_all : ∀ g ∈ goalChunk_11, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_11 at hg
  cases hg with
  | head =>
    exact prove_goal_81_from_pattern_25
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_82_from_pattern_25
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_83_from_pattern_6
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_84_from_pattern_8
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_85_from_pattern_10
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_86_from_pattern_8
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_87_from_pattern_9
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_88_from_pattern_8
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_12_all : ∀ g ∈ goalChunk_12, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_12 at hg
  cases hg with
  | head =>
    exact prove_goal_89_from_pattern_26
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_90_from_pattern_47
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_91_from_pattern_48
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_92_from_pattern_29
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_93_from_pattern_49
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_94_from_pattern_50
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_95_from_pattern_51
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_96_from_pattern_52
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_13_all : ∀ g ∈ goalChunk_13, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_13 at hg
  cases hg with
  | head =>
    exact prove_goal_97_from_pattern_18
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_98_from_pattern_43
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_99_from_pattern_44
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_100_from_pattern_5
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_101_from_pattern_45
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_102_from_pattern_46
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_103_from_pattern_45
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_104_from_pattern_44
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_14_all : ∀ g ∈ goalChunk_14, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_14 at hg
  cases hg with
  | head =>
    exact prove_goal_105_from_pattern_21
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_106_from_pattern_19
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_107_from_pattern_53
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_108_from_pattern_54
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_109_from_pattern_55
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_110_from_pattern_56
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_111_from_pattern_57
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_112_from_pattern_58
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_15_all : ∀ g ∈ goalChunk_15, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_15 at hg
  cases hg with
  | head =>
    exact prove_goal_113_from_pattern_59
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_114_from_pattern_60
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_115_from_pattern_61
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_116_from_pattern_62
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_117_from_pattern_61
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_118_from_pattern_62
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_119_from_pattern_63
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_120_from_pattern_62
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_16_all : ∀ g ∈ goalChunk_16, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_16 at hg
  cases hg with
  | head =>
    exact prove_goal_121_from_pattern_64
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_122_from_pattern_65
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_123_from_pattern_66
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_124_from_pattern_67
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_125_from_pattern_64
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_126_from_pattern_68
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_127_from_pattern_65
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_128_from_pattern_69
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_17_all : ∀ g ∈ goalChunk_17, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_17 at hg
  cases hg with
  | head =>
    exact prove_goal_129_from_pattern_70
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_130_from_pattern_71
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_131_from_pattern_72
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_132_from_pattern_73
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_133_from_pattern_74
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_134_from_pattern_75
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_135_from_pattern_76
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_136_from_pattern_77
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_18_all : ∀ g ∈ goalChunk_18, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_18 at hg
  cases hg with
  | head =>
    exact prove_goal_137_from_pattern_57
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_138_from_pattern_58
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_139_from_pattern_59
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_140_from_pattern_78
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_141_from_pattern_76
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_142_from_pattern_79
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_143_from_pattern_80
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_144_from_pattern_81
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_19_all : ∀ g ∈ goalChunk_19, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_19 at hg
  cases hg with
  | head =>
    exact prove_goal_145_from_pattern_82
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_146_from_pattern_57
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_147_from_pattern_58
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_148_from_pattern_59
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_149_from_pattern_83
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_150_from_pattern_84
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_151_from_pattern_62
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_152_from_pattern_61
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_20_all : ∀ g ∈ goalChunk_20, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_20 at hg
  cases hg with
  | head =>
    exact prove_goal_153_from_pattern_62
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_154_from_pattern_84
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_155_from_pattern_62
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_156_from_pattern_85
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_157_from_pattern_86
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_158_from_pattern_66
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_159_from_pattern_87
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_160_from_pattern_64
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_21_all : ∀ g ∈ goalChunk_21, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_21 at hg
  cases hg with
  | head =>
    exact prove_goal_161_from_pattern_88
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_162_from_pattern_89
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_163_from_pattern_90
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_164_from_pattern_91
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_165_from_pattern_92
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_166_from_pattern_93
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_167_from_pattern_94
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_168_from_pattern_74
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_22_all : ∀ g ∈ goalChunk_22, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_22 at hg
  cases hg with
  | head =>
    exact prove_goal_169_from_pattern_95
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_170_from_pattern_96
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_171_from_pattern_82
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_172_from_pattern_97
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_173_from_pattern_58
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_174_from_pattern_59
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_175_from_pattern_78
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_176_from_pattern_76
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_23_all : ∀ g ∈ goalChunk_23, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_23 at hg
  cases hg with
  | head =>
    exact prove_goal_177_from_pattern_98
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_178_from_pattern_78
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_179_from_pattern_76
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_180_from_pattern_99
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_181_from_pattern_100
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_182_from_pattern_58
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_183_from_pattern_59
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_184_from_pattern_101
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_24_all : ∀ g ∈ goalChunk_24, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_24 at hg
  cases hg with
  | head =>
    exact prove_goal_185_from_pattern_63
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_186_from_pattern_62
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_187_from_pattern_63
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_188_from_pattern_62
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_189_from_pattern_61
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_190_from_pattern_62
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_191_from_pattern_66
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_192_from_pattern_102
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_25_all : ∀ g ∈ goalChunk_25, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_25 at hg
  cases hg with
  | head =>
    exact prove_goal_193_from_pattern_64
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_194_from_pattern_103
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_195_from_pattern_85
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_196_from_pattern_104
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_197_from_pattern_105
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_198_from_pattern_106
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_199_from_pattern_91
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_200_from_pattern_107
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_26_all : ∀ g ∈ goalChunk_26, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_26 at hg
  cases hg with
  | head =>
    exact prove_goal_201_from_pattern_108
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_202_from_pattern_109
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_203_from_pattern_74
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_204_from_pattern_110
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_205_from_pattern_111
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_206_from_pattern_112
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_207_from_pattern_100
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_208_from_pattern_58
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_27_all : ∀ g ∈ goalChunk_27, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_27 at hg
  cases hg with
  | head =>
    exact prove_goal_209_from_pattern_59
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_210_from_pattern_113
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_211_from_pattern_114
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_212_from_pattern_115
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_213_from_pattern_113
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_214_from_pattern_114
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_215_from_pattern_112
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_216_from_pattern_100
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_28_all : ∀ g ∈ goalChunk_28, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_28 at hg
  cases hg with
  | head =>
    exact prove_goal_217_from_pattern_58
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_218_from_pattern_59
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_219_from_pattern_116
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_220_from_pattern_84
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_221_from_pattern_62
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_222_from_pattern_84
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_223_from_pattern_62
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_224_from_pattern_61
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_29_all : ∀ g ∈ goalChunk_29, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_29 at hg
  cases hg with
  | head =>
    exact prove_goal_225_from_pattern_62
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_226_from_pattern_66
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_227_from_pattern_117
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_228_from_pattern_64
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_229_from_pattern_118
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_230_from_pattern_85
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_231_from_pattern_119
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_232_from_pattern_120
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_30_all : ∀ g ∈ goalChunk_30, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_30 at hg
  cases hg with
  | head =>
    exact prove_goal_233_from_pattern_90
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_234_from_pattern_121
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_235_from_pattern_122
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_236_from_pattern_123
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_237_from_pattern_124
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_238_from_pattern_74
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_239_from_pattern_110
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_240_from_pattern_111
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_31_all : ∀ g ∈ goalChunk_31, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_31 at hg
  cases hg with
  | head =>
    exact prove_goal_241_from_pattern_112
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_242_from_pattern_100
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_243_from_pattern_58
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_244_from_pattern_59
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_245_from_pattern_113
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_246_from_pattern_114
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_247_from_pattern_115
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_248_from_pattern_113
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_32_all : ∀ g ∈ goalChunk_32, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_32 at hg
  cases hg with
  | head =>
    exact prove_goal_249_from_pattern_114
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_250_from_pattern_112
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_251_from_pattern_125
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_252_from_pattern_58
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_253_from_pattern_59
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_254_from_pattern_78
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_255_from_pattern_76
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_256_from_pattern_126
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_33_all : ∀ g ∈ goalChunk_33, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_33 at hg
  cases hg with
  | head =>
    exact prove_goal_257_from_pattern_127
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_258_from_pattern_125
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_259_from_pattern_128
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_260_from_pattern_77
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_261_from_pattern_129
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_262_from_pattern_130
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_263_from_pattern_129
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_264_from_pattern_130
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_34_all : ∀ g ∈ goalChunk_34, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_34 at hg
  cases hg with
  | head =>
    exact prove_goal_265_from_pattern_131
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_266_from_pattern_132
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_267_from_pattern_127
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_268_from_pattern_125
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_269_from_pattern_128
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_270_from_pattern_133
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_271_from_pattern_127
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_272_from_pattern_125
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_35_all : ∀ g ∈ goalChunk_35, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_35 at hg
  cases hg with
  | head =>
    exact prove_goal_273_from_pattern_128
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_274_from_pattern_133
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_275_from_pattern_134
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_276_from_pattern_84
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_277_from_pattern_129
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_278_from_pattern_130
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_279_from_pattern_135
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_280_from_pattern_84
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_36_all : ∀ g ∈ goalChunk_36, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_36 at hg
  cases hg with
  | head =>
    exact prove_goal_281_from_pattern_127
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_282_from_pattern_125
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_283_from_pattern_136
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_284_from_pattern_137
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_285_from_pattern_128
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_286_from_pattern_125
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_287_from_pattern_128
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_288_from_pattern_138
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_37_all : ∀ g ∈ goalChunk_37, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_37 at hg
  cases hg with
  | head =>
    exact prove_goal_289_from_pattern_139
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_290_from_pattern_132
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_291_from_pattern_140
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_292_from_pattern_132
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_293_from_pattern_129
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_294_from_pattern_130
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_295_from_pattern_128
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_296_from_pattern_125
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_38_all : ∀ g ∈ goalChunk_38, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_38 at hg
  cases hg with
  | head =>
    exact prove_goal_297_from_pattern_128
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_298_from_pattern_138
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_299_from_pattern_128
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_300_from_pattern_125
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_301_from_pattern_128
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_302_from_pattern_138
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_303_from_pattern_134
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_304_from_pattern_84
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_39_all : ∀ g ∈ goalChunk_39, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_39 at hg
  cases hg with
  | head =>
    exact prove_goal_305_from_pattern_141
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_306_from_pattern_84
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_307_from_pattern_129
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_308_from_pattern_130
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_309_from_pattern_128
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_310_from_pattern_125
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_311_from_pattern_128
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_312_from_pattern_138
                | tail _ hg =>
                  cases hg

theorem gpt_main_all_goals : all_goals_stmt := by
  unfold all_goals_stmt goals
  exact (forall_mem_append_goal gpt_goal_chunk_1_all (forall_mem_append_goal gpt_goal_chunk_2_all (forall_mem_append_goal gpt_goal_chunk_3_all (forall_mem_append_goal gpt_goal_chunk_4_all (forall_mem_append_goal gpt_goal_chunk_5_all (forall_mem_append_goal gpt_goal_chunk_6_all (forall_mem_append_goal gpt_goal_chunk_7_all (forall_mem_append_goal gpt_goal_chunk_8_all (forall_mem_append_goal gpt_goal_chunk_9_all (forall_mem_append_goal gpt_goal_chunk_10_all (forall_mem_append_goal gpt_goal_chunk_11_all (forall_mem_append_goal gpt_goal_chunk_12_all (forall_mem_append_goal gpt_goal_chunk_13_all (forall_mem_append_goal gpt_goal_chunk_14_all (forall_mem_append_goal gpt_goal_chunk_15_all (forall_mem_append_goal gpt_goal_chunk_16_all (forall_mem_append_goal gpt_goal_chunk_17_all (forall_mem_append_goal gpt_goal_chunk_18_all (forall_mem_append_goal gpt_goal_chunk_19_all (forall_mem_append_goal gpt_goal_chunk_20_all (forall_mem_append_goal gpt_goal_chunk_21_all (forall_mem_append_goal gpt_goal_chunk_22_all (forall_mem_append_goal gpt_goal_chunk_23_all (forall_mem_append_goal gpt_goal_chunk_24_all (forall_mem_append_goal gpt_goal_chunk_25_all (forall_mem_append_goal gpt_goal_chunk_26_all (forall_mem_append_goal gpt_goal_chunk_27_all (forall_mem_append_goal gpt_goal_chunk_28_all (forall_mem_append_goal gpt_goal_chunk_29_all (forall_mem_append_goal gpt_goal_chunk_30_all (forall_mem_append_goal gpt_goal_chunk_31_all (forall_mem_append_goal gpt_goal_chunk_32_all (forall_mem_append_goal gpt_goal_chunk_33_all (forall_mem_append_goal gpt_goal_chunk_34_all (forall_mem_append_goal gpt_goal_chunk_35_all (forall_mem_append_goal gpt_goal_chunk_36_all (forall_mem_append_goal gpt_goal_chunk_37_all (forall_mem_append_goal gpt_goal_chunk_38_all gpt_goal_chunk_39_all))))))))))))))))))))))))))))))))))))))

end TrainVerify.Denote.GeneratedMain

