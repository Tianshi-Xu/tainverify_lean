/- Auto-generated main composition skeleton.
   This file is the place where segment/pattern proofs are composed
   into the full graph theorem.
-/
import denote.gpt2_small_ly12_segments.SegmentInstances
import denote.gpt2_small_ly12_segments.Instances

set_option maxRecDepth 20000
set_option linter.style.emptyLine false

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedPatternInstances
open TrainVerify.Denote.GeneratedSegmentInstances

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

/-- Full graph theorem placeholder.

The intended proof path is:
1. replace duplicated concrete goal proofs by reusable pattern instances;
2. partition `fullGraphSegment` into real layer/block segments;
3. compose segment relations using the coverage certificate above.
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
          exact prove_goal_4_from_segment_1_1
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_5_from_segment_1_1
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_6_from_segment_1_1
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_7_from_segment_1_1
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_8_from_segment_1_1
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_2_all : ∀ g ∈ goalChunk_2, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_2 at hg
  cases hg with
  | head =>
    exact prove_goal_9_from_segment_1_1
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_10_from_segment_1_1
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_11_from_segment_1_1
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_12_from_segment_2_1
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_13_from_segment_2_1
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_14_from_segment_2_1
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_15_from_segment_2_1
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_16_from_segment_2_1
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_3_all : ∀ g ∈ goalChunk_3, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_3 at hg
  cases hg with
  | head =>
    exact prove_goal_17_from_segment_2_1
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_18_from_segment_2_1
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_19_from_segment_2_1
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_20_from_segment_3_1
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_21_from_segment_3_1
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_22_from_segment_3_1
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_23_from_segment_3_1
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_24_from_segment_3_1
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_4_all : ∀ g ∈ goalChunk_4, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_4 at hg
  cases hg with
  | head =>
    exact prove_goal_25_from_segment_3_1
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_26_from_segment_3_1
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_27_from_segment_3_1
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_28_from_pattern_23
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_29_from_segment_1_2
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_30_from_segment_1_2
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_31_from_segment_1_2
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_32_from_segment_1_2
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_5_all : ∀ g ∈ goalChunk_5, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_5 at hg
  cases hg with
  | head =>
    exact prove_goal_33_from_segment_1_2
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_34_from_segment_1_2
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_35_from_segment_1_2
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_36_from_segment_1_2
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_37_from_segment_2_2
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_38_from_segment_2_2
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_39_from_segment_2_2
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_40_from_segment_2_2
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_6_all : ∀ g ∈ goalChunk_6, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_6 at hg
  cases hg with
  | head =>
    exact prove_goal_41_from_segment_2_2
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_42_from_segment_2_2
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_43_from_segment_2_2
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_44_from_segment_2_2
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_45_from_segment_3_2
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_46_from_segment_3_2
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_47_from_segment_3_2
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_48_from_segment_3_2
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_7_all : ∀ g ∈ goalChunk_7, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_7 at hg
  cases hg with
  | head =>
    exact prove_goal_49_from_segment_3_2
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_50_from_segment_3_2
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_51_from_segment_3_2
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_52_from_segment_3_2
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_53_from_pattern_36
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_54_from_segment_1_3
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_55_from_segment_1_3
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_56_from_segment_1_3
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_8_all : ∀ g ∈ goalChunk_8, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_8 at hg
  cases hg with
  | head =>
    exact prove_goal_57_from_segment_1_3
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_58_from_segment_1_3
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_59_from_segment_1_3
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_60_from_segment_1_3
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_61_from_segment_1_3
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_62_from_segment_2_3
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_63_from_segment_2_3
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_64_from_segment_2_3
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_9_all : ∀ g ∈ goalChunk_9, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_9 at hg
  cases hg with
  | head =>
    exact prove_goal_65_from_segment_2_3
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_66_from_segment_2_3
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_67_from_segment_2_3
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_68_from_segment_2_3
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_69_from_segment_2_3
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_70_from_segment_3_3
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_71_from_segment_3_3
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_72_from_segment_3_3
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_10_all : ∀ g ∈ goalChunk_10, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_10 at hg
  cases hg with
  | head =>
    exact prove_goal_73_from_segment_3_3
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_74_from_segment_3_3
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_75_from_segment_3_3
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_76_from_segment_3_3
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_77_from_segment_3_3
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_78_from_pattern_46
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_79_from_segment_1_4
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_80_from_segment_1_4
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_11_all : ∀ g ∈ goalChunk_11, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_11 at hg
  cases hg with
  | head =>
    exact prove_goal_81_from_segment_1_4
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_82_from_segment_1_4
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_83_from_segment_1_4
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_84_from_segment_1_4
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_85_from_segment_1_4
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_86_from_segment_1_4
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_87_from_segment_2_4
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_88_from_segment_2_4
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_12_all : ∀ g ∈ goalChunk_12, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_12 at hg
  cases hg with
  | head =>
    exact prove_goal_89_from_segment_2_4
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_90_from_segment_2_4
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_91_from_segment_2_4
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_92_from_segment_2_4
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_93_from_segment_2_4
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_94_from_segment_2_4
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_95_from_segment_3_4
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_96_from_segment_3_4
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_13_all : ∀ g ∈ goalChunk_13, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_13 at hg
  cases hg with
  | head =>
    exact prove_goal_97_from_segment_3_4
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_98_from_segment_3_4
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_99_from_segment_3_4
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_100_from_segment_3_4
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_101_from_segment_3_4
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_102_from_segment_3_4
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_103_from_pattern_46
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_104_from_segment_1_5
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_14_all : ∀ g ∈ goalChunk_14, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_14 at hg
  cases hg with
  | head =>
    exact prove_goal_105_from_segment_1_5
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_106_from_segment_1_5
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_107_from_segment_1_5
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_108_from_segment_1_5
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_109_from_segment_1_5
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_110_from_segment_1_5
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_111_from_segment_1_5
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_112_from_segment_2_5
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_15_all : ∀ g ∈ goalChunk_15, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_15 at hg
  cases hg with
  | head =>
    exact prove_goal_113_from_segment_2_5
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_114_from_segment_2_5
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_115_from_segment_2_5
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_116_from_segment_2_5
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_117_from_segment_2_5
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_118_from_segment_2_5
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_119_from_segment_2_5
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_120_from_segment_3_5
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_16_all : ∀ g ∈ goalChunk_16, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_16 at hg
  cases hg with
  | head =>
    exact prove_goal_121_from_segment_3_5
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_122_from_segment_3_5
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_123_from_segment_3_5
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_124_from_segment_3_5
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_125_from_segment_3_5
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_126_from_segment_3_5
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_127_from_segment_3_5
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_128_from_pattern_23
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_17_all : ∀ g ∈ goalChunk_17, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_17 at hg
  cases hg with
  | head =>
    exact prove_goal_129_from_segment_1_6
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_130_from_segment_1_6
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_131_from_segment_1_6
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_132_from_segment_1_6
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_133_from_segment_1_6
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_134_from_segment_1_6
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_135_from_segment_1_6
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_136_from_segment_1_6
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_18_all : ∀ g ∈ goalChunk_18, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_18 at hg
  cases hg with
  | head =>
    exact prove_goal_137_from_segment_2_6
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_138_from_segment_2_6
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_139_from_segment_2_6
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_140_from_segment_2_6
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_141_from_segment_2_6
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_142_from_segment_2_6
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_143_from_segment_2_6
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_144_from_segment_2_6
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_19_all : ∀ g ∈ goalChunk_19, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_19 at hg
  cases hg with
  | head =>
    exact prove_goal_145_from_segment_3_6
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_146_from_segment_3_6
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_147_from_segment_3_6
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_148_from_segment_3_6
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_149_from_segment_3_6
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_150_from_segment_3_6
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_151_from_segment_3_6
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_152_from_segment_3_6
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_20_all : ∀ g ∈ goalChunk_20, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_20 at hg
  cases hg with
  | head =>
    exact prove_goal_153_from_pattern_66
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_154_from_segment_1_7
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_155_from_segment_1_7
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_156_from_segment_1_7
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_157_from_segment_1_7
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_158_from_segment_1_7
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_159_from_segment_1_7
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_160_from_segment_1_7
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_21_all : ∀ g ∈ goalChunk_21, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_21 at hg
  cases hg with
  | head =>
    exact prove_goal_161_from_segment_1_7
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_162_from_segment_2_7
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_163_from_segment_2_7
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_164_from_segment_2_7
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_165_from_segment_2_7
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_166_from_segment_2_7
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_167_from_segment_2_7
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_168_from_segment_2_7
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_22_all : ∀ g ∈ goalChunk_22, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_22 at hg
  cases hg with
  | head =>
    exact prove_goal_169_from_segment_2_7
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_170_from_segment_3_7
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_171_from_segment_3_7
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_172_from_segment_3_7
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_173_from_segment_3_7
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_174_from_segment_3_7
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_175_from_segment_3_7
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_176_from_segment_3_7
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_23_all : ∀ g ∈ goalChunk_23, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_23 at hg
  cases hg with
  | head =>
    exact prove_goal_177_from_segment_3_7
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_178_from_pattern_66
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_179_from_segment_1_8
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_180_from_segment_1_8
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_181_from_segment_1_8
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_182_from_segment_1_8
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_183_from_segment_1_8
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_184_from_segment_1_8
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_24_all : ∀ g ∈ goalChunk_24, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_24 at hg
  cases hg with
  | head =>
    exact prove_goal_185_from_segment_1_8
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_186_from_segment_1_8
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_187_from_segment_2_8
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_188_from_segment_2_8
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_189_from_segment_2_8
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_190_from_segment_2_8
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_191_from_segment_2_8
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_192_from_segment_2_8
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_25_all : ∀ g ∈ goalChunk_25, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_25 at hg
  cases hg with
  | head =>
    exact prove_goal_193_from_segment_2_8
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_194_from_segment_2_8
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_195_from_segment_3_8
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_196_from_segment_3_8
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_197_from_segment_3_8
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_198_from_segment_3_8
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_199_from_segment_3_8
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_200_from_segment_3_8
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_26_all : ∀ g ∈ goalChunk_26, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_26 at hg
  cases hg with
  | head =>
    exact prove_goal_201_from_segment_3_8
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_202_from_segment_3_8
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_203_from_pattern_46
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_204_from_segment_1_9
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_205_from_segment_1_9
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_206_from_segment_1_9
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_207_from_segment_1_9
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_208_from_segment_1_9
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_27_all : ∀ g ∈ goalChunk_27, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_27 at hg
  cases hg with
  | head =>
    exact prove_goal_209_from_segment_1_9
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_210_from_segment_1_9
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_211_from_segment_1_9
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_212_from_segment_2_9
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_213_from_segment_2_9
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_214_from_segment_2_9
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_215_from_segment_2_9
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_216_from_segment_2_9
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_28_all : ∀ g ∈ goalChunk_28, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_28 at hg
  cases hg with
  | head =>
    exact prove_goal_217_from_segment_2_9
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_218_from_segment_2_9
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_219_from_segment_2_9
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_220_from_segment_3_9
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_221_from_segment_3_9
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_222_from_segment_3_9
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_223_from_segment_3_9
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_224_from_segment_3_9
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_29_all : ∀ g ∈ goalChunk_29, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_29 at hg
  cases hg with
  | head =>
    exact prove_goal_225_from_segment_3_9
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_226_from_segment_3_9
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_227_from_segment_3_9
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_228_from_pattern_36
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_229_from_segment_1_10
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_230_from_segment_1_10
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_231_from_segment_1_10
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_232_from_segment_1_10
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_30_all : ∀ g ∈ goalChunk_30, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_30 at hg
  cases hg with
  | head =>
    exact prove_goal_233_from_segment_1_10
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_234_from_segment_1_10
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_235_from_segment_1_10
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_236_from_segment_1_10
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_237_from_segment_2_10
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_238_from_segment_2_10
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_239_from_segment_2_10
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_240_from_segment_2_10
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_31_all : ∀ g ∈ goalChunk_31, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_31 at hg
  cases hg with
  | head =>
    exact prove_goal_241_from_segment_2_10
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_242_from_segment_2_10
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_243_from_segment_2_10
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_244_from_segment_2_10
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_245_from_segment_3_10
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_246_from_segment_3_10
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_247_from_segment_3_10
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_248_from_segment_3_10
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_32_all : ∀ g ∈ goalChunk_32, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_32 at hg
  cases hg with
  | head =>
    exact prove_goal_249_from_segment_3_10
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_250_from_segment_3_10
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_251_from_segment_3_10
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_252_from_segment_3_10
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_253_from_pattern_7
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_254_from_segment_1_11
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_255_from_segment_1_11
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_256_from_segment_1_11
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_33_all : ∀ g ∈ goalChunk_33, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_33 at hg
  cases hg with
  | head =>
    exact prove_goal_257_from_segment_1_11
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_258_from_segment_1_11
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_259_from_segment_1_11
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_260_from_segment_1_11
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_261_from_segment_1_11
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_262_from_segment_2_11
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_263_from_segment_2_11
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_264_from_segment_2_11
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_34_all : ∀ g ∈ goalChunk_34, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_34 at hg
  cases hg with
  | head =>
    exact prove_goal_265_from_segment_2_11
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_266_from_segment_2_11
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_267_from_segment_2_11
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_268_from_segment_2_11
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_269_from_segment_2_11
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_270_from_segment_3_11
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_271_from_segment_3_11
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_272_from_segment_3_11
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_35_all : ∀ g ∈ goalChunk_35, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_35 at hg
  cases hg with
  | head =>
    exact prove_goal_273_from_segment_3_11
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_274_from_segment_3_11
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_275_from_segment_3_11
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_276_from_segment_3_11
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_277_from_segment_3_11
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_278_from_pattern_46
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_279_from_segment_1_12
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_280_from_segment_1_12
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_36_all : ∀ g ∈ goalChunk_36, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_36 at hg
  cases hg with
  | head =>
    exact prove_goal_281_from_segment_1_12
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_282_from_segment_1_12
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_283_from_segment_1_12
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_284_from_segment_1_12
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_285_from_segment_1_12
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_286_from_segment_1_12
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_287_from_segment_2_12
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_288_from_segment_2_12
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_37_all : ∀ g ∈ goalChunk_37, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_37 at hg
  cases hg with
  | head =>
    exact prove_goal_289_from_segment_2_12
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_290_from_segment_2_12
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_291_from_segment_2_12
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_292_from_segment_2_12
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_293_from_segment_2_12
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_294_from_segment_2_12
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_295_from_segment_3_12
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_296_from_segment_3_12
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_38_all : ∀ g ∈ goalChunk_38, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_38 at hg
  cases hg with
  | head =>
    exact prove_goal_297_from_segment_3_12
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_298_from_segment_3_12
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_299_from_segment_3_12
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_300_from_segment_3_12
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_301_from_segment_3_12
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_302_from_segment_3_12
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_303_from_pattern_7
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_304_from_pattern_47
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_39_all : ∀ g ∈ goalChunk_39, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_39 at hg
  cases hg with
  | head =>
    exact prove_goal_305_from_pattern_87
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_306_from_pattern_36
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_307_from_pattern_88
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_308_from_pattern_89
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_309_from_pattern_90
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_310_from_segment_4_1
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_311_from_segment_4_1
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_312_from_segment_4_1
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_40_all : ∀ g ∈ goalChunk_40, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_40 at hg
  cases hg with
  | head =>
    exact prove_goal_313_from_segment_4_1
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_314_from_segment_4_1
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_315_from_segment_4_1
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_316_from_segment_4_1
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_317_from_segment_4_1
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_318_from_segment_5_1
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_319_from_segment_5_1
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_320_from_segment_5_1
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_41_all : ∀ g ∈ goalChunk_41, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_41 at hg
  cases hg with
  | head =>
    exact prove_goal_321_from_segment_5_1
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_322_from_segment_5_1
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_323_from_segment_5_1
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_324_from_segment_5_1
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_325_from_segment_5_1
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_326_from_segment_6_1
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_327_from_segment_6_1
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_328_from_segment_6_1
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_42_all : ∀ g ∈ goalChunk_42, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_42 at hg
  cases hg with
  | head =>
    exact prove_goal_329_from_segment_6_1
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_330_from_segment_6_1
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_331_from_segment_6_1
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_332_from_segment_6_1
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_333_from_segment_6_1
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_334_from_segment_7_1
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_335_from_segment_7_1
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_336_from_segment_7_1
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_43_all : ∀ g ∈ goalChunk_43, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_43 at hg
  cases hg with
  | head =>
    exact prove_goal_337_from_segment_7_1
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_338_from_segment_7_1
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_339_from_segment_7_1
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_340_from_segment_7_1
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_341_from_segment_7_1
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_342_from_segment_8_1
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_343_from_segment_8_1
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_344_from_segment_8_1
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_44_all : ∀ g ∈ goalChunk_44, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_44 at hg
  cases hg with
  | head =>
    exact prove_goal_345_from_segment_4_2
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_346_from_segment_4_2
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_347_from_segment_4_2
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_348_from_segment_4_2
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_349_from_segment_4_2
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_350_from_segment_4_2
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_351_from_segment_4_2
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_352_from_segment_4_2
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_45_all : ∀ g ∈ goalChunk_45, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_45 at hg
  cases hg with
  | head =>
    exact prove_goal_353_from_segment_5_2
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_354_from_segment_5_2
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_355_from_segment_5_2
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_356_from_segment_5_2
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_357_from_segment_5_2
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_358_from_segment_5_2
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_359_from_segment_5_2
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_360_from_segment_5_2
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_46_all : ∀ g ∈ goalChunk_46, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_46 at hg
  cases hg with
  | head =>
    exact prove_goal_361_from_segment_6_2
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_362_from_segment_6_2
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_363_from_segment_6_2
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_364_from_segment_6_2
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_365_from_segment_6_2
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_366_from_segment_6_2
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_367_from_segment_6_2
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_368_from_segment_6_2
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_47_all : ∀ g ∈ goalChunk_47, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_47 at hg
  cases hg with
  | head =>
    exact prove_goal_369_from_segment_7_2
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_370_from_segment_7_2
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_371_from_segment_7_2
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_372_from_segment_7_2
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_373_from_segment_7_2
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_374_from_segment_7_2
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_375_from_segment_7_2
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_376_from_segment_7_2
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_48_all : ∀ g ∈ goalChunk_48, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_48 at hg
  cases hg with
  | head =>
    exact prove_goal_377_from_segment_8_2
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_378_from_segment_8_2
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_379_from_segment_8_2
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_380_from_segment_4_3
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_381_from_segment_4_3
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_382_from_segment_4_3
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_383_from_segment_4_3
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_384_from_segment_4_3
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_49_all : ∀ g ∈ goalChunk_49, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_49 at hg
  cases hg with
  | head =>
    exact prove_goal_385_from_segment_4_3
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_386_from_segment_4_3
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_387_from_segment_4_3
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_388_from_segment_5_3
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_389_from_segment_5_3
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_390_from_segment_5_3
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_391_from_segment_5_3
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_392_from_segment_5_3
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_50_all : ∀ g ∈ goalChunk_50, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_50 at hg
  cases hg with
  | head =>
    exact prove_goal_393_from_segment_5_3
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_394_from_segment_5_3
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_395_from_segment_5_3
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_396_from_segment_6_3
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_397_from_segment_6_3
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_398_from_segment_6_3
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_399_from_segment_6_3
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_400_from_segment_6_3
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_51_all : ∀ g ∈ goalChunk_51, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_51 at hg
  cases hg with
  | head =>
    exact prove_goal_401_from_segment_6_3
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_402_from_segment_6_3
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_403_from_segment_6_3
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_404_from_segment_7_3
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_405_from_segment_7_3
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_406_from_segment_7_3
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_407_from_segment_7_3
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_408_from_segment_7_3
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_52_all : ∀ g ∈ goalChunk_52, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_52 at hg
  cases hg with
  | head =>
    exact prove_goal_409_from_segment_7_3
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_410_from_segment_7_3
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_411_from_segment_7_3
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_412_from_segment_8_3
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_413_from_segment_8_3
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_414_from_segment_8_3
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_415_from_segment_4_4
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_416_from_segment_4_4
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_53_all : ∀ g ∈ goalChunk_53, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_53 at hg
  cases hg with
  | head =>
    exact prove_goal_417_from_segment_4_4
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_418_from_segment_4_4
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_419_from_segment_4_4
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_420_from_segment_4_4
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_421_from_segment_4_4
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_422_from_segment_4_4
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_423_from_segment_5_4
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_424_from_segment_5_4
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_54_all : ∀ g ∈ goalChunk_54, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_54 at hg
  cases hg with
  | head =>
    exact prove_goal_425_from_segment_5_4
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_426_from_segment_5_4
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_427_from_segment_5_4
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_428_from_segment_5_4
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_429_from_segment_5_4
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_430_from_segment_5_4
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_431_from_segment_6_4
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_432_from_segment_6_4
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_55_all : ∀ g ∈ goalChunk_55, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_55 at hg
  cases hg with
  | head =>
    exact prove_goal_433_from_segment_6_4
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_434_from_segment_6_4
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_435_from_segment_6_4
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_436_from_segment_6_4
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_437_from_segment_6_4
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_438_from_segment_6_4
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_439_from_segment_7_4
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_440_from_segment_7_4
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_56_all : ∀ g ∈ goalChunk_56, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_56 at hg
  cases hg with
  | head =>
    exact prove_goal_441_from_segment_7_4
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_442_from_segment_7_4
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_443_from_segment_7_4
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_444_from_segment_7_4
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_445_from_segment_7_4
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_446_from_segment_7_4
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_447_from_segment_8_4
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_448_from_segment_8_4
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_57_all : ∀ g ∈ goalChunk_57, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_57 at hg
  cases hg with
  | head =>
    exact prove_goal_449_from_segment_8_4
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_450_from_segment_4_5
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_451_from_segment_4_5
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_452_from_segment_4_5
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_453_from_segment_4_5
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_454_from_segment_4_5
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_455_from_segment_4_5
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_456_from_segment_4_5
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_58_all : ∀ g ∈ goalChunk_58, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_58 at hg
  cases hg with
  | head =>
    exact prove_goal_457_from_segment_4_5
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_458_from_segment_5_5
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_459_from_segment_5_5
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_460_from_segment_5_5
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_461_from_segment_5_5
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_462_from_segment_5_5
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_463_from_segment_5_5
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_464_from_segment_5_5
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_59_all : ∀ g ∈ goalChunk_59, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_59 at hg
  cases hg with
  | head =>
    exact prove_goal_465_from_segment_5_5
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_466_from_segment_6_5
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_467_from_segment_6_5
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_468_from_segment_6_5
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_469_from_segment_6_5
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_470_from_segment_6_5
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_471_from_segment_6_5
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_472_from_segment_6_5
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_60_all : ∀ g ∈ goalChunk_60, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_60 at hg
  cases hg with
  | head =>
    exact prove_goal_473_from_segment_6_5
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_474_from_segment_7_5
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_475_from_segment_7_5
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_476_from_segment_7_5
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_477_from_segment_7_5
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_478_from_segment_7_5
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_479_from_segment_7_5
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_480_from_segment_7_5
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_61_all : ∀ g ∈ goalChunk_61, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_61 at hg
  cases hg with
  | head =>
    exact prove_goal_481_from_segment_7_5
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_482_from_segment_8_5
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_483_from_segment_8_5
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_484_from_segment_8_5
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_485_from_segment_4_6
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_486_from_segment_4_6
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_487_from_segment_4_6
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_488_from_segment_4_6
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_62_all : ∀ g ∈ goalChunk_62, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_62 at hg
  cases hg with
  | head =>
    exact prove_goal_489_from_segment_4_6
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_490_from_segment_4_6
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_491_from_segment_4_6
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_492_from_segment_4_6
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_493_from_segment_5_6
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_494_from_segment_5_6
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_495_from_segment_5_6
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_496_from_segment_5_6
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_63_all : ∀ g ∈ goalChunk_63, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_63 at hg
  cases hg with
  | head =>
    exact prove_goal_497_from_segment_5_6
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_498_from_segment_5_6
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_499_from_segment_5_6
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_500_from_segment_5_6
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_501_from_segment_6_6
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_502_from_segment_6_6
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_503_from_segment_6_6
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_504_from_segment_6_6
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_64_all : ∀ g ∈ goalChunk_64, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_64 at hg
  cases hg with
  | head =>
    exact prove_goal_505_from_segment_6_6
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_506_from_segment_6_6
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_507_from_segment_6_6
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_508_from_segment_6_6
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_509_from_segment_7_6
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_510_from_segment_7_6
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_511_from_segment_7_6
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_512_from_segment_7_6
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_65_all : ∀ g ∈ goalChunk_65, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_65 at hg
  cases hg with
  | head =>
    exact prove_goal_513_from_segment_7_6
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_514_from_segment_7_6
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_515_from_segment_7_6
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_516_from_segment_7_6
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_517_from_segment_8_6
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_518_from_segment_8_6
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_519_from_segment_8_6
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_520_from_segment_4_7
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_66_all : ∀ g ∈ goalChunk_66, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_66 at hg
  cases hg with
  | head =>
    exact prove_goal_521_from_segment_4_7
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_522_from_segment_4_7
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_523_from_segment_4_7
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_524_from_segment_4_7
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_525_from_segment_4_7
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_526_from_segment_4_7
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_527_from_segment_4_7
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_528_from_segment_5_7
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_67_all : ∀ g ∈ goalChunk_67, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_67 at hg
  cases hg with
  | head =>
    exact prove_goal_529_from_segment_5_7
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_530_from_segment_5_7
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_531_from_segment_5_7
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_532_from_segment_5_7
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_533_from_segment_5_7
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_534_from_segment_5_7
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_535_from_segment_5_7
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_536_from_segment_6_7
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_68_all : ∀ g ∈ goalChunk_68, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_68 at hg
  cases hg with
  | head =>
    exact prove_goal_537_from_segment_6_7
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_538_from_segment_6_7
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_539_from_segment_6_7
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_540_from_segment_6_7
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_541_from_segment_6_7
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_542_from_segment_6_7
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_543_from_segment_6_7
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_544_from_segment_7_7
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_69_all : ∀ g ∈ goalChunk_69, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_69 at hg
  cases hg with
  | head =>
    exact prove_goal_545_from_segment_7_7
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_546_from_segment_7_7
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_547_from_segment_7_7
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_548_from_segment_7_7
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_549_from_segment_7_7
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_550_from_segment_7_7
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_551_from_segment_7_7
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_552_from_segment_8_7
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_70_all : ∀ g ∈ goalChunk_70, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_70 at hg
  cases hg with
  | head =>
    exact prove_goal_553_from_segment_8_7
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_554_from_segment_8_7
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_555_from_segment_4_8
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_556_from_segment_4_8
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_557_from_segment_4_8
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_558_from_segment_4_8
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_559_from_segment_4_8
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_560_from_segment_4_8
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_71_all : ∀ g ∈ goalChunk_71, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_71 at hg
  cases hg with
  | head =>
    exact prove_goal_561_from_segment_4_8
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_562_from_segment_4_8
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_563_from_segment_5_8
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_564_from_segment_5_8
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_565_from_segment_5_8
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_566_from_segment_5_8
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_567_from_segment_5_8
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_568_from_segment_5_8
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_72_all : ∀ g ∈ goalChunk_72, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_72 at hg
  cases hg with
  | head =>
    exact prove_goal_569_from_segment_5_8
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_570_from_segment_5_8
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_571_from_segment_6_8
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_572_from_segment_6_8
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_573_from_segment_6_8
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_574_from_segment_6_8
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_575_from_segment_6_8
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_576_from_segment_6_8
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_73_all : ∀ g ∈ goalChunk_73, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_73 at hg
  cases hg with
  | head =>
    exact prove_goal_577_from_segment_6_8
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_578_from_segment_6_8
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_579_from_segment_7_8
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_580_from_segment_7_8
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_581_from_segment_7_8
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_582_from_segment_7_8
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_583_from_segment_7_8
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_584_from_segment_7_8
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_74_all : ∀ g ∈ goalChunk_74, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_74 at hg
  cases hg with
  | head =>
    exact prove_goal_585_from_segment_7_8
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_586_from_segment_7_8
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_587_from_segment_8_8
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_588_from_segment_8_8
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_589_from_segment_8_8
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_590_from_segment_4_9
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_591_from_segment_4_9
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_592_from_segment_4_9
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_75_all : ∀ g ∈ goalChunk_75, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_75 at hg
  cases hg with
  | head =>
    exact prove_goal_593_from_segment_4_9
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_594_from_segment_4_9
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_595_from_segment_4_9
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_596_from_segment_4_9
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_597_from_segment_4_9
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_598_from_segment_5_9
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_599_from_segment_5_9
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_600_from_segment_5_9
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_76_all : ∀ g ∈ goalChunk_76, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_76 at hg
  cases hg with
  | head =>
    exact prove_goal_601_from_segment_5_9
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_602_from_segment_5_9
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_603_from_segment_5_9
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_604_from_segment_5_9
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_605_from_segment_5_9
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_606_from_segment_6_9
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_607_from_segment_6_9
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_608_from_segment_6_9
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_77_all : ∀ g ∈ goalChunk_77, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_77 at hg
  cases hg with
  | head =>
    exact prove_goal_609_from_segment_6_9
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_610_from_segment_6_9
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_611_from_segment_6_9
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_612_from_segment_6_9
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_613_from_segment_6_9
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_614_from_segment_7_9
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_615_from_segment_7_9
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_616_from_segment_7_9
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_78_all : ∀ g ∈ goalChunk_78, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_78 at hg
  cases hg with
  | head =>
    exact prove_goal_617_from_segment_7_9
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_618_from_segment_7_9
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_619_from_segment_7_9
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_620_from_segment_7_9
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_621_from_segment_7_9
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_622_from_segment_8_9
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_623_from_segment_8_9
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_624_from_segment_8_9
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_79_all : ∀ g ∈ goalChunk_79, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_79 at hg
  cases hg with
  | head =>
    exact prove_goal_625_from_segment_4_10
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_626_from_segment_4_10
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_627_from_segment_4_10
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_628_from_segment_4_10
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_629_from_segment_4_10
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_630_from_segment_4_10
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_631_from_segment_4_10
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_632_from_segment_4_10
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_80_all : ∀ g ∈ goalChunk_80, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_80 at hg
  cases hg with
  | head =>
    exact prove_goal_633_from_segment_5_10
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_634_from_segment_5_10
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_635_from_segment_5_10
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_636_from_segment_5_10
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_637_from_segment_5_10
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_638_from_segment_5_10
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_639_from_segment_5_10
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_640_from_segment_5_10
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_81_all : ∀ g ∈ goalChunk_81, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_81 at hg
  cases hg with
  | head =>
    exact prove_goal_641_from_segment_6_10
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_642_from_segment_6_10
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_643_from_segment_6_10
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_644_from_segment_6_10
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_645_from_segment_6_10
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_646_from_segment_6_10
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_647_from_segment_6_10
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_648_from_segment_6_10
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_82_all : ∀ g ∈ goalChunk_82, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_82 at hg
  cases hg with
  | head =>
    exact prove_goal_649_from_segment_7_10
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_650_from_segment_7_10
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_651_from_segment_7_10
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_652_from_segment_7_10
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_653_from_segment_7_10
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_654_from_segment_7_10
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_655_from_segment_7_10
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_656_from_segment_7_10
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_83_all : ∀ g ∈ goalChunk_83, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_83 at hg
  cases hg with
  | head =>
    exact prove_goal_657_from_segment_8_10
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_658_from_segment_8_10
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_659_from_segment_8_10
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_660_from_segment_4_11
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_661_from_segment_4_11
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_662_from_segment_4_11
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_663_from_segment_4_11
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_664_from_segment_4_11
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_84_all : ∀ g ∈ goalChunk_84, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_84 at hg
  cases hg with
  | head =>
    exact prove_goal_665_from_segment_4_11
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_666_from_segment_4_11
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_667_from_segment_4_11
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_668_from_segment_5_11
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_669_from_segment_5_11
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_670_from_segment_5_11
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_671_from_segment_5_11
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_672_from_segment_5_11
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_85_all : ∀ g ∈ goalChunk_85, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_85 at hg
  cases hg with
  | head =>
    exact prove_goal_673_from_segment_5_11
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_674_from_segment_5_11
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_675_from_segment_5_11
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_676_from_segment_6_11
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_677_from_segment_6_11
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_678_from_segment_6_11
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_679_from_segment_6_11
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_680_from_segment_6_11
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_86_all : ∀ g ∈ goalChunk_86, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_86 at hg
  cases hg with
  | head =>
    exact prove_goal_681_from_segment_6_11
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_682_from_segment_6_11
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_683_from_segment_6_11
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_684_from_segment_7_11
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_685_from_segment_7_11
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_686_from_segment_7_11
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_687_from_segment_7_11
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_688_from_segment_7_11
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_87_all : ∀ g ∈ goalChunk_87, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_87 at hg
  cases hg with
  | head =>
    exact prove_goal_689_from_segment_7_11
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_690_from_segment_7_11
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_691_from_segment_7_11
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_692_from_segment_8_11
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_693_from_segment_8_11
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_694_from_segment_8_11
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_695_from_segment_4_12
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_696_from_segment_4_12
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_88_all : ∀ g ∈ goalChunk_88, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_88 at hg
  cases hg with
  | head =>
    exact prove_goal_697_from_segment_4_12
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_698_from_segment_4_12
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_699_from_segment_4_12
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_700_from_segment_4_12
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_701_from_segment_4_12
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_702_from_segment_4_12
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_703_from_segment_5_12
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_704_from_segment_5_12
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_89_all : ∀ g ∈ goalChunk_89, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_89 at hg
  cases hg with
  | head =>
    exact prove_goal_705_from_segment_5_12
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_706_from_segment_5_12
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_707_from_segment_5_12
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_708_from_segment_5_12
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_709_from_segment_5_12
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_710_from_segment_5_12
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_711_from_segment_6_12
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_712_from_segment_6_12
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_90_all : ∀ g ∈ goalChunk_90, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_90 at hg
  cases hg with
  | head =>
    exact prove_goal_713_from_segment_6_12
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_714_from_segment_6_12
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_715_from_segment_6_12
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_716_from_segment_6_12
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_717_from_segment_6_12
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_718_from_segment_6_12
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_719_from_segment_7_12
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_720_from_segment_7_12
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_91_all : ∀ g ∈ goalChunk_91, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_91 at hg
  cases hg with
  | head =>
    exact prove_goal_721_from_segment_7_12
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_722_from_segment_7_12
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_723_from_segment_7_12
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_724_from_segment_7_12
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_725_from_segment_7_12
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_726_from_segment_7_12
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_727_from_segment_8_12
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_728_from_segment_8_12
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_92_all : ∀ g ∈ goalChunk_92, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_92 at hg
  cases hg with
  | head =>
    exact prove_goal_729_from_segment_8_12
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_730_from_pattern_151
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_731_from_pattern_203
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_732_from_pattern_204
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_733_from_pattern_205
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_734_from_pattern_134
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_735_from_pattern_135
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_736_from_pattern_206
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_93_all : ∀ g ∈ goalChunk_93, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_93 at hg
  cases hg with
  | head =>
    exact prove_goal_737_from_segment_9_1
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_738_from_segment_9_1
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_739_from_segment_9_1
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_740_from_segment_9_1
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_741_from_segment_9_1
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_742_from_segment_9_1
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_743_from_segment_9_1
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_744_from_segment_9_1
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_94_all : ∀ g ∈ goalChunk_94, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_94 at hg
  cases hg with
  | head =>
    exact prove_goal_745_from_segment_10_1
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_746_from_segment_10_1
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_747_from_segment_10_1
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_748_from_segment_10_1
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_749_from_segment_10_1
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_750_from_segment_10_1
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_751_from_segment_9_2
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_752_from_segment_9_2
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_95_all : ∀ g ∈ goalChunk_95, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_95 at hg
  cases hg with
  | head =>
    exact prove_goal_753_from_segment_9_2
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_754_from_segment_9_2
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_755_from_segment_9_2
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_756_from_segment_9_2
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_757_from_segment_9_2
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_758_from_segment_9_2
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_759_from_segment_10_2
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_760_from_segment_10_2
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_96_all : ∀ g ∈ goalChunk_96, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_96 at hg
  cases hg with
  | head =>
    exact prove_goal_761_from_segment_10_2
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_762_from_segment_10_2
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_763_from_segment_10_2
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_764_from_segment_10_2
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_765_from_segment_9_3
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_766_from_segment_9_3
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_767_from_segment_9_3
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_768_from_segment_9_3
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_97_all : ∀ g ∈ goalChunk_97, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_97 at hg
  cases hg with
  | head =>
    exact prove_goal_769_from_segment_9_3
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_770_from_segment_9_3
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_771_from_segment_9_3
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_772_from_segment_9_3
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_773_from_segment_10_3
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_774_from_segment_10_3
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_775_from_segment_10_3
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_776_from_segment_10_3
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_98_all : ∀ g ∈ goalChunk_98, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_98 at hg
  cases hg with
  | head =>
    exact prove_goal_777_from_segment_10_3
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_778_from_segment_10_3
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_779_from_segment_9_4
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_780_from_segment_9_4
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_781_from_segment_9_4
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_782_from_segment_9_4
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_783_from_segment_9_4
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_784_from_segment_9_4
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_99_all : ∀ g ∈ goalChunk_99, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_99 at hg
  cases hg with
  | head =>
    exact prove_goal_785_from_segment_9_4
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_786_from_segment_9_4
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_787_from_segment_10_4
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_788_from_segment_10_4
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_789_from_segment_10_4
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_790_from_segment_10_4
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_791_from_segment_10_4
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_792_from_segment_10_4
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_100_all : ∀ g ∈ goalChunk_100, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_100 at hg
  cases hg with
  | head =>
    exact prove_goal_793_from_segment_9_5
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_794_from_segment_9_5
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_795_from_segment_9_5
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_796_from_segment_9_5
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_797_from_segment_9_5
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_798_from_segment_9_5
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_799_from_segment_9_5
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_800_from_segment_9_5
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_101_all : ∀ g ∈ goalChunk_101, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_101 at hg
  cases hg with
  | head =>
    exact prove_goal_801_from_segment_10_5
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_802_from_segment_10_5
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_803_from_segment_10_5
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_804_from_segment_10_5
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_805_from_segment_10_5
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_806_from_segment_10_5
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_807_from_segment_9_6
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_808_from_segment_9_6
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_102_all : ∀ g ∈ goalChunk_102, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_102 at hg
  cases hg with
  | head =>
    exact prove_goal_809_from_segment_9_6
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_810_from_segment_9_6
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_811_from_segment_9_6
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_812_from_segment_9_6
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_813_from_segment_9_6
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_814_from_segment_9_6
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_815_from_segment_10_6
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_816_from_segment_10_6
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_103_all : ∀ g ∈ goalChunk_103, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_103 at hg
  cases hg with
  | head =>
    exact prove_goal_817_from_segment_10_6
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_818_from_segment_10_6
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_819_from_segment_10_6
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_820_from_segment_10_6
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_821_from_segment_9_7
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_822_from_segment_9_7
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_823_from_segment_9_7
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_824_from_segment_9_7
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_104_all : ∀ g ∈ goalChunk_104, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_104 at hg
  cases hg with
  | head =>
    exact prove_goal_825_from_segment_9_7
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_826_from_segment_9_7
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_827_from_segment_9_7
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_828_from_segment_9_7
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_829_from_segment_10_7
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_830_from_segment_10_7
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_831_from_segment_10_7
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_832_from_segment_10_7
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_105_all : ∀ g ∈ goalChunk_105, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_105 at hg
  cases hg with
  | head =>
    exact prove_goal_833_from_segment_10_7
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_834_from_segment_10_7
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_835_from_segment_9_8
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_836_from_segment_9_8
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_837_from_segment_9_8
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_838_from_segment_9_8
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_839_from_segment_9_8
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_840_from_segment_9_8
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_106_all : ∀ g ∈ goalChunk_106, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_106 at hg
  cases hg with
  | head =>
    exact prove_goal_841_from_segment_9_8
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_842_from_segment_9_8
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_843_from_segment_10_8
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_844_from_segment_10_8
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_845_from_segment_10_8
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_846_from_segment_10_8
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_847_from_segment_10_8
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_848_from_segment_10_8
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_107_all : ∀ g ∈ goalChunk_107, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_107 at hg
  cases hg with
  | head =>
    exact prove_goal_849_from_segment_9_9
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_850_from_segment_9_9
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_851_from_segment_9_9
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_852_from_segment_9_9
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_853_from_segment_9_9
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_854_from_segment_9_9
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_855_from_segment_9_9
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_856_from_segment_9_9
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_108_all : ∀ g ∈ goalChunk_108, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_108 at hg
  cases hg with
  | head =>
    exact prove_goal_857_from_segment_10_9
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_858_from_segment_10_9
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_859_from_segment_10_9
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_860_from_segment_10_9
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_861_from_segment_10_9
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_862_from_segment_10_9
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_863_from_segment_9_10
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_864_from_segment_9_10
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_109_all : ∀ g ∈ goalChunk_109, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_109 at hg
  cases hg with
  | head =>
    exact prove_goal_865_from_segment_9_10
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_866_from_segment_9_10
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_867_from_segment_9_10
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_868_from_segment_9_10
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_869_from_segment_9_10
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_870_from_segment_9_10
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_871_from_segment_10_10
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_872_from_segment_10_10
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_110_all : ∀ g ∈ goalChunk_110, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_110 at hg
  cases hg with
  | head =>
    exact prove_goal_873_from_segment_10_10
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_874_from_segment_10_10
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_875_from_segment_10_10
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_876_from_segment_10_10
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_877_from_segment_9_11
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_878_from_segment_9_11
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_879_from_segment_9_11
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_880_from_segment_9_11
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_111_all : ∀ g ∈ goalChunk_111, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_111 at hg
  cases hg with
  | head =>
    exact prove_goal_881_from_segment_9_11
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_882_from_segment_9_11
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_883_from_segment_9_11
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_884_from_segment_9_11
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_885_from_segment_10_11
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_886_from_segment_10_11
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_887_from_segment_10_11
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_888_from_segment_10_11
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_112_all : ∀ g ∈ goalChunk_112, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_112 at hg
  cases hg with
  | head =>
    exact prove_goal_889_from_segment_10_11
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_890_from_segment_10_11
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_891_from_segment_9_12
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_892_from_segment_9_12
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_893_from_segment_9_12
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_894_from_segment_9_12
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_895_from_segment_9_12
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_896_from_segment_9_12
                | tail _ hg =>
                  cases hg

theorem gpt_goal_chunk_113_all : ∀ g ∈ goalChunk_113, CoarseLineageHoldsWithInit sm pm g smInitEnv pmInitEnv initGoals := by
  intro g hg
  unfold goalChunk_113 at hg
  cases hg with
  | head =>
    exact prove_goal_897_from_segment_9_12
  | tail _ hg =>
    cases hg with
    | head =>
      exact prove_goal_898_from_segment_9_12
    | tail _ hg =>
      cases hg with
      | head =>
        exact prove_goal_899_from_segment_10_12
      | tail _ hg =>
        cases hg with
        | head =>
          exact prove_goal_900_from_segment_10_12
        | tail _ hg =>
          cases hg with
          | head =>
            exact prove_goal_901_from_segment_10_12
          | tail _ hg =>
            cases hg with
            | head =>
              exact prove_goal_902_from_segment_10_12
            | tail _ hg =>
              cases hg with
              | head =>
                exact prove_goal_903_from_segment_10_12
              | tail _ hg =>
                cases hg with
                | head =>
                  exact prove_goal_904_from_segment_10_12
                | tail _ hg =>
                  cases hg

theorem gpt_main_all_goals : all_goals_stmt := by
  unfold all_goals_stmt goals
  exact (forall_mem_append_goal gpt_goal_chunk_1_all (forall_mem_append_goal gpt_goal_chunk_2_all (forall_mem_append_goal gpt_goal_chunk_3_all (forall_mem_append_goal gpt_goal_chunk_4_all (forall_mem_append_goal gpt_goal_chunk_5_all (forall_mem_append_goal gpt_goal_chunk_6_all (forall_mem_append_goal gpt_goal_chunk_7_all (forall_mem_append_goal gpt_goal_chunk_8_all (forall_mem_append_goal gpt_goal_chunk_9_all (forall_mem_append_goal gpt_goal_chunk_10_all (forall_mem_append_goal gpt_goal_chunk_11_all (forall_mem_append_goal gpt_goal_chunk_12_all (forall_mem_append_goal gpt_goal_chunk_13_all (forall_mem_append_goal gpt_goal_chunk_14_all (forall_mem_append_goal gpt_goal_chunk_15_all (forall_mem_append_goal gpt_goal_chunk_16_all (forall_mem_append_goal gpt_goal_chunk_17_all (forall_mem_append_goal gpt_goal_chunk_18_all (forall_mem_append_goal gpt_goal_chunk_19_all (forall_mem_append_goal gpt_goal_chunk_20_all (forall_mem_append_goal gpt_goal_chunk_21_all (forall_mem_append_goal gpt_goal_chunk_22_all (forall_mem_append_goal gpt_goal_chunk_23_all (forall_mem_append_goal gpt_goal_chunk_24_all (forall_mem_append_goal gpt_goal_chunk_25_all (forall_mem_append_goal gpt_goal_chunk_26_all (forall_mem_append_goal gpt_goal_chunk_27_all (forall_mem_append_goal gpt_goal_chunk_28_all (forall_mem_append_goal gpt_goal_chunk_29_all (forall_mem_append_goal gpt_goal_chunk_30_all (forall_mem_append_goal gpt_goal_chunk_31_all (forall_mem_append_goal gpt_goal_chunk_32_all (forall_mem_append_goal gpt_goal_chunk_33_all (forall_mem_append_goal gpt_goal_chunk_34_all (forall_mem_append_goal gpt_goal_chunk_35_all (forall_mem_append_goal gpt_goal_chunk_36_all (forall_mem_append_goal gpt_goal_chunk_37_all (forall_mem_append_goal gpt_goal_chunk_38_all (forall_mem_append_goal gpt_goal_chunk_39_all (forall_mem_append_goal gpt_goal_chunk_40_all (forall_mem_append_goal gpt_goal_chunk_41_all (forall_mem_append_goal gpt_goal_chunk_42_all (forall_mem_append_goal gpt_goal_chunk_43_all (forall_mem_append_goal gpt_goal_chunk_44_all (forall_mem_append_goal gpt_goal_chunk_45_all (forall_mem_append_goal gpt_goal_chunk_46_all (forall_mem_append_goal gpt_goal_chunk_47_all (forall_mem_append_goal gpt_goal_chunk_48_all (forall_mem_append_goal gpt_goal_chunk_49_all (forall_mem_append_goal gpt_goal_chunk_50_all (forall_mem_append_goal gpt_goal_chunk_51_all (forall_mem_append_goal gpt_goal_chunk_52_all (forall_mem_append_goal gpt_goal_chunk_53_all (forall_mem_append_goal gpt_goal_chunk_54_all (forall_mem_append_goal gpt_goal_chunk_55_all (forall_mem_append_goal gpt_goal_chunk_56_all (forall_mem_append_goal gpt_goal_chunk_57_all (forall_mem_append_goal gpt_goal_chunk_58_all (forall_mem_append_goal gpt_goal_chunk_59_all (forall_mem_append_goal gpt_goal_chunk_60_all (forall_mem_append_goal gpt_goal_chunk_61_all (forall_mem_append_goal gpt_goal_chunk_62_all (forall_mem_append_goal gpt_goal_chunk_63_all (forall_mem_append_goal gpt_goal_chunk_64_all (forall_mem_append_goal gpt_goal_chunk_65_all (forall_mem_append_goal gpt_goal_chunk_66_all (forall_mem_append_goal gpt_goal_chunk_67_all (forall_mem_append_goal gpt_goal_chunk_68_all (forall_mem_append_goal gpt_goal_chunk_69_all (forall_mem_append_goal gpt_goal_chunk_70_all (forall_mem_append_goal gpt_goal_chunk_71_all (forall_mem_append_goal gpt_goal_chunk_72_all (forall_mem_append_goal gpt_goal_chunk_73_all (forall_mem_append_goal gpt_goal_chunk_74_all (forall_mem_append_goal gpt_goal_chunk_75_all (forall_mem_append_goal gpt_goal_chunk_76_all (forall_mem_append_goal gpt_goal_chunk_77_all (forall_mem_append_goal gpt_goal_chunk_78_all (forall_mem_append_goal gpt_goal_chunk_79_all (forall_mem_append_goal gpt_goal_chunk_80_all (forall_mem_append_goal gpt_goal_chunk_81_all (forall_mem_append_goal gpt_goal_chunk_82_all (forall_mem_append_goal gpt_goal_chunk_83_all (forall_mem_append_goal gpt_goal_chunk_84_all (forall_mem_append_goal gpt_goal_chunk_85_all (forall_mem_append_goal gpt_goal_chunk_86_all (forall_mem_append_goal gpt_goal_chunk_87_all (forall_mem_append_goal gpt_goal_chunk_88_all (forall_mem_append_goal gpt_goal_chunk_89_all (forall_mem_append_goal gpt_goal_chunk_90_all (forall_mem_append_goal gpt_goal_chunk_91_all (forall_mem_append_goal gpt_goal_chunk_92_all (forall_mem_append_goal gpt_goal_chunk_93_all (forall_mem_append_goal gpt_goal_chunk_94_all (forall_mem_append_goal gpt_goal_chunk_95_all (forall_mem_append_goal gpt_goal_chunk_96_all (forall_mem_append_goal gpt_goal_chunk_97_all (forall_mem_append_goal gpt_goal_chunk_98_all (forall_mem_append_goal gpt_goal_chunk_99_all (forall_mem_append_goal gpt_goal_chunk_100_all (forall_mem_append_goal gpt_goal_chunk_101_all (forall_mem_append_goal gpt_goal_chunk_102_all (forall_mem_append_goal gpt_goal_chunk_103_all (forall_mem_append_goal gpt_goal_chunk_104_all (forall_mem_append_goal gpt_goal_chunk_105_all (forall_mem_append_goal gpt_goal_chunk_106_all (forall_mem_append_goal gpt_goal_chunk_107_all (forall_mem_append_goal gpt_goal_chunk_108_all (forall_mem_append_goal gpt_goal_chunk_109_all (forall_mem_append_goal gpt_goal_chunk_110_all (forall_mem_append_goal gpt_goal_chunk_111_all (forall_mem_append_goal gpt_goal_chunk_112_all gpt_goal_chunk_113_all))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

end TrainVerify.Denote.GeneratedMain

