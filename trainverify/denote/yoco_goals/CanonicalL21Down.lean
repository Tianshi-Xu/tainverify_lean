/- Canonical Goal 1, layer 21: faithful SwiGLU/down-projection branch. -/
import denote.yoco_goals.CanonicalL21ResidualGate

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

noncomputable section

private def cL21dSmRef : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [6162], outs := [8909, 8913, 8917, 8921, 8925], params := [5] }

private def cL21dPmRef0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_multiref", ins := [11358], outs := [15428, 15092, 15102, 15116, 15128], params := [5] }

private def cL21dPmRef1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_multiref", ins := [11359], outs := [15430, 15093, 15103, 15117, 15129], params := [5] }

private def cL21dSmReshapeA : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8921], outs := [6177], params := [4096, 1024] }

private def cL21dSmReshapeB : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8925], outs := [6181], params := [4096, 1024] }

private def cL21dPmReshapeA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [15116], outs := [11390], params := [2048, 1024] }

private def cL21dPmReshapeA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [15117], outs := [11391], params := [2048, 1024] }

private def cL21dPmReshapeB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [15128], outs := [11402], params := [2048, 1024] }

private def cL21dPmReshapeB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [15129], outs := [11403], params := [2048, 1024] }

private def cL21dSmLinearA : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [6177, 6178], outs := [6179] }

private def cL21dSmLinearB : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [6181, 6182], outs := [6183] }

private def cL21dPmLinearA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11390, 6178], outs := [11394] }

private def cL21dPmLinearA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11391, 6178], outs := [11395] }

private def cL21dPmLinearB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11402, 6182], outs := [11406] }

private def cL21dPmLinearB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11403, 6182], outs := [11407] }

private def cL21dSmViewA : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [6179], outs := [6180], params := [4096, 512] }

private def cL21dSmViewB : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [6183], outs := [6184], params := [4096, 512] }

private def cL21dPmViewA0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11394], outs := [11396], params := [2048, 512] }

private def cL21dPmViewA1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11395], outs := [11397], params := [2048, 512] }

private def cL21dPmViewB0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11406], outs := [11408], params := [2048, 512] }

private def cL21dPmViewB1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11407], outs := [11409], params := [2048, 512] }

private def cL21dSmSwi : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [6180, 6184], outs := [6185] }

private def cL21dPmSwi0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_swiglu", ins := [11396, 11408], outs := [11414] }

private def cL21dPmSwi1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_swiglu", ins := [11397, 11409], outs := [11415] }

private def cL21dSmReshapeDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [6185], outs := [6186], params := [4096, 512] }

private def cL21dPmReshapeDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [11414], outs := [11416], params := [2048, 512] }

private def cL21dPmReshapeDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [11415], outs := [11417], params := [2048, 512] }

private def cL21dSmLinearDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [6186, 6187], outs := [6188] }

private def cL21dPmLinearDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11416, 6187], outs := [11422] }

private def cL21dPmLinearDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11417, 6187], outs := [11423] }

private def cL21dSmViewDown : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [6188], outs := [6189], params := [4096, 1024] }

private def cL21dPmViewDown0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_view", ins := [11422], outs := [11424], params := [2048, 1024] }

private def cL21dPmViewDown1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_view", ins := [11423], outs := [11425], params := [2048, 1024] }

private theorem cL21d_red_sm8921 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8921 =
      denoteGraphDistributedFaithful sm_goal_1 init 6162 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 864 cL21dSmRef
    6162 8921 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21dSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6162 [8948, 8952, 8956, 8921, 8925] 5 rfl 8921 (by decide)

private theorem cL21d_red_sm8925 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 8925 =
      denoteGraphDistributedFaithful sm_goal_1 init 6162 := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 864 cL21dSmRef
    6162 8925 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21dSmRef
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at sm_goal_1 s 0 6162 [8948, 8952, 8956, 8921, 8925] 5 rfl 8925 (by decide)

private theorem cL21d_red_pm15116 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 15116 =
      denoteGraphDistributedFaithful pm_goal_1 init 11358 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1891 cL21dPmRef0
    11358 15116 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21dPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 11358 [15428, 15092, 15102, 15116, 15128] 5 rfl 15116 (by decide)

private theorem cL21d_red_pm15128 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 15128 =
      denoteGraphDistributedFaithful pm_goal_1 init 11358 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1891 cL21dPmRef0
    11358 15128 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21dPmRef0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 0 11358 [15428, 15092, 15102, 15116, 15128] 5 rfl 15128 (by decide)

private theorem cL21d_red_pm15117 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 15117 =
      denoteGraphDistributedFaithful pm_goal_1 init 11359 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1892 cL21dPmRef1
    11359 15117 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21dPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 11359 [15430, 15093, 15103, 15117, 15129] 5 rfl 15117 (by decide)

private theorem cL21d_red_pm15129 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 15129 =
      denoteGraphDistributedFaithful pm_goal_1 init 11359 := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1892 cL21dPmRef1
    11359 15129 (fun x => x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21dPmRef1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_multiref_at pm_goal_1 s 1 11359 [15430, 15093, 15103, 15117, 15129] 5 rfl 15129 (by decide)

private theorem cL21d_red_sm6177 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6177 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8921) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 867 cL21dSmReshapeA
    8921 6177 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21dSmReshapeA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8921 6177 [4096, 1024]

private theorem cL21d_red_sm6181 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6181 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 8925) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 868 cL21dSmReshapeB
    8925 6181 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21dSmReshapeB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 8925 6181 [4096, 1024]

private theorem cL21d_red_pm11390 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11390 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 15116) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1894 cL21dPmReshapeA0
    15116 11390 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21dPmReshapeA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 15116 11390 [2048, 1024]

private theorem cL21d_red_pm11391 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11391 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 15117) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1898 cL21dPmReshapeA1
    15117 11391 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21dPmReshapeA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 15117 11391 [2048, 1024]

private theorem cL21d_red_pm11402 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11402 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 15128) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1895 cL21dPmReshapeB0
    15128 11402 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21dPmReshapeB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 15128 11402 [2048, 1024]

private theorem cL21d_red_pm11403 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11403 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 15129) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1899 cL21dPmReshapeB1
    15129 11403 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21dPmReshapeB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 15129 11403 [2048, 1024]

private theorem cL21d_red_sm6180 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6180 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 6179) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 875 cL21dSmViewA
    6179 6180 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21dSmViewA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 6179 6180

private theorem cL21d_red_sm6184 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6184 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 6183) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 876 cL21dSmViewB
    6183 6184 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21dSmViewB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [512] 6183 6184

private theorem cL21d_red_pm11396 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11396 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 11394) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1909 cL21dPmViewA0
    11394 11396 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21dPmViewA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 11394 11396

private theorem cL21d_red_pm11397 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11397 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 11395) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1914 cL21dPmViewA1
    11395 11397 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21dPmViewA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 11395 11397

private theorem cL21d_red_pm11408 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11408 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 11406) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1910 cL21dPmViewB0
    11406 11408 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21dPmViewB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [512] 11406 11408

private theorem cL21d_red_pm11409 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11409 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 11407) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1915 cL21dPmViewB1
    11407 11409 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21dPmViewB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [512] 11407 11409

private theorem cL21d_red_sm6186 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6186 =
      fw_view [4096, 512] (denoteGraphDistributedFaithful sm_goal_1 init 6185) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 880 cL21dSmReshapeDown
    6185 6186 (fun x => fw_view [4096, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21dSmReshapeDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm_goal_1 s 0 6185 6186 [4096, 512]

private theorem cL21d_red_pm11416 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11416 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 11414) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1922 cL21dPmReshapeDown0
    11414 11416 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21dPmReshapeDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 0 11414 11416 [2048, 512]

private theorem cL21d_red_pm11417 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11417 =
      fw_view [2048, 512] (denoteGraphDistributedFaithful pm_goal_1 init 11415) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1925 cL21dPmReshapeDown1
    11415 11417 (fun x => fw_view [2048, 512] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21dPmReshapeDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm_goal_1 s 1 11415 11417 [2048, 512]

private theorem cL21d_red_sm6189 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6189 =
      fw_view [4096, 1024] (denoteGraphDistributedFaithful sm_goal_1 init 6188) := by
  refine denoteGraphDistributedFaithful_reduce1 sm_goal_1 init 882 cL21dSmViewDown
    6188 6189 (fun x => fw_view [4096, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21dSmViewDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out sm_goal_1 s 0 4096 [1024] 6188 6189

private theorem cL21d_red_pm11424 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11424 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 11422) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1930 cL21dPmViewDown0
    11422 11424 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21dPmViewDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 0 2048 [1024] 11422 11424

private theorem cL21d_red_pm11425 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11425 =
      fw_view [2048, 1024] (denoteGraphDistributedFaithful pm_goal_1 init 11423) := by
  refine denoteGraphDistributedFaithful_reduce1 pm_goal_1 init 1931 cL21dPmViewDown1
    11423 11425 (fun x => fw_view [2048, 1024] x)
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)
  intro s
  unfold cL21dPmViewDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_view_out pm_goal_1 s 1 2048 [1024] 11423 11425

private theorem cL21d_red_sm6179 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6179 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 6177)
        (denoteGraphDistributedFaithful sm_goal_1 init 6178) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 871 cL21dSmLinearA
    6177 6178 6179 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21dSmLinearA
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 6177 6178 6179

private theorem cL21d_red_sm6183 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6183 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 6181)
        (denoteGraphDistributedFaithful sm_goal_1 init 6182) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 872 cL21dSmLinearB
    6181 6182 6183 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21dSmLinearB
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 6181 6182 6183

private theorem cL21d_red_pm11394 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11394 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 11390)
        (denoteGraphDistributedFaithful pm_goal_1 init 6178) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1901 cL21dPmLinearA0
    11390 6178 11394 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21dPmLinearA0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 11390 6178 11394

private theorem cL21d_red_pm11395 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11395 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 11391)
        (denoteGraphDistributedFaithful pm_goal_1 init 6178) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1906 cL21dPmLinearA1
    11391 6178 11395 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21dPmLinearA1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 11391 6178 11395

private theorem cL21d_red_pm11406 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11406 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 11402)
        (denoteGraphDistributedFaithful pm_goal_1 init 6182) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1902 cL21dPmLinearB0
    11402 6182 11406 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21dPmLinearB0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 11402 6182 11406

private theorem cL21d_red_pm11407 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11407 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 11403)
        (denoteGraphDistributedFaithful pm_goal_1 init 6182) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1907 cL21dPmLinearB1
    11403 6182 11407 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21dPmLinearB1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 11403 6182 11407

private theorem cL21d_red_sm6185 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6185 =
      fw_swiglu (denoteGraphDistributedFaithful sm_goal_1 init 6180)
        (denoteGraphDistributedFaithful sm_goal_1 init 6184) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 879 cL21dSmSwi
    6180 6184 6185 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21dSmSwi
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p sm_goal_1 s 0 6180 6184 6185

private theorem cL21d_red_pm11414 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11414 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 11396)
        (denoteGraphDistributedFaithful pm_goal_1 init 11408) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1917 cL21dPmSwi0
    11396 11408 11414 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21dPmSwi0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 0 11396 11408 11414

private theorem cL21d_red_pm11415 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11415 =
      fw_swiglu (denoteGraphDistributedFaithful pm_goal_1 init 11397)
        (denoteGraphDistributedFaithful pm_goal_1 init 11409) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1921 cL21dPmSwi1
    11397 11409 11415 fw_swiglu
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21dPmSwi1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_swiglu_out_1p pm_goal_1 s 1 11397 11409 11415

private theorem cL21d_red_sm6188 (init : Store) :
    denoteGraphDistributedFaithful sm_goal_1 init 6188 =
      fw_linear (denoteGraphDistributedFaithful sm_goal_1 init 6186)
        (denoteGraphDistributedFaithful sm_goal_1 init 6187) := by
  refine denoteGraphDistributedFaithful_reduce2 sm_goal_1 init 881 cL21dSmLinearDown
    6186 6187 6188 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21dSmLinearDown
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm_goal_1 s 0 6186 6187 6188

private theorem cL21d_red_pm11422 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11422 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 11416)
        (denoteGraphDistributedFaithful pm_goal_1 init 6187) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1926 cL21dPmLinearDown0
    11416 6187 11422 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21dPmLinearDown0
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 0 11416 6187 11422

private theorem cL21d_red_pm11423 (init : Store) :
    denoteGraphDistributedFaithful pm_goal_1 init 11423 =
      fw_linear (denoteGraphDistributedFaithful pm_goal_1 init 11417)
        (denoteGraphDistributedFaithful pm_goal_1 init 6187) := by
  refine denoteGraphDistributedFaithful_reduce2 pm_goal_1 init 1929 cL21dPmLinearDown1
    11417 6187 11423 fw_linear
    (by native_decide) (by native_decide) ?_
    (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide)
  intro s
  unfold cL21dPmLinearDown1
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm_goal_1 s 1 11417 6187 11423

private theorem cL21d_leaf (g : GraphDecl) (init : Store) (tid : Tid)
    (hn : ∀ n ∈ g.nodes, n.outs ≠ []) (hw : ∀ n ∈ g.nodes, tid ∉ n.outs) :
    denoteGraphDistributedFaithful g init tid = init tid := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written g g.nodes init tid hn hw

private theorem cL21d_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (gW : LineageGoal) (hgW : gW ∈ initGoals) (W : Tid)
    (htp : gW.tps = [{rank := 0, tid := W}])
    (hts : gW.ts = W) (hgd : gW.gatherDim = 0) (hrep : gW.replicated = false)
    (hsm : ∀ n ∈ sm_goal_1.nodes, W ∉ n.outs)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    denoteGraphDistributedFaithful sm_goal_1 initSM W =
      denoteGraphDistributedFaithful pm_goal_1 initPM W := by
  have hi := (hInit gW hgW).2.2
  rw [reconstructForGoal_of_not_replicated gW pm_goal_1.numRanks _ hrep,
    htp, hts, hgd] at hi
  simp only [List.map, reconstructWithDim] at hi
  rw [cL21d_leaf sm_goal_1 initSM W (by native_decide) hsm,
    cL21d_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hi

private theorem cL21d_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv) (W : Tid) (shape : Shape)
    (henv : pm_goal_1InitEnv W = some shape)
    (hpm : ∀ n ∈ pm_goal_1.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm_goal_1 initPM W).shape = shape := by
  rw [cL21d_leaf pm_goal_1 initPM W (by native_decide) hpm]
  exact hPM W shape henv

/-- The real canonical Goal-1 L21 SwiGLU and down-projection nodes preserve the
CP2 zigzag layout.  The only lineage premise is the shared normalized layer
input; both up projections, SwiGLU, and the down projection are derived from
faithful graph execution and externally initialized replicated weights. -/
theorem canonical_l21_down_from_norm_input (initSM initPM : Store)
    (hPM : StoreShapesHold initPM pm_goal_1InitEnv)
    (hInit : InitGoalsHold pm_goal_1.numRanks initGoals initSM initPM)
    (hNorm : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6162)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11358)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11359)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024]) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6189)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11424)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11425)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
  have hARef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8921)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15116)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15117)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL21d_red_sm8921 initSM, cL21d_red_pm15116 initPM, cL21d_red_pm15117 initPM]
    exact hNorm
  have hBRef : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 8925)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15128)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 15129)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL21d_red_sm8925 initSM, cL21d_red_pm15128 initPM, cL21d_red_pm15129 initPM]
    exact hNorm
  have hAR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6177)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11390)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11391)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL21d_red_sm6177 initSM, cL21d_red_pm11390 initPM, cL21d_red_pm11391 initPM]
    exact Zigzag2Rel.view_id' hARef
  have hBR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6181)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11402)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11403)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL21d_red_sm6181 initSM, cL21d_red_pm11402 initPM, cL21d_red_pm11403 initPM]
    exact Zigzag2Rel.view_id' hBRef
  have hwA := cL21d_weight_eq initSM initPM hInit initGoal_6178 (by native_decide)
    6178 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hwB := cL21d_weight_eq initSM initPM hInit initGoal_6182 (by native_decide)
    6182 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsA := cL21d_weight_shape initPM hPM 6178 [512, 1024]
    (by native_decide) (by native_decide)
  have hsB := cL21d_weight_shape initPM hPM 6182 [512, 1024]
    (by native_decide) (by native_decide)
  have hALinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6179)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11394)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11395)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [cL21d_red_sm6179 initSM, cL21d_red_pm11394 initPM,
      cL21d_red_pm11395 initPM, hwA]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hAR hsA
      (by decide) (by decide) (by decide)
  have hBLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6183)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11406)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11407)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [cL21d_red_sm6183 initSM, cL21d_red_pm11406 initPM,
      cL21d_red_pm11407 initPM, hwB]
    exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hBR hsB
      (by decide) (by decide) (by decide)
  have hAView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6180)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11396)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11397)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [cL21d_red_sm6180 initSM, cL21d_red_pm11396 initPM, cL21d_red_pm11397 initPM]
    exact Zigzag2Rel.view_id' hALinear
  have hBView : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6184)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11408)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11409)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [cL21d_red_sm6184 initSM, cL21d_red_pm11408 initPM, cL21d_red_pm11409 initPM]
    exact Zigzag2Rel.view_id' hBLinear
  obtain ⟨a0, a1, has⟩ := hAView
  obtain ⟨b0, b1, hbs⟩ := hBView
  have hAView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6180)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11396)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11397)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨a0, a1, has⟩
  have hBView' : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6184)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11408)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11409)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [2048 * 2, 512] [2048, 512] := ⟨b0, b1, hbs⟩
  have hSwi : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6185)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11414)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11415)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [cL21d_red_sm6185 initSM, cL21d_red_pm11414 initPM, cL21d_red_pm11415 initPM]
    exact Zigzag2Rel.swiglu 2048 512 hAView' hBView' (by decide) (by decide)
  have hSwiR : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6186)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11416)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11417)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 512] [2048, 512] := by
    rw [cL21d_red_sm6186 initSM, cL21d_red_pm11416 initPM, cL21d_red_pm11417 initPM]
    exact Zigzag2Rel.view_id' hSwi
  have hwD := cL21d_weight_eq initSM initPM hInit initGoal_6187 (by native_decide)
    6187 rfl rfl rfl rfl (by native_decide) (by native_decide)
  have hsD := cL21d_weight_shape initPM hPM 6187 [1024, 512]
    (by native_decide) (by native_decide)
  have hDownLinear : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_1 initSM 6188)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11422)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 11423)
      (denoteGraphDistributedFaithful pm_goal_1 initPM 6252)
      [4096, 1024] [2048, 1024] := by
    rw [cL21d_red_sm6188 initSM, cL21d_red_pm11422 initPM,
      cL21d_red_pm11423 initPM, hwD]
    exact Zigzag2Rel.mix_precision_linear 2048 512 1024 hSwiR hsD
      (by decide) (by decide) (by decide)
  rw [cL21d_red_sm6189 initSM, cL21d_red_pm11424 initPM, cL21d_red_pm11425 initPM]
  exact Zigzag2Rel.view_id' hDownLinear

end
end TrainVerify.Denote.GeneratedPatterns
