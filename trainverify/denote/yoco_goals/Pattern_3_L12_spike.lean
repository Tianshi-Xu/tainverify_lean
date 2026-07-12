/-
  Pattern_3_L12_spike.lean — rapid iteration on L12 zigzag-band proof.

  This scratch module imports Pattern_3 so we get cached oleans from L0..L11.
  Once L12 is proven here, we'll paste the verified block back into Pattern_3.lean.
-/
import denote.yoco_goals.Pattern_3

set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

namespace TrainVerify.Denote.GeneratedPatterns

-- L11 MoE-branch denote-unfold helpers (generated from L10 analogs).
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_9527 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9527 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 9525) 8
        (((denoteGraph_ringAttn pm_goal_3 initPM 9525).shape.reverse.head?).getD 1)).fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9527 9525 968
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [9525], outs := [9527, 9529, 9531], params := [8] })
    (fun a1 => (fw_topk_routing (a1) 8
        (((a1).shape.reverse.head?).getD 1)).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out pm_goal_3 s 0 9525 9527 9529 9531 [8])
    rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_9528 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9528 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 9526) 8
        (((denoteGraph_ringAttn pm_goal_3 initPM 9526).shape.reverse.head?).getD 1)).fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9528 9526 972
    ({ rank := 1, op := "OpName.FW_topk_routing", ins := [9526], outs := [9528, 9530, 9532], params := [8] })
    (fun a1 => (fw_topk_routing (a1) 8
        (((a1).shape.reverse.head?).getD 1)).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out pm_goal_3 s 1 9526 9528 9530 9532 [8])
    rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_9537 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9537 =
      fw_all2all_moe_gmm_full
        (denoteGraph_ringAttn pm_goal_3 initPM 15702)
        (denoteGraph_ringAttn pm_goal_3 initPM 9527)
        (denoteGraph_ringAttn pm_goal_3 initPM 9529)
        [initPM 9533, initPM 9534] [initPM 9535, initPM 9536]
        64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep7 pm_goal_3 initPM 9537 15702 9527 9529 9533 9534 9535 9536 976
    ({ rank := 0, op := "OpName.FW_all2all_moe_gmm_full", ins := [15702, 9527, 9529, 9533, 9534, 9535, 9536], outs := [9537], params := [64, 8, 10] })
    (fun a1 a2 a3 a4 a5 a6 a7 => fw_all2all_moe_gmm_full
        (a1)
        (a2)
        (a3)
        [a4, a5] [a6, a7]
        64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_3 s 0 15702 9527 9529 9533 9534 9535 9536 9537 [64, 8, 10])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 9533 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 9534 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 9535 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 9536 (by decide) (by decide))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_9538 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9538 =
      fw_all2all_moe_gmm_full
        (denoteGraph_ringAttn pm_goal_3 initPM 15725)
        (denoteGraph_ringAttn pm_goal_3 initPM 9528)
        (denoteGraph_ringAttn pm_goal_3 initPM 9530)
        [initPM 9533, initPM 9534] [initPM 9535, initPM 9536]
        64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep7 pm_goal_3 initPM 9538 15725 9528 9530 9533 9534 9535 9536 979
    ({ rank := 1, op := "OpName.FW_all2all_moe_gmm_full", ins := [15725, 9528, 9530, 9533, 9534, 9535, 9536], outs := [9538], params := [64, 8, 10] })
    (fun a1 a2 a3 a4 a5 a6 a7 => fw_all2all_moe_gmm_full
        (a1)
        (a2)
        (a3)
        [a4, a5] [a6, a7]
        64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_3 s 1 15725 9528 9530 9533 9534 9535 9536 9538 [64, 8, 10])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 9533 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 9534 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 9535 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 9536 (by decide) (by decide))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_15702 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 15702 =
      denoteGraph_ringAttn pm_goal_3 initPM 9517 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15702 9517 950
    ({ rank := 0, op := "OpName.FW_multiref", ins := [9517], outs := [15698, 15702, 15706, 15710, 15714], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out pm_goal_3 s 0 9517 15698 15702 15706 15710 15714 (by decide))
    rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_15725 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 15725 =
      denoteGraph_ringAttn pm_goal_3 initPM 9518 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15725 9518 951
    ({ rank := 1, op := "OpName.FW_multiref", ins := [9518], outs := [15721, 15725, 15729, 15733, 15737], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out pm_goal_3 s 1 9518 15721 15725 15729 15733 15737 (by decide))
    rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_9611 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9611 =
      (elemwiseMul (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 15706)) (initPM 5310)))) (fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 15710)) (initPM 5315))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 15714)) (initPM 5319))))) (initPM 5324)))) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9611 9551 9607 988
    ({ rank := 0, op := "OpName.FW_mul", ins := [9551, 9607], outs := [9611] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out pm_goal_3 s 0 9551 9607 9611])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9551 9549 977
      ({ rank := 0, op := "OpName.FW_sigmoid", ins := [9549], outs := [9551] })
      (fun a1 => fw_sigmoid a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => by rw [applyNode_fw_sigmoid_out_1p pm_goal_3 s 0 9549 9551])
      (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9549 9543 969
        ({ rank := 0, op := "OpName.FW_view", ins := [9543], outs := [9549], params := [2048, 1] })
        (fun a1 => fw_view [2048, 1] a1)
        (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (fun s => by rw [applyNode_fw_view_out pm_goal_3 s 0 2048 [1] 9543 9549])
        (DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9543 9539 5310 961
          ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9539, 5310], outs := [9543] })
          (fun a1 a2 => fw_linear a1 a2)
          (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (fun s => by rw [applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 9539 5310 9543])
          (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9539 15706 953
            ({ rank := 0, op := "OpName.FW_reshape", ins := [15706], outs := [9539], params := [2048, 1024] })
            (fun a1 => fw_view [2048, 1024] a1)
            (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (fun s => by rw [applyNode_fw_reshape_out pm_goal_3 s 0 15706 9539 [2048, 1024]])
            (rfl))
          (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5310 (by decide) (by decide)))))
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9607 9597 986
      ({ rank := 0, op := "OpName.FW_view", ins := [9597], outs := [9607], params := [2048, 1024] })
      (fun a1 => fw_view [2048, 1024] a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => by rw [applyNode_fw_view_out pm_goal_3 s 0 2048 [1024] 9597 9607])
      (DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9597 9591 5324 984
        ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9591, 5324], outs := [9597] })
        (fun a1 a2 => fw_linear a1 a2)
        (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (fun s => by rw [applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 9591 5324 9597])
        (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9591 9589 982
          ({ rank := 0, op := "OpName.FW_reshape", ins := [9589], outs := [9591], params := [2048, 512] })
          (fun a1 => fw_view [2048, 512] a1)
          (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (fun s => by rw [applyNode_fw_reshape_out pm_goal_3 s 0 9589 9591 [2048, 512]])
          (DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9589 9567 9585 978
            ({ rank := 0, op := "OpName.FW_swiglu", ins := [9567, 9585], outs := [9589] })
            (fun a1 a2 => fw_swiglu a1 a2)
            (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (fun s => by rw [applyNode_fw_swiglu_out_1p pm_goal_3 s 0 9567 9585 9589])
            (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9567 9557 970
              ({ rank := 0, op := "OpName.FW_view", ins := [9557], outs := [9567], params := [2048, 512] })
              (fun a1 => fw_view [2048, 512] a1)
              (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (fun s => by rw [applyNode_fw_view_out pm_goal_3 s 0 2048 [512] 9557 9567])
              (DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9557 9553 5315 962
                ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9553, 5315], outs := [9557] })
                (fun a1 a2 => fw_linear a1 a2)
                (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (fun s => by rw [applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 9553 5315 9557])
                (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9553 15710 954
                  ({ rank := 0, op := "OpName.FW_reshape", ins := [15710], outs := [9553], params := [2048, 1024] })
                  (fun a1 => fw_view [2048, 1024] a1)
                  (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                  (fun s => by rw [applyNode_fw_reshape_out pm_goal_3 s 0 15710 9553 [2048, 1024]])
                  (rfl))
                (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5315 (by decide) (by decide))))
            (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9585 9575 971
              ({ rank := 0, op := "OpName.FW_view", ins := [9575], outs := [9585], params := [2048, 512] })
              (fun a1 => fw_view [2048, 512] a1)
              (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (fun s => by rw [applyNode_fw_view_out pm_goal_3 s 0 2048 [512] 9575 9585])
              (DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9575 9571 5319 963
                ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9571, 5319], outs := [9575] })
                (fun a1 a2 => fw_linear a1 a2)
                (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (fun s => by rw [applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 9571 5319 9575])
                (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9571 15714 955
                  ({ rank := 0, op := "OpName.FW_reshape", ins := [15714], outs := [9571], params := [2048, 1024] })
                  (fun a1 => fw_view [2048, 1024] a1)
                  (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                  (fun s => by rw [applyNode_fw_reshape_out pm_goal_3 s 0 15714 9571 [2048, 1024]])
                  (rfl))
                (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5319 (by decide) (by decide))))))
        (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5324 (by decide) (by decide))))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_9612 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9612 =
      (elemwiseMul (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 15729)) (initPM 5310)))) (fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 15733)) (initPM 5315))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 15737)) (initPM 5319))))) (initPM 5324)))) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9612 9552 9608 989
    ({ rank := 1, op := "OpName.FW_mul", ins := [9552, 9608], outs := [9612] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out pm_goal_3 s 1 9552 9608 9612])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9552 9550 980
      ({ rank := 1, op := "OpName.FW_sigmoid", ins := [9550], outs := [9552] })
      (fun a1 => fw_sigmoid a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => by rw [applyNode_fw_sigmoid_out_1p pm_goal_3 s 1 9550 9552])
      (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9550 9544 973
        ({ rank := 1, op := "OpName.FW_view", ins := [9544], outs := [9550], params := [2048, 1] })
        (fun a1 => fw_view [2048, 1] a1)
        (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (fun s => by rw [applyNode_fw_view_out pm_goal_3 s 1 2048 [1] 9544 9550])
        (DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9544 9540 5310 965
          ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9540, 5310], outs := [9544] })
          (fun a1 a2 => fw_linear a1 a2)
          (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (fun s => by rw [applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 9540 5310 9544])
          (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9540 15729 957
            ({ rank := 1, op := "OpName.FW_reshape", ins := [15729], outs := [9540], params := [2048, 1024] })
            (fun a1 => fw_view [2048, 1024] a1)
            (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (fun s => by rw [applyNode_fw_reshape_out pm_goal_3 s 1 15729 9540 [2048, 1024]])
            (rfl))
          (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5310 (by decide) (by decide)))))
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9608 9598 987
      ({ rank := 1, op := "OpName.FW_view", ins := [9598], outs := [9608], params := [2048, 1024] })
      (fun a1 => fw_view [2048, 1024] a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => by rw [applyNode_fw_view_out pm_goal_3 s 1 2048 [1024] 9598 9608])
      (DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9598 9592 5324 985
        ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9592, 5324], outs := [9598] })
        (fun a1 a2 => fw_linear a1 a2)
        (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (fun s => by rw [applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 9592 5324 9598])
        (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9592 9590 983
          ({ rank := 1, op := "OpName.FW_reshape", ins := [9590], outs := [9592], params := [2048, 512] })
          (fun a1 => fw_view [2048, 512] a1)
          (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (fun s => by rw [applyNode_fw_reshape_out pm_goal_3 s 1 9590 9592 [2048, 512]])
          (DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9590 9568 9586 981
            ({ rank := 1, op := "OpName.FW_swiglu", ins := [9568, 9586], outs := [9590] })
            (fun a1 a2 => fw_swiglu a1 a2)
            (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (fun s => by rw [applyNode_fw_swiglu_out_1p pm_goal_3 s 1 9568 9586 9590])
            (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9568 9558 974
              ({ rank := 1, op := "OpName.FW_view", ins := [9558], outs := [9568], params := [2048, 512] })
              (fun a1 => fw_view [2048, 512] a1)
              (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (fun s => by rw [applyNode_fw_view_out pm_goal_3 s 1 2048 [512] 9558 9568])
              (DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9558 9554 5315 966
                ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9554, 5315], outs := [9558] })
                (fun a1 a2 => fw_linear a1 a2)
                (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (fun s => by rw [applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 9554 5315 9558])
                (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9554 15733 958
                  ({ rank := 1, op := "OpName.FW_reshape", ins := [15733], outs := [9554], params := [2048, 1024] })
                  (fun a1 => fw_view [2048, 1024] a1)
                  (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                  (fun s => by rw [applyNode_fw_reshape_out pm_goal_3 s 1 15733 9554 [2048, 1024]])
                  (rfl))
                (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5315 (by decide) (by decide))))
            (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9586 9576 975
              ({ rank := 1, op := "OpName.FW_view", ins := [9576], outs := [9586], params := [2048, 512] })
              (fun a1 => fw_view [2048, 512] a1)
              (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (fun s => by rw [applyNode_fw_view_out pm_goal_3 s 1 2048 [512] 9576 9586])
              (DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9576 9572 5319 967
                ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9572, 5319], outs := [9576] })
                (fun a1 a2 => fw_linear a1 a2)
                (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (fun s => by rw [applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 9572 5319 9576])
                (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9572 15737 959
                  ({ rank := 1, op := "OpName.FW_reshape", ins := [15737], outs := [9572], params := [2048, 1024] })
                  (fun a1 => fw_view [2048, 1024] a1)
                  (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                  (fun s => by rw [applyNode_fw_reshape_out pm_goal_3 s 1 15737 9572 [2048, 1024]])
                  (rfl))
                (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5319 (by decide) (by decide))))))
        (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5324 (by decide) (by decide))))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_15706 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 15706 =
      denoteGraph_ringAttn pm_goal_3 initPM 9517 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15706 9517 950
    ({ rank := 0, op := "OpName.FW_multiref", ins := [9517], outs := [15698, 15702, 15706, 15710, 15714], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out pm_goal_3 s 0 9517 15698 15702 15706 15710 15714 (by decide) (by decide))
    rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_15710 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 15710 =
      denoteGraph_ringAttn pm_goal_3 initPM 9517 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15710 9517 950
    ({ rank := 0, op := "OpName.FW_multiref", ins := [9517], outs := [15698, 15702, 15706, 15710, 15714], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out pm_goal_3 s 0 9517 15698 15702 15706 15710 15714 (by decide) (by decide) (by decide))
    rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_15714 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 15714 =
      denoteGraph_ringAttn pm_goal_3 initPM 9517 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15714 9517 950
    ({ rank := 0, op := "OpName.FW_multiref", ins := [9517], outs := [15698, 15702, 15706, 15710, 15714], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out pm_goal_3 s 0 9517 15698 15702 15706 15710 15714 (by decide) (by decide) (by decide) (by decide))
    rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_15729 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 15729 =
      denoteGraph_ringAttn pm_goal_3 initPM 9518 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15729 9518 951
    ({ rank := 1, op := "OpName.FW_multiref", ins := [9518], outs := [15721, 15725, 15729, 15733, 15737], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out pm_goal_3 s 1 9518 15721 15725 15729 15733 15737 (by decide) (by decide))
    rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_15733 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 15733 =
      denoteGraph_ringAttn pm_goal_3 initPM 9518 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15733 9518 951
    ({ rank := 1, op := "OpName.FW_multiref", ins := [9518], outs := [15721, 15725, 15729, 15733, 15737], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out pm_goal_3 s 1 9518 15721 15725 15729 15733 15737 (by decide) (by decide) (by decide))
    rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_15737 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 15737 =
      denoteGraph_ringAttn pm_goal_3 initPM 9518 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15737 9518 951
    ({ rank := 1, op := "OpName.FW_multiref", ins := [9518], outs := [15721, 15725, 15729, 15733, 15737], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out pm_goal_3 s 1 9518 15721 15725 15729 15733 15737 (by decide) (by decide) (by decide) (by decide))
    rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_9615 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9615 = elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 9537) (denoteGraph_ringAttn pm_goal_3 initPM 9611) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9615 9537 9611 990
    ({ rank := 0, op := "OpName.FW_add", ins := [9537, 9611], outs := [9615] })
    (fun a1 a2 => elemwiseAdd (a1) (a2))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 9537 9611 9615)
    rfl rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_9616 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9616 = elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 9538) (denoteGraph_ringAttn pm_goal_3 initPM 9612) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9616 9538 9612 991
    ({ rank := 1, op := "OpName.FW_add", ins := [9538, 9612], outs := [9616] })
    (fun a1 a2 => elemwiseAdd (a1) (a2))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 9538 9612 9616)
    rfl rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_9621 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9621 = denoteGraph_ringAttn pm_goal_3 initPM 9615 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9621 9615 992
    ({ rank := 0, op := "OpName.FW_float", ins := [9615], outs := [9621] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 9615 9621 [])
    rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_9622 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9622 = denoteGraph_ringAttn pm_goal_3 initPM 9616 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9622 9616 993
    ({ rank := 1, op := "OpName.FW_float", ins := [9616], outs := [9622] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 9616 9622 [])
    rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_9625 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9625 = elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 15683) (denoteGraph_ringAttn pm_goal_3 initPM 9621) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9625 15683 9621 994
    ({ rank := 0, op := "OpName.FW_add", ins := [15683, 9621], outs := [9625] })
    (fun a1 a2 => elemwiseAdd (a1) (a2))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 15683 9621 9625)
    rfl rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_9626 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9626 = elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 15691) (denoteGraph_ringAttn pm_goal_3 initPM 9622) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9626 15691 9622 995
    ({ rank := 1, op := "OpName.FW_add", ins := [15691, 9622], outs := [9626] })
    (fun a1 a2 => elemwiseAdd (a1) (a2))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 15691 9622 9626)
    rfl rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_15683 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 15683 = denoteGraph_ringAttn pm_goal_3 initPM 9513 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15683 9513 946
    ({ rank := 0, op := "OpName.FW_multiref", ins := [9513], outs := [15679, 15683], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out pm_goal_3 s 0 9513 15679 15683 (by decide))
    rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_15691 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 15691 = denoteGraph_ringAttn pm_goal_3 initPM 9514 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15691 9514 947
    ({ rank := 1, op := "OpName.FW_multiref", ins := [9514], outs := [15687, 15691], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out pm_goal_3 s 1 9514 15687 15691 (by decide))
    rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_sm_goal_3_5303 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5303 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3 initSM 5302) 8
        (((denoteGraph_ringAttn sm_goal_3 initSM 5302).shape.reverse.head?).getD 1)).fst :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5303 5302 455
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [5302], outs := [5303, 5304, 5305], params := [8] })
    (fun a1 => (fw_topk_routing (a1) 8
        (((a1).shape.reverse.head?).getD 1)).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out sm_goal_3 s 0 5302 5303 5304 5305 [8])
    rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_sm_goal_3_5308 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5308 =
      fw_all2all_moe_gmm
        (denoteGraph_ringAttn sm_goal_3 initSM 7991)
        (denoteGraph_ringAttn sm_goal_3 initSM 5303)
        (denoteGraph_ringAttn sm_goal_3 initSM 5304)
        (initSM 5306) (initSM 5307) 64 0 64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep5 sm_goal_3 initSM 5308 7991 5303 5304 5306 5307 459
    ({ rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7991, 5303, 5304, 5306, 5307], outs := [5308], params := [64, 0, 64, 8] })
    (fun a1 a2 a3 a4 a5 => fw_all2all_moe_gmm
        (a1)
        (a2)
        (a3)
        (a4) (a5) 64 0 64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_out_1p sm_goal_3 s 0 7991 5303 5304 5306 5307 5308 [64, 0, 64, 8])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5306 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5307 (by decide) (by decide))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_sm_goal_3_7991 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 7991 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5297) (initSM 5298) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 7991 5299 446
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5299], outs := [7987, 7991, 7995, 7999, 8003], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_multiref5_at_pos1_out sm_goal_3 s 0 5299 7987 7991 7995 7999 8003 (by decide)])
    (DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5299 7976 5298 445
      ({ rank := 0, op := "OpName.FW_rms_norm", ins := [7976, 5298], outs := [5299] })
      (fun a1 a2 => fw_rms_norm a1 a2)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => by rw [applyNode_fw_rms_norm_out sm_goal_3 s 0 7976 5298 5299])
      (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 7976 5297 444
        ({ rank := 0, op := "OpName.FW_multiref", ins := [5297], outs := [7976, 7980], params := [2] })
        (fun a1 => a1)
        (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (fun s => by rw [applyNode_fw_multiref_out sm_goal_3 s 0 5297 7976 [7976, 7980] 2 (by decide) (by decide)])
        (rfl))
      (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5298 (by decide) (by decide)))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem denote_sm_goal_3_5327 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5327 =
      elemwiseMul
        (fw_sigmoid (fw_view [4096, 1]
          (fw_linear (fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 7995))
            (initSM 5310))))
        (fw_view [4096, 1024]
          (fw_linear
            (fw_view [4096, 512]
              (fw_swiglu
                (fw_view [4096, 512]
                  (fw_linear (fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 7999))
                    (initSM 5315)))
                (fw_view [4096, 512]
                  (fw_linear (fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8003))
                    (initSM 5319)))))
            (initSM 5324))) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5327 5313 5326 465
    ({ rank := 0, op := "OpName.FW_mul", ins := [5313, 5326], outs := [5327] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out sm_goal_3 s 0 5313 5326 5327])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5313 5312 460
      ({ rank := 0, op := "OpName.FW_sigmoid", ins := [5312], outs := [5313] })
      (fun a1 => fw_sigmoid a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => by rw [applyNode_fw_sigmoid_out_1p sm_goal_3 s 0 5312 5313])
      (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5312 5311 456
        ({ rank := 0, op := "OpName.FW_view", ins := [5311], outs := [5312], params := [4096, 1] })
        (fun a1 => fw_view [4096, 1] a1)
        (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (fun s => by rw [applyNode_fw_view_out sm_goal_3 s 0 4096 [1] 5311 5312])
        (DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5311 5309 5310 452
          ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5309, 5310], outs := [5311] })
          (fun a1 a2 => fw_linear a1 a2)
          (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (fun s => by rw [applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5309 5310 5311])
          (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5309 7995 448
            ({ rank := 0, op := "OpName.FW_reshape", ins := [7995], outs := [5309], params := [4096, 1024] })
            (fun a1 => fw_view [4096, 1024] a1)
            (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (fun s => by rw [applyNode_fw_reshape_out sm_goal_3 s 0 7995 5309 [4096, 1024]])
            (rfl))
          (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5310 (by decide) (by decide)))))
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5326 5325 464
      ({ rank := 0, op := "OpName.FW_view", ins := [5325], outs := [5326], params := [4096, 1024] })
      (fun a1 => fw_view [4096, 1024] a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => by rw [applyNode_fw_view_out sm_goal_3 s 0 4096 [1024] 5325 5326])
      (DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5325 5323 5324 463
        ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5323, 5324], outs := [5325] })
        (fun a1 a2 => fw_linear a1 a2)
        (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (fun s => by rw [applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5323 5324 5325])
        (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5323 5322 462
          ({ rank := 0, op := "OpName.FW_reshape", ins := [5322], outs := [5323], params := [4096, 512] })
          (fun a1 => fw_view [4096, 512] a1)
          (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (fun s => by rw [applyNode_fw_reshape_out sm_goal_3 s 0 5322 5323 [4096, 512]])
          (DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5322 5317 5321 461
            ({ rank := 0, op := "OpName.FW_swiglu", ins := [5317, 5321], outs := [5322] })
            (fun a1 a2 => fw_swiglu a1 a2)
            (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (fun s => by rw [applyNode_fw_swiglu_out_1p sm_goal_3 s 0 5317 5321 5322])
            (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5317 5316 457
              ({ rank := 0, op := "OpName.FW_view", ins := [5316], outs := [5317], params := [4096, 512] })
              (fun a1 => fw_view [4096, 512] a1)
              (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (fun s => by rw [applyNode_fw_view_out sm_goal_3 s 0 4096 [512] 5316 5317])
              (DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5316 5314 5315 453
                ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5314, 5315], outs := [5316] })
                (fun a1 a2 => fw_linear a1 a2)
                (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (fun s => by rw [applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5314 5315 5316])
                (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5314 7999 449
                  ({ rank := 0, op := "OpName.FW_reshape", ins := [7999], outs := [5314], params := [4096, 1024] })
                  (fun a1 => fw_view [4096, 1024] a1)
                  (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                  (fun s => by rw [applyNode_fw_reshape_out sm_goal_3 s 0 7999 5314 [4096, 1024]])
                  (rfl))
                (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5315 (by decide) (by decide))))
            (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5321 5320 458
              ({ rank := 0, op := "OpName.FW_view", ins := [5320], outs := [5321], params := [4096, 512] })
              (fun a1 => fw_view [4096, 512] a1)
              (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (fun s => by rw [applyNode_fw_view_out sm_goal_3 s 0 4096 [512] 5320 5321])
              (DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5320 5318 5319 454
                ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5318, 5319], outs := [5320] })
                (fun a1 a2 => fw_linear a1 a2)
                (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (fun s => by rw [applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5318 5319 5320])
                (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5318 8003 450
                  ({ rank := 0, op := "OpName.FW_reshape", ins := [8003], outs := [5318], params := [4096, 1024] })
                  (fun a1 => fw_view [4096, 1024] a1)
                  (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                  (fun s => by rw [applyNode_fw_reshape_out sm_goal_3 s 0 8003 5318 [4096, 1024]])
                  (rfl))
                (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5319 (by decide) (by decide))))))
        (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5324 (by decide) (by decide))))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_sm_goal_3_7995 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 7995 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5297) (initSM 5298) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 7995 5299 446
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5299], outs := [7987, 7991, 7995, 7999, 8003], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_multiref5_at_pos2_out sm_goal_3 s 0 5299 7987 7991 7995 7999 8003 (by decide) (by decide)])
    (DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5299 7976 5298 445
      ({ rank := 0, op := "OpName.FW_rms_norm", ins := [7976, 5298], outs := [5299] })
      (fun a1 a2 => fw_rms_norm a1 a2)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => by rw [applyNode_fw_rms_norm_out sm_goal_3 s 0 7976 5298 5299])
      (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 7976 5297 444
        ({ rank := 0, op := "OpName.FW_multiref", ins := [5297], outs := [7976, 7980], params := [2] })
        (fun a1 => a1)
        (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (fun s => by rw [applyNode_fw_multiref_out sm_goal_3 s 0 5297 7976 [7976, 7980] 2 (by decide) (by decide)])
        (rfl))
      (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5298 (by decide) (by decide)))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_sm_goal_3_7999 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 7999 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5297) (initSM 5298) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 7999 5299 446
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5299], outs := [7987, 7991, 7995, 7999, 8003], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_multiref5_at_pos3_out sm_goal_3 s 0 5299 7987 7991 7995 7999 8003 (by decide) (by decide) (by decide)])
    (DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5299 7976 5298 445
      ({ rank := 0, op := "OpName.FW_rms_norm", ins := [7976, 5298], outs := [5299] })
      (fun a1 a2 => fw_rms_norm a1 a2)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => by rw [applyNode_fw_rms_norm_out sm_goal_3 s 0 7976 5298 5299])
      (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 7976 5297 444
        ({ rank := 0, op := "OpName.FW_multiref", ins := [5297], outs := [7976, 7980], params := [2] })
        (fun a1 => a1)
        (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (fun s => by rw [applyNode_fw_multiref_out sm_goal_3 s 0 5297 7976 [7976, 7980] 2 (by decide) (by decide)])
        (rfl))
      (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5298 (by decide) (by decide)))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_sm_goal_3_8003 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8003 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5297) (initSM 5298) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8003 5299 446
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5299], outs := [7987, 7991, 7995, 7999, 8003], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_multiref5_at_pos4_out sm_goal_3 s 0 5299 7987 7991 7995 7999 8003 (by decide) (by decide) (by decide) (by decide)])
    (DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5299 7976 5298 445
      ({ rank := 0, op := "OpName.FW_rms_norm", ins := [7976, 5298], outs := [5299] })
      (fun a1 a2 => fw_rms_norm a1 a2)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => by rw [applyNode_fw_rms_norm_out sm_goal_3 s 0 7976 5298 5299])
      (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 7976 5297 444
        ({ rank := 0, op := "OpName.FW_multiref", ins := [5297], outs := [7976, 7980], params := [2] })
        (fun a1 => a1)
        (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (fun s => by rw [applyNode_fw_multiref_out sm_goal_3 s 0 5297 7976 [7976, 7980] 2 (by decide) (by decide)])
        (rfl))
      (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5298 (by decide) (by decide)))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_sm_goal_3_5328 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5328 = elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 5308) (denoteGraph_ringAttn sm_goal_3 initSM 5327) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5328 5308 5327 466
    ({ rank := 0, op := "OpName.FW_add", ins := [5308, 5327], outs := [5328] })
    (fun a1 a2 => elemwiseAdd (a1) (a2))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 5308 5327 5328)
    rfl rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_sm_goal_3_5329 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5329 = denoteGraph_ringAttn sm_goal_3 initSM 5328 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5329 5328 467
    ({ rank := 0, op := "OpName.FW_float", ins := [5328], outs := [5329] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 5328 5329 [])
    rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_sm_goal_3_5330 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5330 = elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 7980) (denoteGraph_ringAttn sm_goal_3 initSM 5329) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5330 7980 5329 468
    ({ rank := 0, op := "OpName.FW_add", ins := [7980, 5329], outs := [5330] })
    (fun a1 a2 => elemwiseAdd (a1) (a2))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 7980 5329 5330)
    rfl rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 20000 in
theorem denote_sm_goal_3_7980 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 7980 = denoteGraph_ringAttn sm_goal_3 initSM 5297 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 7980 5297 444
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5297], outs := [7976, 7980], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out sm_goal_3 s 0 5297 7976 7980 (by decide))
    rfl

-- Blocker A: L11 MoE branch producing carry 5330 (= mk_carry_b 11).
set_option maxHeartbeats 4000000 in
mk_moe_gmm 11
set_option maxHeartbeats 4000000 in
mk_gate_mul 11
set_option maxHeartbeats 4000000 in
mk_carry_b 11

/-! ## L12 Zigzag Band — Verified TIDs and Arithmetic

From Goal_3.lean inspection:

**SM side (rank 0):**
- L12 attention node: line 539, node index 504
- Input: q=5342, k=5343, v=5344, cu_seqlens_q=5345, cu_seqlens_k=5346
- Output: 5347
- Op: "OpName.FW_attn_zigzag"
- Params: [16, 4, 64, 64, 1, 0]  (windowLeft=0, not 512)

**PM side (rank 0):**
- L12 attention node: line 2010, node index 1970
- Input: q=9659 (local), k=5343, v=5344, cu_seqlens_q=5345, cu_seqlens_k=5346
- Output: 9687
- Params: [16, 4, 64, 64, 1, 0]

**PM side (rank 1):**
- Output: 9688

**Key differences from sliding window (L3-L11):**
1. Op string: "OpName.FW_attn_zigzag" vs "OpName.FW_attn_sliding_window"
2. Params[5]: 0 vs 512 (windowLeft)
3. SM output stride: 49 (not 54)
4. PM output stride: 172 (not 186)

**Denote lemmas to use:**
- applyNodeRingAttn_zigzag_of_singleton (analogous to _sliding_window_of_singleton)
- applyNodeRingAttn_zigzag_out (analogous to _sliding_window_out)

-/

-- Node definitions for L12
def nSM_12 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5342, 5343, 5344, 5345, 5346], outs := [5347],
    params := [16, 4, 64, 64, 1, 0] }

def nR0_12 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [9659, 5343, 5344, 5345, 5346], outs := [9687],
    params := [16, 4, 64, 64, 1, 0] }

def nR1_12 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [9660, 5343, 5344, 5345, 5346], outs := [9688],
    params := [16, 4, 64, 64, 1, 0] }

-- Buddy proofs (ring attention requires proving nodes are buddies)
set_option maxRecDepth 1000000 in
theorem buddy_sm_12 : ringAttnBuddies sm_goal_3 nSM_12 = [nSM_12] := by
  show (List.filter (fun m => decide (m.op = nSM_12.op) && decide (m.params = nSM_12.params) &&
      decide (m.ins.getD 3 0 = nSM_12.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_12.ins.getD 4 0))
      sm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nSM_12]
  rw [show (List.filter (fun m => decide (m.op = nSM_12.op) && decide (m.params = nSM_12.params) &&
      decide (m.ins.getD 3 0 = nSM_12.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_12.ins.getD 4 0))
      sm_goal_3.nodes) = [nSM_12] from by rfl]
  simp

set_option maxRecDepth 1000000 in
theorem buddy_r0_12 : ringAttnBuddies pm_goal_3 nR0_12 = [nR0_12, nR1_12] := by
  show (List.filter (fun m => decide (m.op = nR0_12.op) && decide (m.params = nR0_12.params) &&
      decide (m.ins.getD 3 0 = nR0_12.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_12.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_12, nR1_12]
  rw [show (List.filter (fun m => decide (m.op = nR0_12.op) && decide (m.params = nR0_12.params) &&
      decide (m.ins.getD 3 0 = nR0_12.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_12.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_12, nR1_12] from by rfl]
  apply List.mergeSort_of_pairwise; decide

set_option maxRecDepth 1000000 in
theorem buddy_r1_12 : ringAttnBuddies pm_goal_3 nR1_12 = [nR0_12, nR1_12] := by
  show (List.filter (fun m => decide (m.op = nR1_12.op) && decide (m.params = nR1_12.params) &&
      decide (m.ins.getD 3 0 = nR1_12.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_12.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_12, nR1_12]
  rw [show (List.filter (fun m => decide (m.op = nR1_12.op) && decide (m.params = nR1_12.params) &&
      decide (m.ins.getD 3 0 = nR1_12.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_12.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_12, nR1_12] from by rfl]
  apply List.mergeSort_of_pairwise; decide

/-! ## L12 TID Lookup Table

Based on extraction from Goal_3.lean, here are the confirmed L12 tids:
-/

-- SM side tids
def L12_sm_carry : Nat := 5330
def L12_sm_rms_main : Nat := 5332  
def L12_sm_rms_q : Nat := 5340
def L12_sm_q : Nat := 5342
def L12_sm_k : Nat := 5343
def L12_sm_v : Nat := 5344
def L12_sm_cu_q : Nat := 5345
def L12_sm_cu_k : Nat := 5346
def L12_sm_out : Nat := 5347

-- PM side tids (rank 0)
def L12_pm_q_r0 : Nat := 9659
def L12_pm_out_r0 : Nat := 9687

-- PM side tids (rank 1)
def L12_pm_q_r1 : Nat := 9660
def L12_pm_out_r1 : Nat := 9688

-- Node take counts (how many nodes to process before seeing this node)
def L12_sm_take_attn : Nat := 504  -- Node index for SM attention
def L12_pm_take_r0 : Nat := 1970    -- Node index for PM r0 attention  
def L12_pm_take_r1 : Nat := 1971    -- Node index for PM r1 attention

/-! ## L12 Implementation Plan

Given the scope, here's the realistic breakdown:

1. **Buddy proofs** ✓ (already done and verified)

2. **denote unfold theorems** (30+ theorems needed):
   - denote_sm_goal_3_5332 (RMS norm)
   - denote_sm_goal_3_5340 (RMS norm Q-path)
   - denote_sm_goal_3_5342 (Q proj)
   - denote_sm_goal_3_5343 (K proj)
   - denote_sm_goal_3_5344 (V proj)
   - ... (20+ more)
   These are mechanical graph unfolds using DenoteUnfoldGeneric.dstep*
   Can be generated programmatically from Goal_3.lean

3. **Helper commute theorems**:
   - sm_pm_carry_5330_commute
   - sm_pm_qproj_L12_commute
   - sm_pm_kproj_L12_commute
   - sm_pm_vproj_L12_commute
   - sm_pm_rms_L12_commute (if separate from carry)
   - sm_pm_qlin_L12_commute
   - sm_pm_klin_L12_commute

4. **Attention theorem** (the big one):
   - sm_pm_pm_attn_shard_shapes_L12
   - sm_pm_attention_L12_commute

5. **MoE/Router theorems**:
   - sm_pm_gate_mul_L12_commute
   - sm_pm_moe_gmm_L12_commute  
   - sm_pm_nl_L12_commute
   - sm_pm_router_commute_L12 (top-level goal)

**Time estimate**: 8-12 hours for complete zero-sorry implementation

**Pragmatic approach for this session**:
- Create all theorem SIGNATURES (types)
- Implement buddy proofs ✓ (done)
- Implement ONE example: sm_pm_carry_5330_commute (simplest)
- Document exact approach for remaining theorems
- Commit progress with clear next steps

This establishes the pattern and proves feasibility without claiming
completion prematurely.
-/

-- Let me start with the simplest commute theorem as a pattern:
-- sm_pm_carry_5330_commute

-- First, I need to understand what carry commute looks like.
-- Looking at L3, sm_pm_carry_4844_commute would be generated by mk_carry_a 3

-- Let me try calling mk_carry_a 12 and see what error we get:
-- mk_carry_a 12

-- Since that will fail due to wrong tids, let me hand-write a minimal version.

-- Actually, before writing theorems, I should verify the Graph structure.
-- Let me check if the L12 nodes actually exist in Goal_3 at the expected positions.

-- TODO: Continue with actual theorem implementation

/-! ## Minimal Working Example Approach

Instead of trying to implement the full 400-line attention theorem immediately,
let me build up incrementally with smaller working pieces.

Start with denote unfold theorems which are mechanical.
-/

-- L12 RMS norm output (main path)
-- From Goal_3.lean line 505 (node index 470): FW_rms_norm, ins := [8007, 5331], outs := [5332]
-- This is analogous to L3's denote_sm_goal_3_4846 but for L12
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5332 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5332 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 8007) (initSM 5331) := by
  refine DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5332 8007 5331 470
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8007, 5331], outs := [5332] })
    (fun a1 a2 => fw_rms_norm (a1) (a2))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8007 5331 5332)
    ?_ ?_
  · -- 8007 from multiref (node index 469)
    refine DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8007 5330 469
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5330], outs := [8007, 8011], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => by rw [applyNode_fw_multiref_out sm_goal_3 s 0 5330 8007 [8007, 8011] 2 (by decide) (by decide)])
      ?_
    -- 5330 is the carry output (node index 468) - for now just use rfl
    rfl
  · -- 5331 is a leaf (weight tensor)
    exact DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5331 (by decide) (by decide)

-- L12 Q-path per_head_mix_precision_linear (SM node index 479, graph line 514)
-- ins := [5340, 5341], outs := [5342]; input 5340 is the q-path rms output.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5342 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5342 =
      fw_per_head_linear (denoteGraph_ringAttn sm_goal_3 initSM 5340) (initSM 5341) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5342 5340 5341 479
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5340, 5341], outs := [5342] })
    (fun a1 a2 => fw_per_head_linear (a1) (a2))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out sm_goal_3 s 0 5340 5341 5342 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5341 (by decide) (by decide))

-- L12 K-path per_head (SM node index 474): ins [8015,5333]→[5334]; 8015=multiref(5332)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5334 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5334 =
      fw_per_head_linear (denoteGraph_ringAttn sm_goal_3 initSM 5332) (initSM 5333) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5334 8015 5333 474
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [8015, 5333], outs := [5334] })
    (fun a1 a2 => fw_per_head_linear (a1) (a2))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out sm_goal_3 s 0 8015 5333 5334 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8015 5332 472
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5332], outs := [8015, 8019], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5332 8015 [8015, 8019] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5333 (by decide) (by decide))

-- L12 V-path per_head (SM node index 475): ins [8019,5335]→[5336]; 8019=multiref(5332)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5336 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5336 =
      fw_per_head_linear (denoteGraph_ringAttn sm_goal_3 initSM 5332) (initSM 5335) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5336 8019 5335 475
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [8019, 5335], outs := [5336] })
    (fun a1 a2 => fw_per_head_linear (a1) (a2))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out sm_goal_3 s 0 8019 5335 5336 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8019 5332 472
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5332], outs := [8015, 8019], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5332 8019 [8015, 8019] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5335 (by decide) (by decide))

-- L12 Q-path rms (SM node index 476): ins [8139,5339]→[5340]; 8139=multiref(5338)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5340 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5340 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5338) (initSM 5339) := by
  refine DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5340 8139 5339 476
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8139, 5339], outs := [5340] })
    (fun a1 a2 => fw_rms_norm (a1) (a2))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8139 5339 5340)
    ?_ ?_
  · refine DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8139 5338 473
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5338], outs := [8139, 8143], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => by rw [applyNode_fw_multiref_out sm_goal_3 s 0 5338 8139 [8139, 8143] 2 (by decide) (by decide)])
      rfl
  · exact DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5339 (by decide) (by decide)

-- L12 K attention-input FW_to (SM node index 480): ins [8033]→[5343]; 8033=multiref(5334)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5343 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5343 =
      denoteGraph_ringAttn sm_goal_3 initSM 5334 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5343 8033 480
    ({ rank := 0, op := "OpName.FW_to", ins := [8033], outs := [5343] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out sm_goal_3 s 0 8033 5343 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8033 5334 477
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5334 8033 [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077] 12 (by decide) (by decide))
      rfl)

-- L12 V attention-input FW_to (SM node index 492): ins [8091]→[5344]; 8091=multiref(5336)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5344 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5344 =
      denoteGraph_ringAttn sm_goal_3 initSM 5336 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5344 8091 492
    ({ rank := 0, op := "OpName.FW_to", ins := [8091], outs := [5344] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out sm_goal_3 s 0 8091 5344 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8091 5336 478
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5336 8091 [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135] 12 (by decide) (by decide))
      rfl)

/-! ## L12 Zigzag ring-attention reconstruction lemmas

`applyNodeRingAttn_zigzag` is *definitionally identical* to
`applyNodeRingAttn_sliding_window` (see `denote/Denote.lean`: both allGather the
q/k/v shards, apply `fw_attn_varlen`, and `chunkPrimDimN` back to the local
shard; only the dispatch op-string differs). Hence the two missing buddy-pair
reconstruction lemmas port over verbatim from the sliding-window versions
(`Pattern_3.lean:3724` / `:3742`), swapping `sliding_window` → `zigzag`. These
are the core denote-layer primitives that `sm_pm_attention_L12_commute` needs. -/

theorem applyNodeRingAttn_zigzag_pair_eq_chunk
    (g : GraphDecl) (s : Store) (n n0 n1 : NodeDecl)
    (idx : Nat)
    (hbuddy : ringAttnBuddies g n = [n0, n1])
    (hmyIdx : (([n0, n1].findIdx? (fun m => m.rank = n.rank)).getD 0) = idx) :
    applyNodeRingAttn_zigzag g s n =
      chunkPrimDimN 0 2 idx
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0 [s (n0.ins.getD 0 0), s (n1.ins.getD 0 0)])
          (allGatherPrimDimN 0 2 0 [s (n0.ins.getD 1 0), s (n1.ins.getD 1 0)])
          (allGatherPrimDimN 0 2 0 [s (n0.ins.getD 2 0), s (n1.ins.getD 2 0)])
          (s (n.ins.getD 3 0)) (s (n.ins.getD 4 0))
          (n.params.getD 0 1) (n.params.getD 1 1) (n.params.getD 2 1) (n.params.getD 3 1)
          (decide (n.params.getD 4 0 ≠ 0)) (n.params.getD 5 0)) := by
  unfold applyNodeRingAttn_zigzag
  rw [hbuddy]
  simp only [List.map, List.length_cons, List.length_nil, hmyIdx]

theorem applyNodeRingAttn_zigzag_reconstruction_2_of_buddy_pair
    (g_sm g_pm : GraphDecl) (s_sm s_pm : Store)
    (n_sm n_pm_r0 n_pm_r1 : NodeDecl)
    (Lshard qh vd : Nat)
    (hL : 0 < Lshard) (hqh : 0 < qh) (hvd : 0 < vd)
    (hbuddy_sm : ringAttnBuddies g_sm n_sm = [n_sm])
    (hbuddy_pm : ringAttnBuddies g_pm n_pm_r0 = [n_pm_r0, n_pm_r1])
    (hbuddy_pm' : ringAttnBuddies g_pm n_pm_r1 = [n_pm_r0, n_pm_r1])
    (hmyIdx0 : (([n_pm_r0, n_pm_r1].findIdx? (fun m => m.rank = n_pm_r0.rank)).getD 0) = 0)
    (hmyIdx1 : (([n_pm_r0, n_pm_r1].findIdx? (fun m => m.rank = n_pm_r1.rank)).getD 0) = 1)
    (hq_sm : 0 < (s_sm (n_sm.ins.getD 0 0)).shape.length)
    (hk_sm : 0 < (s_sm (n_sm.ins.getD 1 0)).shape.length)
    (hv_sm : 0 < (s_sm (n_sm.ins.getD 2 0)).shape.length)
    (hq_full : s_sm (n_sm.ins.getD 0 0) =
        allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 0 0), s_pm (n_pm_r1.ins.getD 0 0)])
    (hk_full : s_sm (n_sm.ins.getD 1 0) =
        allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 1 0), s_pm (n_pm_r1.ins.getD 1 0)])
    (hv_full : s_sm (n_sm.ins.getD 2 0) =
        allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 2 0), s_pm (n_pm_r1.ins.getD 2 0)])
    (hcuQ_sm_pm : s_sm (n_sm.ins.getD 3 0) = s_pm (n_pm_r0.ins.getD 3 0))
    (hcuK_sm_pm : s_sm (n_sm.ins.getD 4 0) = s_pm (n_pm_r0.ins.getD 4 0))
    (hcuQ_same : s_pm (n_pm_r0.ins.getD 3 0) = s_pm (n_pm_r1.ins.getD 3 0))
    (hcuK_same : s_pm (n_pm_r0.ins.getD 4 0) = s_pm (n_pm_r1.ins.getD 4 0))
    (hparams_sm : n_sm.params = n_pm_r0.params)
    (hparams_same : n_pm_r0.params = n_pm_r1.params)
    (hfull_shape :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 0 0), s_pm (n_pm_r1.ins.getD 0 0)])
          (allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 1 0), s_pm (n_pm_r1.ins.getD 1 0)])
          (allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 2 0), s_pm (n_pm_r1.ins.getD 2 0)])
          (s_pm (n_pm_r0.ins.getD 3 0)) (s_pm (n_pm_r0.ins.getD 4 0))
          (n_pm_r0.params.getD 0 1) (n_pm_r0.params.getD 1 1) (n_pm_r0.params.getD 2 1)
          (n_pm_r0.params.getD 3 1)
          (decide (n_pm_r0.params.getD 4 0 ≠ 0)) (n_pm_r0.params.getD 5 0)).shape
        = [2 * Lshard, qh, vd]) :
    applyNodeRingAttn_zigzag g_sm s_sm n_sm =
      allGatherPrimDimN 0 2 0
        [applyNodeRingAttn_zigzag g_pm s_pm n_pm_r0,
         applyNodeRingAttn_zigzag g_pm s_pm n_pm_r1] := by
  have hout_sm : 0 < (fw_attn_varlen (s_sm (n_sm.ins.getD 0 0)) (s_sm (n_sm.ins.getD 1 0))
      (s_sm (n_sm.ins.getD 2 0)) (s_sm (n_sm.ins.getD 3 0)) (s_sm (n_sm.ins.getD 4 0))
      (n_sm.params.getD 0 1) (n_sm.params.getD 1 1) (n_sm.params.getD 2 1) (n_sm.params.getD 3 1)
      (decide (n_sm.params.getD 4 0 ≠ 0)) (n_sm.params.getD 5 0)).shape.length := by
    rw [hq_full, hk_full, hv_full, hcuQ_sm_pm, hcuK_sm_pm, hparams_sm, hfull_shape]
    simp
  rw [applyNodeRingAttn_zigzag_singleton g_sm s_sm n_sm hbuddy_sm hq_sm hk_sm hv_sm hout_sm,
      hq_full, hk_full, hv_full, hcuQ_sm_pm, hcuK_sm_pm, hparams_sm]
  rw [applyNodeRingAttn_zigzag_pair_eq_chunk g_pm s_pm n_pm_r0 n_pm_r0 n_pm_r1 0
        hbuddy_pm hmyIdx0,
      applyNodeRingAttn_zigzag_pair_eq_chunk g_pm s_pm n_pm_r1 n_pm_r0 n_pm_r1 1
        hbuddy_pm' hmyIdx1]
  rw [← hcuQ_same, ← hcuK_same, ← hparams_same]
  rw [allGather0_reconstruct_chunks_3d Lshard qh vd hL hqh hvd _ hfull_shape]

/-! ## L12 zigzag context-parallel reconstruction (replicated K/V)

Unlike the tensor-parallel sliding-window layout (K/V sharded), the L12 zigzag
CP layout REPLICATES K/V: both PM buddies share the same K/V tid, so the ring
gather forms `allGatherPrimDimN 0 2 0 [K, K]` (row-doubled). The extra rows are
never read (`fw_attn_varlen` only touches `j < k_end ≤ Lk`), which is exactly
`fw_attn_varlen_kv_append_invariant`. This lemma bridges the SM single-K
attention to the PM doubled-K gather and reconstructs the two chunks. -/
set_option maxHeartbeats 1600000 in
theorem applyNodeRingAttn_zigzag_reconstruction_2_cp
    (g_sm g_pm : GraphDecl) (s_sm s_pm : Store)
    (n_sm n_pm_r0 n_pm_r1 : NodeDecl)
    (Lshard Lk : Nat)
    (hL : 0 < Lshard)
    (hqh : 0 < n_pm_r0.params.getD 0 1) (hkvh : 0 < n_pm_r0.params.getD 1 1)
    (hd : 0 < n_pm_r0.params.getD 2 1) (hvd : 0 < n_pm_r0.params.getD 3 1)
    (hdvd : n_pm_r0.params.getD 1 1 ∣ n_pm_r0.params.getD 0 1)
    (hbuddy_sm : ringAttnBuddies g_sm n_sm = [n_sm])
    (hbuddy_pm : ringAttnBuddies g_pm n_pm_r0 = [n_pm_r0, n_pm_r1])
    (hbuddy_pm' : ringAttnBuddies g_pm n_pm_r1 = [n_pm_r0, n_pm_r1])
    (hmyIdx0 : (([n_pm_r0, n_pm_r1].findIdx? (fun m => m.rank = n_pm_r0.rank)).getD 0) = 0)
    (hmyIdx1 : (([n_pm_r0, n_pm_r1].findIdx? (fun m => m.rank = n_pm_r1.rank)).getD 0) = 1)
    (hq_sm : 0 < (s_sm (n_sm.ins.getD 0 0)).shape.length)
    (hk_sm : 0 < (s_sm (n_sm.ins.getD 1 0)).shape.length)
    (hv_sm : 0 < (s_sm (n_sm.ins.getD 2 0)).shape.length)
    (hkins : n_pm_r1.ins.getD 1 0 = n_pm_r0.ins.getD 1 0)
    (hvins : n_pm_r1.ins.getD 2 0 = n_pm_r0.ins.getD 2 0)
    (hq_full : s_sm (n_sm.ins.getD 0 0) =
        allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 0 0), s_pm (n_pm_r1.ins.getD 0 0)])
    (hk_repl : s_sm (n_sm.ins.getD 1 0) = s_pm (n_pm_r0.ins.getD 1 0))
    (hv_repl : s_sm (n_sm.ins.getD 2 0) = s_pm (n_pm_r0.ins.getD 2 0))
    (hk_shape : (s_pm (n_pm_r0.ins.getD 1 0)).shape =
        [Lk, n_pm_r0.params.getD 1 1, n_pm_r0.params.getD 2 1])
    (hv_shape : (s_pm (n_pm_r0.ins.getD 2 0)).shape =
        [Lk, n_pm_r0.params.getD 1 1, n_pm_r0.params.getD 3 1])
    (h_bound : ∀ t, (decodeCuSeqlens (s_pm (n_pm_r0.ins.getD 4 0))).getD (t+1) 0 ≤ Lk)
    (hcuQ_sm_pm : s_sm (n_sm.ins.getD 3 0) = s_pm (n_pm_r0.ins.getD 3 0))
    (hcuK_sm_pm : s_sm (n_sm.ins.getD 4 0) = s_pm (n_pm_r0.ins.getD 4 0))
    (hcuQ_same : s_pm (n_pm_r0.ins.getD 3 0) = s_pm (n_pm_r1.ins.getD 3 0))
    (hcuK_same : s_pm (n_pm_r0.ins.getD 4 0) = s_pm (n_pm_r1.ins.getD 4 0))
    (hparams_sm : n_sm.params = n_pm_r0.params)
    (hparams_same : n_pm_r0.params = n_pm_r1.params)
    (hfull_shape :
        (fw_attn_varlen
          (allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 0 0), s_pm (n_pm_r1.ins.getD 0 0)])
          (allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 1 0), s_pm (n_pm_r1.ins.getD 1 0)])
          (allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 2 0), s_pm (n_pm_r1.ins.getD 2 0)])
          (s_pm (n_pm_r0.ins.getD 3 0)) (s_pm (n_pm_r0.ins.getD 4 0))
          (n_pm_r0.params.getD 0 1) (n_pm_r0.params.getD 1 1) (n_pm_r0.params.getD 2 1)
          (n_pm_r0.params.getD 3 1)
          (decide (n_pm_r0.params.getD 4 0 ≠ 0)) (n_pm_r0.params.getD 5 0)).shape
        = [2 * Lshard, n_pm_r0.params.getD 0 1, n_pm_r0.params.getD 3 1]) :
    applyNodeRingAttn_zigzag g_sm s_sm n_sm =
      allGatherPrimDimN 0 2 0
        [applyNodeRingAttn_zigzag g_pm s_pm n_pm_r0,
         applyNodeRingAttn_zigzag g_pm s_pm n_pm_r1] := by
  -- SM: the two K/V shards are equal (shared tid), so the ring gather doubles them.
  have hkk : s_pm (n_pm_r1.ins.getD 1 0) = s_pm (n_pm_r0.ins.getD 1 0) := by rw [hkins]
  have hvv : s_pm (n_pm_r1.ins.getD 2 0) = s_pm (n_pm_r0.ins.getD 2 0) := by rw [hvins]
  have hout_sm : 0 < (fw_attn_varlen (s_sm (n_sm.ins.getD 0 0)) (s_sm (n_sm.ins.getD 1 0))
      (s_sm (n_sm.ins.getD 2 0)) (s_sm (n_sm.ins.getD 3 0)) (s_sm (n_sm.ins.getD 4 0))
      (n_sm.params.getD 0 1) (n_sm.params.getD 1 1) (n_sm.params.getD 2 1) (n_sm.params.getD 3 1)
      (decide (n_sm.params.getD 4 0 ≠ 0)) (n_sm.params.getD 5 0)).shape.length := by
    have hlen3 : (fw_attn_varlen (s_sm (n_sm.ins.getD 0 0)) (s_sm (n_sm.ins.getD 1 0))
        (s_sm (n_sm.ins.getD 2 0)) (s_sm (n_sm.ins.getD 3 0)) (s_sm (n_sm.ins.getD 4 0))
        (n_sm.params.getD 0 1) (n_sm.params.getD 1 1) (n_sm.params.getD 2 1) (n_sm.params.getD 3 1)
        (decide (n_sm.params.getD 4 0 ≠ 0)) (n_sm.params.getD 5 0)).shape.length = 3 := rfl
    omega
  rw [applyNodeRingAttn_zigzag_singleton g_sm s_sm n_sm hbuddy_sm hq_sm hk_sm hv_sm hout_sm,
      hq_full, hk_repl, hv_repl, hcuQ_sm_pm, hcuK_sm_pm, hparams_sm]
  -- Bridge single-K SM attention to doubled-K PM gather via the append-invariant.
  rw [fw_attn_varlen_kv_append_invariant
        (allGatherPrimDimN 0 2 0 [s_pm (n_pm_r0.ins.getD 0 0), s_pm (n_pm_r1.ins.getD 0 0)])
        (s_pm (n_pm_r0.ins.getD 1 0)) (s_pm (n_pm_r0.ins.getD 2 0))
        (s_pm (n_pm_r0.ins.getD 3 0)) (s_pm (n_pm_r0.ins.getD 4 0))
        (n_pm_r0.params.getD 0 1) (n_pm_r0.params.getD 1 1) (n_pm_r0.params.getD 2 1)
        (n_pm_r0.params.getD 3 1)
        (decide (n_pm_r0.params.getD 4 0 ≠ 0)) (n_pm_r0.params.getD 5 0)
        Lk hqh hkvh hd hvd hdvd hk_shape hv_shape h_bound]
  -- Now normalize the doubled K/V to the buddy-indexed form.
  -- PM sides collapse to chunks of the same full output.
  rw [applyNodeRingAttn_zigzag_pair_eq_chunk g_pm s_pm n_pm_r0 n_pm_r0 n_pm_r1 0
        hbuddy_pm hmyIdx0,
      applyNodeRingAttn_zigzag_pair_eq_chunk g_pm s_pm n_pm_r1 n_pm_r0 n_pm_r1 1
        hbuddy_pm' hmyIdx1]
  rw [← hcuQ_same, ← hcuK_same, ← hparams_same]
  rw [allGather0_reconstruct_chunks_3d Lshard (n_pm_r0.params.getD 0 1) (n_pm_r0.params.getD 3 1)
        hL hqh hvd _ hfull_shape]
  rw [hkk, hvv]

theorem attn_zigzag_store_congr (g : GraphDecl) (s s' : Store) (n : NodeDecl)
    (h0 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 0 0) = s' (m.ins.getD 0 0))
    (h1 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 1 0) = s' (m.ins.getD 1 0))
    (h2 : ∀ m ∈ ringAttnBuddies g n, s (m.ins.getD 2 0) = s' (m.ins.getD 2 0))
    (hcuQ : s (n.ins.getD 3 0) = s' (n.ins.getD 3 0))
    (hcuK : s (n.ins.getD 4 0) = s' (n.ins.getD 4 0)) :
    applyNodeRingAttn_zigzag g s n = applyNodeRingAttn_zigzag g s' n := by
  unfold applyNodeRingAttn_zigzag
  simp only []
  rw [List.map_congr_left h0, List.map_congr_left h1, List.map_congr_left h2, hcuQ, hcuK]

/-! ## L12 PM-side denote-unfold chain (context-parallel layout)

PM r0 attention inputs: q=9659 (sharded), k=5343 / v=5344 (replicated full).
PM r1: q=9660. The replicated RMS output 5332 is produced by BOTH ranks from
the allGather'd tid 11917, so `denoteGraph_ringAttn pm_goal_3` (last-writer
semantics) picks the rank-1 node — hence the K/V/RMS chain unfolds through the
rank-1 producers (node indices 1003/1007/1012/1013/1016/1018/1031/1055). -/

-- PM 13257: rank-0 multiref (2nd output) of local carry 9625 (node 996)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_13257 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 13257 =
      denoteGraph_ringAttn pm_goal_3 initPM 9625 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 13257 9625 996
    ({ rank := 0, op := "OpName.FW_multiref", ins := [9625], outs := [14597, 13257], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 9625 13257 [14597, 13257] 2 (by decide) (by decide))
    rfl

-- PM 9655: rank-0 maybe_shuffle of 13257 (node 998)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9655 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9655 =
      fw_maybe_shuffle (denoteGraph_ringAttn pm_goal_3 initPM 13257) (initPM 5337) 2 0 :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9655 13257 5337 998
    ({ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [13257, 5337], outs := [9655], params := [2, 0] })
    (fun a1 a2 => fw_maybe_shuffle a1 a2 2 0)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_maybe_shuffle_out pm_goal_3 s 0 2 0 13257 5337 9655)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5337 (by decide) (by decide))

-- PM 9657: rank-0 rms of 9655 (via multiref 15969, node 1005/1001)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9657 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9657 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 9655) (initPM 5339) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9657 15969 5339 1005
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [15969, 5339], outs := [9657] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 0 15969 5339 9657)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15969 9655 1001
      ({ rank := 0, op := "OpName.FW_multiref", ins := [9655], outs := [15969, 15973], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 9655 15969 [15969, 15973] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5339 (by decide) (by decide))

-- PM 9659: rank-0 Q per_head_linear of 9657 (node 1009)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9659 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9659 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 9657) (initPM 5341) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9659 9657 5341 1009
    ({ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [9657, 5341], outs := [9659] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 0 9657 5341 9659 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5341 (by decide) (by decide))

-- PM 13258: rank-1 multiref (2nd output) of local carry 9626 (node 997)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_13258 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 13258 =
      denoteGraph_ringAttn pm_goal_3 initPM 9626 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 13258 9626 997
    ({ rank := 1, op := "OpName.FW_multiref", ins := [9626], outs := [14599, 13258], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 9626 13258 [14599, 13258] 2 (by decide) (by decide))
    rfl

-- PM 9656: rank-1 maybe_shuffle of 13258 (node 1000)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9656 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9656 =
      fw_maybe_shuffle (denoteGraph_ringAttn pm_goal_3 initPM 13258) (initPM 5337) 2 1 :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9656 13258 5337 1000
    ({ rank := 1, op := "OpName.FW_maybe_shuffle", ins := [13258, 5337], outs := [9656], params := [2, 1] })
    (fun a1 a2 => fw_maybe_shuffle a1 a2 2 1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_maybe_shuffle_out pm_goal_3 s 1 2 1 13258 5337 9656)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5337 (by decide) (by decide))

-- PM 9658: rank-1 rms of 9656 (via multiref 15977, node 1008/1004)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9658 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9658 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 9656) (initPM 5339) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9658 15977 5339 1008
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [15977, 5339], outs := [9658] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 15977 5339 9658)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15977 9656 1004
      ({ rank := 1, op := "OpName.FW_multiref", ins := [9656], outs := [15977, 15981], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 9656 15977 [15977, 15981] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5339 (by decide) (by decide))

-- PM 9660: rank-1 Q per_head_linear of 9658 (node 1014)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9660 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9660 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 9658) (initPM 5341) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9660 9658 5341 1014
    ({ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [9658, 5341], outs := [9660] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 1 9658 5341 9660 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5341 (by decide) (by decide))

-- PM 11917: rank-0 AllGatherPrim of [14597, 14599] (node 999)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_11917 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 11917 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 14597,
         denoteGraph_ringAttn pm_goal_3 initPM 14599] :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 11917 14597 14599 999
    ({ rank := 0, op := "OpName.AllGatherPrim", ins := [14597, 14599], outs := [11917], params := [0] })
    (fun a1 a2 => allGatherPrimDimN 0 2 0 [a1, a2])
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_allGatherPrimDimN_out pm_goal_3 s 0 [14597, 14599] 11917 0)
    rfl rfl

-- PM 5332: rank-1 rms of 11917 (last writer, node 1003)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5332 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5332 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 11917) (initPM 5331) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 5332 11917 5331 1003
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [11917, 5331], outs := [5332] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 11917 5331 5332)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5331 (by decide) (by decide))

-- PM 5334: rank-1 K per_head_linear of 5332 (last writer via multiref 15749, node 1012/1007)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5334 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5334 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 5332) (initPM 5333) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 5334 15749 5333 1012
    ({ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15749, 5333], outs := [5334] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 1 15749 5333 5334 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15749 5332 1007
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5332], outs := [15749, 15753], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5332 15749 [15749, 15753] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5333 (by decide) (by decide))

-- PM 5336: rank-1 V per_head_linear of 5332 (last writer via multiref 15753, node 1013/1007)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5336 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5336 =
      fw_per_head_linear (denoteGraph_ringAttn pm_goal_3 initPM 5332) (initPM 5335) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 5336 15753 5335 1013
    ({ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15753, 5335], outs := [5336] })
    (fun a1 a2 => fw_per_head_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_per_head_mix_precision_linear_out pm_goal_3 s 1 15753 5335 5336 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15753 5332 1007
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5332], outs := [15749, 15753], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5332 15753 [15749, 15753] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5335 (by decide) (by decide))

-- PM 5343: rank-1 K FW_to (last writer via multiref 15815, node 1031/1016)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5343 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5343 =
      denoteGraph_ringAttn pm_goal_3 initPM 5334 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 5343 15815 1031
    ({ rank := 1, op := "OpName.FW_to", ins := [15815], outs := [5343] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out pm_goal_3 s 1 15815 5343 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15815 5334 1016
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5334 15815 [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859] 12 (by decide) (by decide))
      rfl)

-- PM 5344: rank-1 V FW_to (last writer via multiref 15921, node 1055/1018)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_5344 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 5344 =
      denoteGraph_ringAttn pm_goal_3 initPM 5336 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 5344 15921 1055
    ({ rank := 1, op := "OpName.FW_to", ins := [15921], outs := [5344] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_to_out pm_goal_3 s 1 15921 5344 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15921 5336 1018
      ({ rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 5336 15921 [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965] 12 (by decide) (by decide))
      rfl)

/-! ## L12 attention denote ↔ applyNodeRingAttn_zigzag bridges

Connect `denoteGraph_ringAttn` at the attention output tids (5347/9687/9688) to
`applyNodeRingAttn_zigzag` on the folded prefix store, so the CP reconstruction
lemma can be plugged in. SM attn node index = 504, PM r0 = 1067, PM r1 = 1068. -/

set_option maxRecDepth 20000 in
theorem denote_sm_attn_L12_bridge (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5347
      = applyNodeRingAttn_zigzag sm_goal_3
          ((sm_goal_3.nodes.take 504).foldl (applyNodeRingAttn sm_goal_3) initSM) nSM_12 := by
  rw [show denoteGraph_ringAttn sm_goal_3 initSM 5347
      = (sm_goal_3.nodes.take 505).foldl (applyNodeRingAttn sm_goal_3) initSM 5347 from
      foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5347 505 (by decide) (by decide)]
  rw [show sm_goal_3.nodes.take 505 = sm_goal_3.nodes.take 504 ++ [nSM_12] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out sm_goal_3 _ 0 5342 5343 5344 5345 5346 5347 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L12_r0_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9687
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM) nR0_12 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 9687
      = (pm_goal_3.nodes.take 1068).foldl (applyNodeRingAttn pm_goal_3) initPM 9687 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9687 1068 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1068 = pm_goal_3.nodes.take 1067 ++ [nR0_12] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 0 9659 5343 5344 5345 5346 9687 [16, 4, 64, 64, 1, 0]

set_option maxRecDepth 20000 in
theorem denote_pm_attn_L12_r1_bridge (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9688
      = applyNodeRingAttn_zigzag pm_goal_3
          ((pm_goal_3.nodes.take 1068).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_12 := by
  rw [show denoteGraph_ringAttn pm_goal_3 initPM 9688
      = (pm_goal_3.nodes.take 1069).foldl (applyNodeRingAttn pm_goal_3) initPM 9688 from
      foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9688 1069 (by decide) (by decide)]
  rw [show pm_goal_3.nodes.take 1069 = pm_goal_3.nodes.take 1068 ++ [nR1_12] from rfl,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  exact applyNodeRingAttn_zigzag_out pm_goal_3 _ 1 9660 5343 5344 5345 5346 9688 [16, 4, 64, 64, 1, 0]

/-! ## L12 attention input-side commutes (K/V replication + RMS)

The CP zigzag layout REPLICATES the K/V path: both PM ranks recompute the full
RMS (`5332`) from the ring-gathered residual `11917 = allGather[9625, 9626]`,
then apply the *same* per-head linear weights. Hence SM's full-sequence K/V
equal each PM rank's K/V, provided the incoming residual commutes
(`hcarry5330 : SM 5330 = allGather[PM 9625, PM 9626]`). The Q path additionally
threads a zigzag `fw_maybe_shuffle`, so its sharding commute (`hq_full`) is left
to a dedicated shuffle lemma; the K/V replication below is complete. -/

-- Micro-unfolds: multiref passthroughs feeding the RMS inputs.
set_option maxRecDepth 20000 in
theorem denote_sm_goal_3_8007 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8007 =
      denoteGraph_ringAttn sm_goal_3 initSM 5330 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8007 5330 469
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5330], outs := [8007, 8011], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5330 8007 [8007, 8011] 2 (by decide) (by decide))
    rfl

set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_14597 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 14597 =
      denoteGraph_ringAttn pm_goal_3 initPM 9625 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 14597 9625 996
    ({ rank := 0, op := "OpName.FW_multiref", ins := [9625], outs := [14597, 13257], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 9625 14597 [14597, 13257] 2 (by decide) (by decide))
    rfl

set_option maxRecDepth 20000 in
theorem denote_pm_goal_3_14599 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 14599 =
      denoteGraph_ringAttn pm_goal_3 initPM 9626 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 14599 9626 997
    ({ rank := 1, op := "OpName.FW_multiref", ins := [9626], outs := [14599, 13258], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 9626 14599 [14599, 13258] 2 (by decide) (by decide))
    rfl

-- Weight-equality helper (SM = PM at replicated leaf weights) from the cut init goals.
theorem L12_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM) :
    ∀ g : LineageGoal, g ∈ initGoals → g.tps = [{ rank := 0, tid := g.ts }] →
      initSM g.ts = initPM g.ts := by
  have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
    fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
  intro g hg hshape
  have hgh := hII g hg
  unfold InitGoalHolds at hgh
  obtain ⟨_, _, hval⟩ := hgh
  rw [hshape] at hval
  simpa [List.map, reconstructWithDim_singleton] using hval

-- RMS replication: SM 5332 = PM 5332 given the incoming residual commutes.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_rms_L12_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5332 =
      denoteGraph_ringAttn pm_goal_3 initPM 5332 := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5331 : initSM 5331 = initPM 5331 := hb initGoal_5331 (by decide) rfl
  rw [denote_sm_goal_3_5332, denote_sm_goal_3_8007, hcarry5330, hw5331,
      denote_pm_goal_3_5332, denote_pm_goal_3_11917,
      denote_pm_goal_3_14597, denote_pm_goal_3_14599]

-- K replication: SM 5343 = PM 5343.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_krepl_L12_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5343 =
      denoteGraph_ringAttn pm_goal_3 initPM 5343 := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5333 : initSM 5333 = initPM 5333 := hb initGoal_5333 (by decide) rfl
  have hrms := sm_pm_rms_L12_commute initSM initPM hInit hcarry5330
  rw [denote_sm_goal_3_5343, denote_sm_goal_3_5334, hrms, hw5333,
      denote_pm_goal_3_5343, denote_pm_goal_3_5334]

-- V replication: SM 5344 = PM 5344.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_vrepl_L12_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5344 =
      denoteGraph_ringAttn pm_goal_3 initPM 5344 := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5335 : initSM 5335 = initPM 5335 := hb initGoal_5335 (by decide) rfl
  have hrms := sm_pm_rms_L12_commute initSM initPM hInit hcarry5330
  rw [denote_sm_goal_3_5344, denote_sm_goal_3_5336, hrms, hw5335,
      denote_pm_goal_3_5344, denote_pm_goal_3_5336]

-- SM 5338: rank-0 zigzag maybe_shuffle of the residual carry (via multiref 8011 of 5330).
-- fw_maybe_shuffle is the identity on its data argument (AGENTS.md #24), so this
-- denote-unfold exposes the carry directly. Node index 471; multiref 5330→8007,8011 = 469.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5338 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5338 =
      fw_maybe_shuffle (denoteGraph_ringAttn sm_goal_3 initSM 5330) (initSM 5337) 1 0 :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5338 8011 5337 471
    ({ rank := 0, op := "OpName.FW_maybe_shuffle", ins := [8011, 5337], outs := [5338], params := [1, 0] })
    (fun a1 a2 => fw_maybe_shuffle a1 a2 1 0)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_maybe_shuffle_out sm_goal_3 s 0 1 0 8011 5337 5338)
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8011 5330 469
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5330], outs := [8007, 8011], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5330 8011 [8007, 8011] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5337 (by decide) (by decide))

-- `fw_rms_norm` preserves its input shape (value-independent — avoids whnf on denote).
theorem fw_rms_norm_shape_eq (x w : Tensor) : (fw_rms_norm x w).shape = x.shape := by
  unfold fw_rms_norm
  cases h : x.shape.reverse with
  | nil => simp
  | cons d ds => simp [Tensor.mkShape]

/-! ## Q full-sharding commute (Blocker B)

The Q path threads a zigzag `fw_maybe_shuffle` (SM: cpSize=1; PM r0: [2,0]; PM r1:
[2,1]), which is the identity on its data argument (AGENTS.md #24).  Below the
shuffle the path is `per_head_linear ∘ rms_norm`, both per-row along dim 0, so they
commute with the dim-0 all-gather of the CP-sharded residual.  Reuses the general
`fw_rms_norm_allGather0_commute_2` (Pattern_1) and
`fw_per_head_mix_precision_linear_allGather0_commute_2` (Denote).  The two PM-side
residual shapes and the Q-weight shape are taken as hypotheses. -/
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_qfull_L12_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626])
    (h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024])
    (h9626 : (denoteGraph_ringAttn pm_goal_3 initPM 9626).shape = [2048, 1024])
    (hw5341 : (initPM 5341).shape = [16, 64, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5342 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9659,
         denoteGraph_ringAttn pm_goal_3 initPM 9660] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5339 : initSM 5339 = initPM 5339 := hb initGoal_5339 (by decide) rfl
  have hw5341e : initSM 5341 = initPM 5341 := hb initGoal_5341 (by decide) rfl
  rw [denote_sm_goal_3_5342, denote_sm_goal_3_5340, denote_sm_goal_3_5338,
      denote_pm_goal_3_9659, denote_pm_goal_3_9657, denote_pm_goal_3_9655, denote_pm_goal_3_13257,
      denote_pm_goal_3_9660, denote_pm_goal_3_9658, denote_pm_goal_3_9656, denote_pm_goal_3_13258]
  unfold fw_maybe_shuffle
  rw [hcarry5330, hw5339, hw5341e]
  have hrms9625 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 9625) (initPM 5339)).shape = [2048, 1024] := by
    rw [fw_rms_norm_shape_eq, h9625]
  have hrms9626 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 9626) (initPM 5339)).shape = [2048, 1024] := by
    rw [fw_rms_norm_shape_eq, h9626]
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5339) 2048 1024 (by omega) (by omega) h9625 h9626,
      fw_per_head_mix_precision_linear_allGather0_commute_2 _ _ (initPM 5341) 2048 1024 16 64
        (by omega) (by omega) (by omega) (by omega) hrms9625 hrms9626 hw5341]

/-! ## L12 attention commute assembly

Compose the CP reconstruction lemma (`applyNodeRingAttn_zigzag_reconstruction_2_cp`)
with the three denote↔applyNode bridges and the `attn_zigzag_store_congr` used to
align the rank-1 buddy's folded prefix store (take 1068) to the shared reconstruction
store (take 1067). K/V replication is discharged by the commutes proven above; the
Q sharding (`hq_full`) and the incoming residual (`hcarry5330`) plus the four PM-side
attention shape facts are taken as hypotheses (each isolated to a dedicated lemma). -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_attention_L12_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626])
    (hq_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5342).shape.length)
    (hk_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5343).shape.length)
    (hv_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5344).shape.length)
    (h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024])
    (h9626 : (denoteGraph_ringAttn pm_goal_3 initPM 9626).shape = [2048, 1024])
    (hw5341 : (initPM 5341).shape = [16, 64, 1024])
    (hk_shape :
      ((pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5343).shape
        = [4096, 4, 64])
    (hv_shape :
      ((pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5344).shape
        = [4096, 4, 64])
    (h_bound : ∀ t, (decodeCuSeqlens
        ((pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5346)).getD (t+1) 0 ≤ 4096)
    (hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 9659,
           (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 9660])
        (allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5343,
           (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5343])
        (allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5344,
           (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5344])
        ((pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5345)
        ((pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5346)
        16 4 64 64 (decide ((1:Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5347
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 9687,
           denoteGraph_ringAttn pm_goal_3 initPM 9688] := by
  -- folded-store bridges for the K/V replication commutes (denote ↔ prefix fold)
  have hkrepl := sm_pm_krepl_L12_commute initSM initPM hInit hcarry5330
  have hvrepl := sm_pm_vrepl_L12_commute initSM initPM hInit hcarry5330
  -- Q full-sharding commute (Blocker B) lifted into folded-prefix form
  have hq_full :
      (sm_goal_3.nodes.take 504).foldl (applyNodeRingAttn sm_goal_3) initSM 5342 =
        allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 9659,
           (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 9660] := by
    have bq5342 : (sm_goal_3.nodes.take 504).foldl (applyNodeRingAttn sm_goal_3) initSM 5342
        = denoteGraph_ringAttn sm_goal_3 initSM 5342 :=
      (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5342 504 (by decide) (by decide)).symm
    have bq9659 : (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 9659
        = denoteGraph_ringAttn pm_goal_3 initPM 9659 :=
      (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9659 1067 (by decide) (by decide)).symm
    have bq9660 : (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 9660
        = denoteGraph_ringAttn pm_goal_3 initPM 9660 :=
      (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9660 1067 (by decide) (by decide)).symm
    rw [bq5342, bq9659, bq9660]
    exact sm_pm_qfull_L12_commute initSM initPM hInit hcarry5330 h9625 h9626 hw5341
  -- SM-side folded ↔ denote at K/V tids
  have bSM5343 : (sm_goal_3.nodes.take 504).foldl (applyNodeRingAttn sm_goal_3) initSM 5343
      = denoteGraph_ringAttn sm_goal_3 initSM 5343 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5343 504 (by decide) (by decide)).symm
  have bSM5344 : (sm_goal_3.nodes.take 504).foldl (applyNodeRingAttn sm_goal_3) initSM 5344
      = denoteGraph_ringAttn sm_goal_3 initSM 5344 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5344 504 (by decide) (by decide)).symm
  have bPM5343 : (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5343
      = denoteGraph_ringAttn pm_goal_3 initPM 5343 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5343 1067 (by decide) (by decide)).symm
  have bPM5344 : (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5344
      = denoteGraph_ringAttn pm_goal_3 initPM 5344 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5344 1067 (by decide) (by decide)).symm
  -- cu_seqlens folded = init (not written in prefix) then SM = PM via cut goals
  have hb := L12_weight_eq initSM initPM hInit
  have hS5345 : (sm_goal_3.nodes.take 504).foldl (applyNodeRingAttn sm_goal_3) initSM 5345 = initSM 5345 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 504) initSM 5345 (by decide) (by decide)
  have hS5346 : (sm_goal_3.nodes.take 504).foldl (applyNodeRingAttn sm_goal_3) initSM 5346 = initSM 5346 :=
    foldl_applyNodeRingAttn_at_not_written sm_goal_3 (sm_goal_3.nodes.take 504) initSM 5346 (by decide) (by decide)
  have hP5345 : (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5345 = initPM 5345 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1067) initPM 5345 (by decide) (by decide)
  have hP5346 : (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5346 = initPM 5346 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1067) initPM 5346 (by decide) (by decide)
  have hw5345 : initSM 5345 = initPM 5345 := hb initGoal_5345 (by decide) rfl
  have hw5346 : initSM 5346 = initPM 5346 := hb initGoal_5346 (by decide) rfl
  -- reconstruction inputs
  have hkfull : (sm_goal_3.nodes.take 504).foldl (applyNodeRingAttn sm_goal_3) initSM 5343
      = (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5343 := by
    rw [bSM5343, bPM5343, hkrepl]
  have hvfull : (sm_goal_3.nodes.take 504).foldl (applyNodeRingAttn sm_goal_3) initSM 5344
      = (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5344 := by
    rw [bSM5344, bPM5344, hvrepl]
  have hcuQ : (sm_goal_3.nodes.take 504).foldl (applyNodeRingAttn sm_goal_3) initSM 5345
      = (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5345 := by
    rw [hS5345, hP5345, hw5345]
  have hcuK : (sm_goal_3.nodes.take 504).foldl (applyNodeRingAttn sm_goal_3) initSM 5346
      = (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5346 := by
    rw [hS5346, hP5346, hw5346]
  -- align rank-1 buddy folded store (take 1068) to reconstruction store (take 1067)
  have e9659 : (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 9659
      = (pm_goal_3.nodes.take 1068).foldl (applyNodeRingAttn pm_goal_3) initPM 9659 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9659 1067 1068 (by omega) (by decide) (by decide)).symm
  have e9660 : (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 9660
      = (pm_goal_3.nodes.take 1068).foldl (applyNodeRingAttn pm_goal_3) initPM 9660 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9660 1067 1068 (by omega) (by decide) (by decide)).symm
  have e5343 : (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5343
      = (pm_goal_3.nodes.take 1068).foldl (applyNodeRingAttn pm_goal_3) initPM 5343 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5343 1067 1068 (by omega) (by decide) (by decide)).symm
  have e5344 : (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5344
      = (pm_goal_3.nodes.take 1068).foldl (applyNodeRingAttn pm_goal_3) initPM 5344 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5344 1067 1068 (by omega) (by decide) (by decide)).symm
  have e5345 : (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5345
      = (pm_goal_3.nodes.take 1068).foldl (applyNodeRingAttn pm_goal_3) initPM 5345 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5345 1067 1068 (by omega) (by decide) (by decide)).symm
  have e5346 : (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5346
      = (pm_goal_3.nodes.take 1068).foldl (applyNodeRingAttn pm_goal_3) initPM 5346 :=
    (foldl_take_split_at_not_written_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5346 1067 1068 (by omega) (by decide) (by decide)).symm
  have bridge_r1 : applyNodeRingAttn_zigzag pm_goal_3
        ((pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_12
      = applyNodeRingAttn_zigzag pm_goal_3
        ((pm_goal_3.nodes.take 1068).foldl (applyNodeRingAttn pm_goal_3) initPM) nR1_12 := by
    apply attn_zigzag_store_congr
    · rw [buddy_r1_12]; intro m hm; fin_cases hm
      · exact e9659
      · exact e9660
    · rw [buddy_r1_12]; intro m hm; fin_cases hm
      · exact e5343
      · exact e5343
    · rw [buddy_r1_12]; intro m hm; fin_cases hm
      · exact e5344
      · exact e5344
    · exact e5345
    · exact e5346
  -- shape-length hyps in folded-store form
  have bSM5342 : (sm_goal_3.nodes.take 504).foldl (applyNodeRingAttn sm_goal_3) initSM 5342
      = denoteGraph_ringAttn sm_goal_3 initSM 5342 :=
    (foldl_prefix_eq_full_ringAttn sm_goal_3 sm_goal_3.nodes initSM 5342 504 (by decide) (by decide)).symm
  have hq_sm' : 0 < ((sm_goal_3.nodes.take 504).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_12.ins.getD 0 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 504).foldl (applyNodeRingAttn sm_goal_3) initSM 5342).shape.length
    rw [bSM5342]; exact hq_sm
  have hk_sm' : 0 < ((sm_goal_3.nodes.take 504).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_12.ins.getD 1 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 504).foldl (applyNodeRingAttn sm_goal_3) initSM 5343).shape.length
    rw [bSM5343]; exact hk_sm
  have hv_sm' : 0 < ((sm_goal_3.nodes.take 504).foldl (applyNodeRingAttn sm_goal_3) initSM (nSM_12.ins.getD 2 0)).shape.length := by
    show 0 < ((sm_goal_3.nodes.take 504).foldl (applyNodeRingAttn sm_goal_3) initSM 5344).shape.length
    rw [bSM5344]; exact hv_sm
  have hrec := applyNodeRingAttn_zigzag_reconstruction_2_cp
    sm_goal_3 pm_goal_3
    ((sm_goal_3.nodes.take 504).foldl (applyNodeRingAttn sm_goal_3) initSM)
    ((pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM)
    nSM_12 nR0_12 nR1_12 2048 4096 (by omega) (by decide) (by decide) (by decide) (by decide)
    (by decide) buddy_sm_12 buddy_r0_12 buddy_r1_12 (by decide) (by decide)
    hq_sm' hk_sm' hv_sm' (by rfl) (by rfl)
    hq_full hkfull hvfull hk_shape hv_shape h_bound
    hcuQ hcuK (by rfl) (by rfl) (by rfl) (by rfl) hfull_shape
  rw [denote_sm_attn_L12_bridge, hrec, bridge_r1,
      ← denote_pm_attn_L12_r0_bridge, ← denote_pm_attn_L12_r1_bridge]

/-! ## L12 attention commute — internally discharged shape/sharding hypotheses

Wrapper over `sm_pm_attention_L12_commute` that derives, from the two
`StoreShapesHold` well-formedness facts and the cut init goals, the nine shape /
Q-sharding hypotheses.  The single remaining hypothesis `h_bound` is a genuine
well-formed-input contract on the K cu_seqlens metadata tensor (`initPM 5346`):
its decoded prefix sums must not exceed the total sequence length `4096`.  Per
AGENTS.md #29 this is kept as a statement-level hypothesis (with a vacuity
witness below), not an axiom. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_attention_L12_commute' (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5346)).getD (t+1) 0 ≤ 4096) :
    denoteGraph_ringAttn sm_goal_3 initSM 5347
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 9687,
           denoteGraph_ringAttn pm_goal_3 initPM 9688] := by
  -- carry (L11 residual) commute
  have hcarry5330 := sm_pm_carry_5330_commute initSM initPM hSM hPM hInit
  -- base PM residual shard shapes
  have h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9625 initPM hPM
  have h9626 : (denoteGraph_ringAttn pm_goal_3 initPM 9626).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9626 initPM hPM
  have hw5341 : (initPM 5341).shape = [16, 64, 1024] := hPM 5341 [16, 64, 1024] (by decide)
  -- PM Q-path shard shapes [2048,16,64]
  have h13257 : (denoteGraph_ringAttn pm_goal_3 initPM 13257).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_13257]; exact h9625
  have h9655 : (denoteGraph_ringAttn pm_goal_3 initPM 9655).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9655, fw_maybe_shuffle_shape]; exact h13257
  have h9657 : (denoteGraph_ringAttn pm_goal_3 initPM 9657).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9657, rms_sh]; exact h9655
  have h9659 : (denoteGraph_ringAttn pm_goal_3 initPM 9659).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_9659]; exact ph_lin_shape_gen _ _ 2048 16 h9657 hw5341
  have h13258 : (denoteGraph_ringAttn pm_goal_3 initPM 13258).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_13258]; exact h9626
  have h9656 : (denoteGraph_ringAttn pm_goal_3 initPM 9656).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9656, fw_maybe_shuffle_shape]; exact h13258
  have h9658 : (denoteGraph_ringAttn pm_goal_3 initPM 9658).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9658, rms_sh]; exact h9656
  have h9660 : (denoteGraph_ringAttn pm_goal_3 initPM 9660).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_9660]; exact ph_lin_shape_gen _ _ 2048 16 h9658 hw5341
  -- PM K/V full (replicated) shapes [4096,4,64]
  have h14597 : (denoteGraph_ringAttn pm_goal_3 initPM 14597).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_14597]; exact h9625
  have h11917 : (denoteGraph_ringAttn pm_goal_3 initPM 11917).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_11917]; exact aG0_2_shape _ _ 2048 1024 h14597
  have h5332 : (denoteGraph_ringAttn pm_goal_3 initPM 5332).shape = [4096, 1024] := by
    rw [denote_pm_goal_3_5332, rms_sh]; exact h11917
  have hPM5343 : (denoteGraph_ringAttn pm_goal_3 initPM 5343).shape = [4096, 4, 64] := by
    rw [denote_pm_goal_3_5343, denote_pm_goal_3_5334]
    exact ph_lin_shape_gen _ _ 4096 4 h5332 (hPM 5333 [4, 64, 1024] (by decide))
  have hPM5344 : (denoteGraph_ringAttn pm_goal_3 initPM 5344).shape = [4096, 4, 64] := by
    rw [denote_pm_goal_3_5344, denote_pm_goal_3_5336]
    exact ph_lin_shape_gen _ _ 4096 4 h5332 (hPM 5335 [4, 64, 1024] (by decide))
  -- SM Q/K/V shape-length facts (denote form)
  have hqfull := sm_pm_qfull_L12_commute initSM initPM hInit hcarry5330 h9625 h9626 hw5341
  have hkrepl := sm_pm_krepl_L12_commute initSM initPM hInit hcarry5330
  have hvrepl := sm_pm_vrepl_L12_commute initSM initPM hInit hcarry5330
  have hSMq : (denoteGraph_ringAttn sm_goal_3 initSM 5342).shape = [4096, 16, 64] := by
    rw [hqfull]
    exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h9659)
  have hq_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5342).shape.length := by
    rw [hSMq]; decide
  have hk_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5343).shape.length := by
    rw [hkrepl, hPM5343]; decide
  have hv_sm : 0 < (denoteGraph_ringAttn sm_goal_3 initSM 5344).shape.length := by
    rw [hvrepl, hPM5344]; decide
  -- folded-store bridges for K/V and cu_seqlens hyps
  have bPM5343 : (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5343
      = denoteGraph_ringAttn pm_goal_3 initPM 5343 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5343 1067 (by decide) (by decide)).symm
  have bPM5344 : (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5344
      = denoteGraph_ringAttn pm_goal_3 initPM 5344 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 5344 1067 (by decide) (by decide)).symm
  have bPM9659 : (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 9659
      = denoteGraph_ringAttn pm_goal_3 initPM 9659 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9659 1067 (by decide) (by decide)).symm
  have bPM9660 : (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 9660
      = denoteGraph_ringAttn pm_goal_3 initPM 9660 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9660 1067 (by decide) (by decide)).symm
  have hk_shape : ((pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5343).shape
      = [4096, 4, 64] := by rw [bPM5343]; exact hPM5343
  have hv_shape : ((pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5344).shape
      = [4096, 4, 64] := by rw [bPM5344]; exact hPM5344
  -- cu_seqlens bound: folded 5346 = initPM 5346 (not written in prefix)
  have hP5346 : (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5346 = initPM 5346 :=
    foldl_applyNodeRingAttn_at_not_written pm_goal_3 (pm_goal_3.nodes.take 1067) initPM 5346 (by decide) (by decide)
  have h_bound' : ∀ t, (decodeCuSeqlens
      ((pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5346)).getD (t+1) 0 ≤ 4096 := by
    intro t; rw [hP5346]; exact h_bound t
  -- full-attention output shape [2*2048,16,64]
  have hfull_shape :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 9659,
           (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 9660])
        (allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5343,
           (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5343])
        (allGatherPrimDimN 0 2 0
          [(pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5344,
           (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5344])
        ((pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5345)
        ((pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 5346)
        16 4 64 64 (decide ((1:Nat) ≠ 0)) 0).shape = [2 * 2048, 16, 64] := by
    rw [fw_attn_varlen_shape_p3]
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 9659,
         (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 9660]).shape
        = [4096, 16, 64] := by
      rw [bPM9659, bPM9660]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h9659)
    rw [hq]; rfl
  exact sm_pm_attention_L12_commute initSM initPM hInit hcarry5330
    hq_sm hk_sm hv_sm h9625 h9626 hw5341 hk_shape hv_shape h_bound' hfull_shape

/-! ## L12 post-attention residual carry: maybe_shuffle branch commute

The router-L12 residual `SM 5354 = add(8143, 5353)` has an "8143" branch that
threads the L11 carry (`SM 5330`, proven `sm_pm_carry_5330_commute`) through a
`multiref → fw_maybe_shuffle → multiref` chain.  `fw_maybe_shuffle` is the
identity on its data argument (AGENTS.md #24), and `multiref` is the gathered
input, so the whole branch is the identity on the carry and the commute reduces
to `hcarry5330`. -/
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_8143 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8143 =
      denoteGraph_ringAttn sm_goal_3 initSM 5338 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8143 5338 473
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5338], outs := [8139, 8143], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5338 8143 [8139, 8143] 2 (by decide) (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_15973 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 15973 =
      denoteGraph_ringAttn pm_goal_3 initPM 9655 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15973 9655 1001
    ({ rank := 0, op := "OpName.FW_multiref", ins := [9655], outs := [15969, 15973], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 9655 15973 [15969, 15973] 2 (by decide) (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_15981 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 15981 =
      denoteGraph_ringAttn pm_goal_3 initPM 9656 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15981 9656 1004
    ({ rank := 1, op := "OpName.FW_multiref", ins := [9656], outs := [15977, 15981], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 9656 15981 [15977, 15981] 2 (by decide) (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem sm_pm_shuffle_carry_commute (initSM initPM : Store)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626]) :
    denoteGraph_ringAttn sm_goal_3 initSM 8143 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 15973,
         denoteGraph_ringAttn pm_goal_3 initPM 15981] := by
  rw [denote_sm_goal_3_8143, denote_sm_goal_3_5338,
      denote_pm_goal_3_15973, denote_pm_goal_3_9655, denote_pm_goal_3_13257,
      denote_pm_goal_3_15981, denote_pm_goal_3_9656, denote_pm_goal_3_13258]
  unfold fw_maybe_shuffle
  exact hcarry5330

/-! ## L12 post-attention reshape→linear→view→float branch commute

The router-L12 residual `SM 5354 = add(8143, 5353)` has a "5353" branch that is
`float ∘ view ∘ mix_linear ∘ reshape ∘ reshape` on the attention output.  The two
reshapes merge `[·,16,64] → [·,1024]` (dim-0 preserved) and commute through the
dim-0 all-gather via the existing `carry_view_commute`; the linear commutes via
`fw_mix_precision_linear_allGather0_commute_2`; the closing view/float are
identity-shaped.  Reduces `SM 5353 = allGather0[PM 9713, 9714]` to the attention
commute plus the two attention-output shapes and the router weight shape. -/

-- fw_view at the tensor's own shape is the identity.
theorem fw_view_id (t : Tensor) (sh : Shape) (h : t.shape = sh) :
    fw_view sh t = t := by
  apply Tensor.ext
  · show sh = t.shape; exact h.symm
  · intro idx hidx
    rw [valAt_fw_view sh t idx (by rw [h])]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5348 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5348 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5347) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5348 5347 505
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5347], outs := [5348], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5347 5348 [4096, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5349 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5349 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5348) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5349 5348 506
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5348], outs := [5349], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5348 5349 [4096, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5351 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5351 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5349) (initSM 5350) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5351 5349 5350 507
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5349, 5350], outs := [5351] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5349 5350 5351)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5350 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5352 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5352 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5351) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5352 5351 508
    ({ rank := 0, op := "OpName.FW_view", ins := [5351], outs := [5352], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1024] 5351 5352)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5353 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5353 =
      denoteGraph_ringAttn sm_goal_3 initSM 5352 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5353 5352 509
    ({ rank := 0, op := "OpName.FW_float", ins := [5352], outs := [5353] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 5352 5353 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9689 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9689 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9687) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9689 9687 1069
    ({ rank := 0, op := "OpName.FW_reshape", ins := [9687], outs := [9689], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 9687 9689 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9695 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9695 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9689) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9695 9689 1071
    ({ rank := 0, op := "OpName.FW_reshape", ins := [9689], outs := [9695], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 9689 9695 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9699 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9699 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 9695) (initPM 5350) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9699 9695 5350 1073
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9695, 5350], outs := [9699] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 9695 5350 9699)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5350 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9709 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9709 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9699) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9709 9699 1075
    ({ rank := 0, op := "OpName.FW_view", ins := [9699], outs := [9709], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1024] 9699 9709)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9713 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9713 =
      denoteGraph_ringAttn pm_goal_3 initPM 9709 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9713 9709 1077
    ({ rank := 0, op := "OpName.FW_float", ins := [9709], outs := [9713] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 9709 9713 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9690 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9690 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9688) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9690 9688 1070
    ({ rank := 1, op := "OpName.FW_reshape", ins := [9688], outs := [9690], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 9688 9690 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9696 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9696 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9690) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9696 9690 1072
    ({ rank := 1, op := "OpName.FW_reshape", ins := [9690], outs := [9696], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 9690 9696 [2048, 1024])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9700 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9700 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 9696) (initPM 5350) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9700 9696 5350 1074
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9696, 5350], outs := [9700] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 9696 5350 9700)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5350 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9710 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9710 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9700) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9710 9700 1076
    ({ rank := 1, op := "OpName.FW_view", ins := [9700], outs := [9710], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1024] 9700 9710)
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9714 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9714 =
      denoteGraph_ringAttn pm_goal_3 initPM 9710 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9714 9710 1078
    ({ rank := 1, op := "OpName.FW_float", ins := [9710], outs := [9714] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 9710 9714 [])
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_reshape_float_5353_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hattn : denoteGraph_ringAttn sm_goal_3 initSM 5347 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9687,
         denoteGraph_ringAttn pm_goal_3 initPM 9688])
    (h9687 : (denoteGraph_ringAttn pm_goal_3 initPM 9687).shape = [2048, 16, 64])
    (h9688 : (denoteGraph_ringAttn pm_goal_3 initPM 9688).shape = [2048, 16, 64])
    (hw5350 : (initPM 5350).shape = [1024, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5353 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9713,
         denoteGraph_ringAttn pm_goal_3 initPM 9714] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw : initSM 5350 = initPM 5350 := hb initGoal_5350 (by decide) rfl
  rw [denote_sm_goal_3_5353, denote_sm_goal_3_5352, denote_sm_goal_3_5351,
      denote_sm_goal_3_5349, denote_sm_goal_3_5348,
      denote_pm_goal_3_9713, denote_pm_goal_3_9709, denote_pm_goal_3_9699,
      denote_pm_goal_3_9695, denote_pm_goal_3_9689,
      denote_pm_goal_3_9714, denote_pm_goal_3_9710, denote_pm_goal_3_9700,
      denote_pm_goal_3_9696, denote_pm_goal_3_9690]
  rw [hattn, hw]
  -- merge the two reshapes through the all-gather
  rw [carry_view_commute _ _ h9687 h9688]
  -- shapes of the view² shards
  have hva : (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9687))).shape = [2048, 1024] := rfl
  have hvb : (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9688))).shape = [2048, 1024] := rfl
  -- push the linear through the all-gather
  rw [fw_mix_precision_linear_allGather0_commute_2 _ _ (initPM 5350) 2048 1024 1024
      (by omega) (by omega) (by omega) hva hvb hw5350]
  -- linear-output shapes
  have hla : (fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9687))) (initPM 5350)).shape = [2048, 1024] := by
    rw [fw_linear_is_matmul 2048 1024 1024 _ _ hva hw5350]; rfl
  have hlb : (fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9688))) (initPM 5350)).shape = [2048, 1024] := by
    rw [fw_linear_is_matmul 2048 1024 1024 _ _ hvb hw5350]; rfl
  -- closing view is identity-shaped on both sides
  have hAG : (allGatherPrimDimN 0 2 0
      [fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9687))) (initPM 5350),
       fw_linear (fw_view [2048, 1024] (fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9688))) (initPM 5350)]).shape = [4096, 1024] := by
    rw [allGatherPrimDimN_shape 0 2 _ [2048, 1024] (by simp [hla])]; simp [List.set]
  rw [fw_view_id _ [4096, 1024] hAG, fw_view_id _ [2048, 1024] hla, fw_view_id _ [2048, 1024] hlb]

/-! ## L12 post-attention residual carry `sm_pm_carry_5354_commute`

`SM 5354 = add(8143, 5353)` combines the two proven branches (shuffle-carry and
reshape-float) via `fw_add_allGather0_commute_2_2048_1024`. -/
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5354 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5354 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 8143)
        (denoteGraph_ringAttn sm_goal_3 initSM 5353) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5354 8143 5353 510
    ({ rank := 0, op := "OpName.FW_add", ins := [8143, 5353], outs := [5354] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 8143 5353 5354)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9717 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9717 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 15973)
        (denoteGraph_ringAttn pm_goal_3 initPM 9713) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9717 15973 9713 1079
    ({ rank := 0, op := "OpName.FW_add", ins := [15973, 9713], outs := [9717] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 15973 9713 9717)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9718 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9718 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 15981)
        (denoteGraph_ringAttn pm_goal_3 initPM 9714) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9718 15981 9714 1080
    ({ rank := 1, op := "OpName.FW_add", ins := [15981, 9714], outs := [9718] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 15981 9714 9718)
    rfl rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem sm_pm_carry_5354_commute (initSM initPM : Store)
    (hshuffle : denoteGraph_ringAttn sm_goal_3 initSM 8143 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 15973,
         denoteGraph_ringAttn pm_goal_3 initPM 15981])
    (hreshape : denoteGraph_ringAttn sm_goal_3 initSM 5353 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9713,
         denoteGraph_ringAttn pm_goal_3 initPM 9714])
    (h15973 : (denoteGraph_ringAttn pm_goal_3 initPM 15973).shape = [2048, 1024])
    (h15981 : (denoteGraph_ringAttn pm_goal_3 initPM 15981).shape = [2048, 1024])
    (h9713 : (denoteGraph_ringAttn pm_goal_3 initPM 9713).shape = [2048, 1024])
    (h9714 : (denoteGraph_ringAttn pm_goal_3 initPM 9714).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5354 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9717,
         denoteGraph_ringAttn pm_goal_3 initPM 9718] := by
  rw [denote_sm_goal_3_5354, denote_pm_goal_3_9717, denote_pm_goal_3_9718]
  rw [hshuffle, hreshape]
  rw [fw_add_allGather0_commute_2_2048_1024 _ _ _ _ h15973 h15981 h9713 h9714]

/-! ## L12 router head: rms → norm_linear → topk commute (`sm_pm_router_commute_L12`)

The post-residual router head is structurally identical to the sliding-band
router (`mk_nl` / `mk_router`): `rms_norm → norm_linear → topk_routing` over the
dim-0-sharded residual, using the generic `fw_rms_norm_allGather0_commute_2`,
`fw_norm_linear_allGather0_commute_2` and `fw_topk_routing_snd_fst_allGather0_commute_2_of`.
Fed by `sm_pm_carry_5354_commute`. -/
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5356 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5356 =
      fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5354) (initSM 5355) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5356 8147 5355 512
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [8147, 5355], outs := [5356] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p sm_goal_3 s 0 8147 5355 5356)
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8147 5354 511
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5354], outs := [8147, 8151], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5354 8147 [8147, 8151] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5355 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5357 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5357 =
      denoteGraph_ringAttn sm_goal_3 initSM 5356 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5357 8158 514
    ({ rank := 0, op := "OpName.FW_float", ins := [8158], outs := [5357] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 8158 5357 [])
    (DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8158 5356 513
      ({ rank := 0, op := "OpName.FW_multiref", ins := [5356], outs := [8158, 8162, 8166, 8170, 8174], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out sm_goal_3 s 0 5356 8158 [8158, 8162, 8166, 8170, 8174] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5359 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5359 =
      fw_norm_linear (denoteGraph_ringAttn sm_goal_3 initSM 5357) (initSM 5358) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5359 5357 5358 518
    ({ rank := 0, op := "OpName.FW_norm_linear", ins := [5357, 5358], outs := [5359] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out sm_goal_3 s 0 5357 5358 5359 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5358 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5361 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5361 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3 initSM 5359) ([8].getD 0 1)
        (((denoteGraph_ringAttn sm_goal_3 initSM 5359).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5361 5359 522
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [5359], outs := [5360, 5361, 5362], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out sm_goal_3 s 0 5359 5360 5361 5362 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9721 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9721 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 9717) (initPM 5355) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9721 15985 5355 1083
    ({ rank := 0, op := "OpName.FW_rms_norm", ins := [15985, 5355], outs := [9721] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 0 15985 5355 9721)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15985 9717 1081
      ({ rank := 0, op := "OpName.FW_multiref", ins := [9717], outs := [15985, 15989], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 9717 15985 [15985, 15989] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5355 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9723 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9723 =
      denoteGraph_ringAttn pm_goal_3 initPM 9721 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9723 16004 1087
    ({ rank := 0, op := "OpName.FW_float", ins := [16004], outs := [9723] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 16004 9723 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16004 9721 1085
      ({ rank := 0, op := "OpName.FW_multiref", ins := [9721], outs := [16004, 16008, 16012, 16016, 16020], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 0 9721 16004 [16004, 16008, 16012, 16016, 16020] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9729 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9729 =
      fw_norm_linear (denoteGraph_ringAttn pm_goal_3 initPM 9723) (initPM 5358) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9729 9723 5358 1095
    ({ rank := 0, op := "OpName.FW_norm_linear", ins := [9723, 5358], outs := [9729] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out pm_goal_3 s 0 9723 5358 9729 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5358 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9733 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9733 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 9729) ([8].getD 0 1)
        (((denoteGraph_ringAttn pm_goal_3 initPM 9729).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9733 9729 1103
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [9729], outs := [9731, 9733, 9735], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out pm_goal_3 s 0 9729 9731 9733 9735 [8] (by decide))
    rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9722 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9722 =
      fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 9718) (initPM 5355) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9722 15993 5355 1084
    ({ rank := 1, op := "OpName.FW_rms_norm", ins := [15993, 5355], outs := [9722] })
    (fun a1 a2 => fw_rms_norm a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_rms_norm_out_1p pm_goal_3 s 1 15993 5355 9722)
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15993 9718 1082
      ({ rank := 1, op := "OpName.FW_multiref", ins := [9718], outs := [15993, 15997], params := [2] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 9718 15993 [15993, 15997] 2 (by decide) (by decide))
      rfl)
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5355 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9724 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9724 =
      denoteGraph_ringAttn pm_goal_3 initPM 9722 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9724 16027 1091
    ({ rank := 1, op := "OpName.FW_float", ins := [16027], outs := [9724] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 16027 9724 [])
    (DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16027 9722 1086
      ({ rank := 1, op := "OpName.FW_multiref", ins := [9722], outs := [16027, 16031, 16035, 16039, 16043], params := [5] })
      (fun a1 => a1)
      (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (fun s => applyNode_fw_multiref_out pm_goal_3 s 1 9722 16027 [16027, 16031, 16035, 16039, 16043] 5 (by decide) (by decide))
      rfl)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9730 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9730 =
      fw_norm_linear (denoteGraph_ringAttn pm_goal_3 initPM 9724) (initPM 5358) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9730 9724 5358 1099
    ({ rank := 1, op := "OpName.FW_norm_linear", ins := [9724, 5358], outs := [9730] })
    (fun a1 a2 => fw_norm_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_norm_linear_out pm_goal_3 s 1 9724 5358 9730 [])
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5358 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9734 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9734 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 9730) ([8].getD 0 1)
        (((denoteGraph_ringAttn pm_goal_3 initPM 9730).shape.reverse.head?).getD ([8].getD 1 1))).snd.fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9734 9730 1107
    ({ rank := 1, op := "OpName.FW_topk_routing", ins := [9730], outs := [9732, 9734, 9736], params := [8] })
    (fun a1 => (fw_topk_routing a1 ([8].getD 0 1) ((a1.shape.reverse.head?).getD ([8].getD 1 1))).snd.fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_map_out pm_goal_3 s 1 9730 9732 9734 9736 [8] (by decide))
    rfl

-- NL commute: SM 5359 = allGather0[PM 9729, 9730], modulo the residual carry commute.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_nl_L12_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5354 : denoteGraph_ringAttn sm_goal_3 initSM 5354 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9717,
         denoteGraph_ringAttn pm_goal_3 initPM 9718])
    (h9717 : (denoteGraph_ringAttn pm_goal_3 initPM 9717).shape = [2048, 1024])
    (h9718 : (denoteGraph_ringAttn pm_goal_3 initPM 9718).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5359 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9729,
         denoteGraph_ringAttn pm_goal_3 initPM 9730] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5355 : initSM 5355 = initPM 5355 := hb initGoal_5355 (by decide) rfl
  have hw5358 : initSM 5358 = initPM 5358 := hb initGoal_5358 (by decide) rfl
  have hw5358sh : (initPM 5358).shape = [64, 1024] := by
    have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
      fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
    have hgh := hII initGoal_5358 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5358] using hsh
  rw [denote_sm_goal_3_5359, denote_sm_goal_3_5357, denote_sm_goal_3_5356,
      denote_pm_goal_3_9729, denote_pm_goal_3_9723, denote_pm_goal_3_9721,
      denote_pm_goal_3_9730, denote_pm_goal_3_9724, denote_pm_goal_3_9722]
  rw [hw5355, hw5358, hcarry5354]
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5355) 2048 1024 (by omega) (by omega) h9717 h9718]
  have hrms9717 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 9717) (initPM 5355)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h9717
  have hrms9718 : (fw_rms_norm (denoteGraph_ringAttn pm_goal_3 initPM 9718) (initPM 5355)).shape = [2048, 1024] := by
    rw [rms_sh]; exact h9718
  rw [fw_norm_linear_allGather0_commute_2 _ _ (initPM 5358) 2048 1024 64 (by omega) (by omega) (by omega) hrms9717 hrms9718 hw5358sh]

-- Router commute: SM 5361 = allGather0[PM 9733, 9734], modulo the residual carry commute.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L12 (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5354 : denoteGraph_ringAttn sm_goal_3 initSM 5354 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9717,
         denoteGraph_ringAttn pm_goal_3 initPM 9718])
    (h9717 : (denoteGraph_ringAttn pm_goal_3 initPM 9717).shape = [2048, 1024])
    (h9718 : (denoteGraph_ringAttn pm_goal_3 initPM 9718).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5361 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9733,
         denoteGraph_ringAttn pm_goal_3 initPM 9734] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5355 : initSM 5355 = initPM 5355 := hb initGoal_5355 (by decide) rfl
  have hw5358sh : (initPM 5358).shape = [64, 1024] := by
    have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
      fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
    have hgh := hII initGoal_5358 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5358] using hsh
  have hnl := sm_pm_nl_L12_commute initSM initPM hInit hcarry5354 h9717 h9718
  -- PM nl-output shapes [2048, 64]
  have hs9729 : (denoteGraph_ringAttn pm_goal_3 initPM 9729).shape = [2048, 64] := by
    rw [denote_pm_goal_3_9729, denote_pm_goal_3_9723, denote_pm_goal_3_9721]
    exact nl_sh 2048 1024 64 _ (initPM 5358) (by rw [rms_sh]; exact h9717) hw5358sh
  have hs9730 : (denoteGraph_ringAttn pm_goal_3 initPM 9730).shape = [2048, 64] := by
    rw [denote_pm_goal_3_9730, denote_pm_goal_3_9724, denote_pm_goal_3_9722]
    exact nl_sh 2048 1024 64 _ (initPM 5358) (by rw [rms_sh]; exact h9718) hw5358sh
  have hSM5359sh : (denoteGraph_ringAttn sm_goal_3 initSM 5359).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 hs9729
  rw [denote_sm_goal_3_5361, denote_pm_goal_3_9733, denote_pm_goal_3_9734]
  rw [show (denoteGraph_ringAttn sm_goal_3 initSM 5359).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hSM5359sh]; rfl,
      show (denoteGraph_ringAttn pm_goal_3 initPM 9729).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hs9729]; rfl,
      show (denoteGraph_ringAttn pm_goal_3 initPM 9730).shape.reverse.head?.getD ([8].getD 1 1) = 64 from by rw [hs9730]; rfl]
  rw [hnl]
  exact fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 ([8].getD 0 1) 64 (by omega) (by omega) hs9729 hs9730

-- Capstone: router-L12 fully reduced to the attention commute + L11 carry + base shapes.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L12_from_attention (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hcarry5330 : denoteGraph_ringAttn sm_goal_3 initSM 5330 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9625,
         denoteGraph_ringAttn pm_goal_3 initPM 9626])
    (hattn : denoteGraph_ringAttn sm_goal_3 initSM 5347 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9687,
         denoteGraph_ringAttn pm_goal_3 initPM 9688])
    (h9687 : (denoteGraph_ringAttn pm_goal_3 initPM 9687).shape = [2048, 16, 64])
    (h9688 : (denoteGraph_ringAttn pm_goal_3 initPM 9688).shape = [2048, 16, 64])
    (h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024])
    (h9626 : (denoteGraph_ringAttn pm_goal_3 initPM 9626).shape = [2048, 1024])
    (hw5350 : (initPM 5350).shape = [1024, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5361 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9733,
         denoteGraph_ringAttn pm_goal_3 initPM 9734] := by
  have hshuffle := sm_pm_shuffle_carry_commute initSM initPM hcarry5330
  have hreshape := sm_pm_reshape_float_5353_commute initSM initPM hInit hattn h9687 h9688 hw5350
  have h15973 : (denoteGraph_ringAttn pm_goal_3 initPM 15973).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_15973, denote_pm_goal_3_9655, fw_maybe_shuffle_shape, denote_pm_goal_3_13257]
    exact h9625
  have h15981 : (denoteGraph_ringAttn pm_goal_3 initPM 15981).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_15981, denote_pm_goal_3_9656, fw_maybe_shuffle_shape, denote_pm_goal_3_13258]
    exact h9626
  have h9713 : (denoteGraph_ringAttn pm_goal_3 initPM 9713).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9713, denote_pm_goal_3_9709]; rfl
  have h9714 : (denoteGraph_ringAttn pm_goal_3 initPM 9714).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9714, denote_pm_goal_3_9710]; rfl
  have hcarry5354 := sm_pm_carry_5354_commute initSM initPM hshuffle hreshape h15973 h15981 h9713 h9714
  have h9717 : (denoteGraph_ringAttn pm_goal_3 initPM 9717).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9717]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h15973 h9713
  have h9718 : (denoteGraph_ringAttn pm_goal_3 initPM 9718).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9718]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h15981 h9714
  exact sm_pm_router_commute_L12 initSM initPM hInit hcarry5354 h9717 h9718

/-! ## L12 router — fully assembled from `StoreShapesHold` + cut init goals

Top-level per-layer commute for the L12 zigzag band.  Every attention shape /
sharding hypothesis is discharged internally from the two `StoreShapesHold`
well-formedness facts and the cut init goals.  The only remaining hypothesis is
the K cu_seqlens well-formed-input contract `h_bound` (kept as a statement-level
hypothesis per AGENTS.md #29; see `sm_pm_router_L12_hbound_witness` for its
vacuity witness). -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_router_commute_L12_full (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_bound : ∀ t, (decodeCuSeqlens (initPM 5346)).getD (t+1) 0 ≤ 4096) :
    denoteGraph_ringAttn sm_goal_3 initSM 5361 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9733,
         denoteGraph_ringAttn pm_goal_3 initPM 9734] := by
  have hcarry5330 := sm_pm_carry_5330_commute initSM initPM hSM hPM hInit
  have hattn := sm_pm_attention_L12_commute' initSM initPM hSM hPM hInit h_bound
  have h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9625 initPM hPM
  have h9626 : (denoteGraph_ringAttn pm_goal_3 initPM 9626).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9626 initPM hPM
  have hw5341 : (initPM 5341).shape = [16, 64, 1024] := hPM 5341 [16, 64, 1024] (by decide)
  have hw5350 : (initPM 5350).shape = [1024, 1024] := hPM 5350 [1024, 1024] (by decide)
  -- PM Q-path shard shapes [2048,16,64] (r0 + r1)
  have h13257 : (denoteGraph_ringAttn pm_goal_3 initPM 13257).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_13257]; exact h9625
  have h9655 : (denoteGraph_ringAttn pm_goal_3 initPM 9655).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9655, fw_maybe_shuffle_shape]; exact h13257
  have h9657 : (denoteGraph_ringAttn pm_goal_3 initPM 9657).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9657, rms_sh]; exact h9655
  have h9659d : (denoteGraph_ringAttn pm_goal_3 initPM 9659).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_9659]; exact ph_lin_shape_gen _ _ 2048 16 h9657 hw5341
  have h13258 : (denoteGraph_ringAttn pm_goal_3 initPM 13258).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_13258]; exact h9626
  have h9656 : (denoteGraph_ringAttn pm_goal_3 initPM 9656).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9656, fw_maybe_shuffle_shape]; exact h13258
  have h9658 : (denoteGraph_ringAttn pm_goal_3 initPM 9658).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9658, rms_sh]; exact h9656
  have h9660d : (denoteGraph_ringAttn pm_goal_3 initPM 9660).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_9660]; exact ph_lin_shape_gen _ _ 2048 16 h9658 hw5341
  -- folded-store ↔ denote bridges at the two attention Q tids
  have b1067_9659 : (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 9659
      = denoteGraph_ringAttn pm_goal_3 initPM 9659 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9659 1067 (by decide) (by decide)).symm
  have b1067_9660 : (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 9660
      = denoteGraph_ringAttn pm_goal_3 initPM 9660 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9660 1067 (by decide) (by decide)).symm
  have b1068_9659 : (pm_goal_3.nodes.take 1068).foldl (applyNodeRingAttn pm_goal_3) initPM 9659
      = denoteGraph_ringAttn pm_goal_3 initPM 9659 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9659 1068 (by decide) (by decide)).symm
  have b1068_9660 : (pm_goal_3.nodes.take 1068).foldl (applyNodeRingAttn pm_goal_3) initPM 9660
      = denoteGraph_ringAttn pm_goal_3 initPM 9660 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9660 1068 (by decide) (by decide)).symm
  -- PM attention output shapes [2048,16,64] (chunk of the full [4096,16,64])
  have h9687 : (denoteGraph_ringAttn pm_goal_3 initPM 9687).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L12_r0_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR0_12 nR0_12 nR1_12 0 buddy_r0_12 (by decide)]
    have e0 : nR0_12.ins.getD 0 0 = 9659 := by decide
    have e1 : nR1_12.ins.getD 0 0 = 9660 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_12.ins.getD 0 0),
         (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_12.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1067_9659, b1067_9660]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h9659d)
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  have h9688 : (denoteGraph_ringAttn pm_goal_3 initPM 9688).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L12_r1_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR1_12 nR0_12 nR1_12 1 buddy_r1_12 (by decide)]
    have e0 : nR0_12.ins.getD 0 0 = 9659 := by decide
    have e1 : nR1_12.ins.getD 0 0 = 9660 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1068).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_12.ins.getD 0 0),
         (pm_goal_3.nodes.take 1068).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_12.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1068_9659, b1068_9660]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h9659d)
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  exact sm_pm_router_commute_L12_from_attention initSM initPM hInit hcarry5330
    hattn h9687 h9688 h9625 h9626 hw5350

/-! ## L12 MoE sublayer denote bridges (generated modular single-step) -/

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_8151 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8151 =
      denoteGraph_ringAttn sm_goal_3 initSM 5354 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8151 5354 511
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5354], outs := [8147, 8151], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out sm_goal_3 s 0 5354 8147 8151 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_8162 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8162 =
      denoteGraph_ringAttn sm_goal_3 initSM 5356 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8162 5356 513
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5356], outs := [8158, 8162, 8166, 8170, 8174], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out sm_goal_3 s 0 5356 8158 8162 8166 8170 8174 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_8166 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8166 =
      denoteGraph_ringAttn sm_goal_3 initSM 5356 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8166 5356 513
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5356], outs := [8158, 8162, 8166, 8170, 8174], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out sm_goal_3 s 0 5356 8158 8162 8166 8170 8174 (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_8170 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8170 =
      denoteGraph_ringAttn sm_goal_3 initSM 5356 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8170 5356 513
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5356], outs := [8158, 8162, 8166, 8170, 8174], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out sm_goal_3 s 0 5356 8158 8162 8166 8170 8174 (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_8174 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 8174 =
      denoteGraph_ringAttn sm_goal_3 initSM 5356 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 8174 5356 513
    ({ rank := 0, op := "OpName.FW_multiref", ins := [5356], outs := [8158, 8162, 8166, 8170, 8174], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out sm_goal_3 s 0 5356 8158 8162 8166 8170 8174 (by decide) (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5360 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5360 =
      (fw_topk_routing (denoteGraph_ringAttn sm_goal_3 initSM 5359) 8
        ((((denoteGraph_ringAttn sm_goal_3 initSM 5359).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5360 5359 522
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [5359], outs := [5360, 5361, 5362], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out sm_goal_3 s 0 5359 5360 5361 5362 [8])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5366 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5366 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8166) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5366 8166 515
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8166], outs := [5366], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8166 5366 [4096, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5371 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5371 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8170) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5371 8170 516
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8170], outs := [5371], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8170 5371 [4096, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5375 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5375 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 8174) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5375 8174 517
    ({ rank := 0, op := "OpName.FW_reshape", ins := [8174], outs := [5375], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 8174 5375 [4096, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5368 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5368 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5366) (initSM 5367) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5368 5366 5367 519
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5366, 5367], outs := [5368] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5366 5367 5368)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5367 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5373 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5373 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5371) (initSM 5372) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5373 5371 5372 520
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5371, 5372], outs := [5373] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5371 5372 5373)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5372 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5377 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5377 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5375) (initSM 5376) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5377 5375 5376 521
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5375, 5376], outs := [5377] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5375 5376 5377)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5376 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5369 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5369 =
      fw_view [4096, 1] (denoteGraph_ringAttn sm_goal_3 initSM 5368) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5369 5368 523
    ({ rank := 0, op := "OpName.FW_view", ins := [5368], outs := [5369], params := [4096, 1] })
    (fun a1 => fw_view [4096, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1] 5368 5369)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5374 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5374 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5373) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5374 5373 524
    ({ rank := 0, op := "OpName.FW_view", ins := [5373], outs := [5374], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [512] 5373 5374)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5378 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5378 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5377) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5378 5377 525
    ({ rank := 0, op := "OpName.FW_view", ins := [5377], outs := [5378], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [512] 5377 5378)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5370 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5370 =
      fw_sigmoid (denoteGraph_ringAttn sm_goal_3 initSM 5369) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5370 5369 527
    ({ rank := 0, op := "OpName.FW_sigmoid", ins := [5369], outs := [5370] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p sm_goal_3 s 0 5369 5370])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5379 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5379 =
      fw_swiglu (denoteGraph_ringAttn sm_goal_3 initSM 5374) (denoteGraph_ringAttn sm_goal_3 initSM 5378) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5379 5374 5378 528
    ({ rank := 0, op := "OpName.FW_swiglu", ins := [5374, 5378], outs := [5379] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p sm_goal_3 s 0 5374 5378 5379])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5380 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5380 =
      fw_view [4096, 512] (denoteGraph_ringAttn sm_goal_3 initSM 5379) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5380 5379 529
    ({ rank := 0, op := "OpName.FW_reshape", ins := [5379], outs := [5380], params := [4096, 512] })
    (fun a1 => fw_view [4096, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out sm_goal_3 s 0 5379 5380 [4096, 512])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5382 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5382 =
      fw_linear (denoteGraph_ringAttn sm_goal_3 initSM 5380) (initSM 5381) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5382 5380 5381 530
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5380, 5381], outs := [5382] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p sm_goal_3 s 0 5380 5381 5382)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5381 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5383 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5383 =
      fw_view [4096, 1024] (denoteGraph_ringAttn sm_goal_3 initSM 5382) :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5383 5382 531
    ({ rank := 0, op := "OpName.FW_view", ins := [5382], outs := [5383], params := [4096, 1024] })
    (fun a1 => fw_view [4096, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out sm_goal_3 s 0 4096 [1024] 5382 5383)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5384 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5384 =
      elemwiseMul (denoteGraph_ringAttn sm_goal_3 initSM 5370) (denoteGraph_ringAttn sm_goal_3 initSM 5383) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5384 5370 5383 532
    ({ rank := 0, op := "OpName.FW_mul", ins := [5370, 5383], outs := [5384] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out sm_goal_3 s 0 5370 5383 5384])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5385 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5385 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 5365) (denoteGraph_ringAttn sm_goal_3 initSM 5384) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5385 5365 5384 533
    ({ rank := 0, op := "OpName.FW_add", ins := [5365, 5384], outs := [5385] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 5365 5384 5385)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5386 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5386 =
      denoteGraph_ringAttn sm_goal_3 initSM 5385 :=
  DenoteUnfoldGeneric.dstep1 sm_goal_3 initSM 5386 5385 534
    ({ rank := 0, op := "OpName.FW_float", ins := [5385], outs := [5386] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out sm_goal_3 s 0 5385 5386 [])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5387 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5387 =
      elemwiseAdd (denoteGraph_ringAttn sm_goal_3 initSM 8151) (denoteGraph_ringAttn sm_goal_3 initSM 5386) :=
  DenoteUnfoldGeneric.dstep2 sm_goal_3 initSM 5387 8151 5386 535
    ({ rank := 0, op := "OpName.FW_add", ins := [8151, 5386], outs := [5387] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out sm_goal_3 s 0 8151 5386 5387)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_15989 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 15989 =
      denoteGraph_ringAttn pm_goal_3 initPM 9717 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15989 9717 1081
    ({ rank := 0, op := "OpName.FW_multiref", ins := [9717], outs := [15985, 15989], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out pm_goal_3 s 0 9717 15985 15989 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_15997 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 15997 =
      denoteGraph_ringAttn pm_goal_3 initPM 9718 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 15997 9718 1082
    ({ rank := 1, op := "OpName.FW_multiref", ins := [9718], outs := [15993, 15997], params := [2] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => RouterShapesHelpers.applyNode_fw_multiref2_second_out pm_goal_3 s 1 9718 15993 15997 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16008 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16008 =
      denoteGraph_ringAttn pm_goal_3 initPM 9721 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16008 9721 1085
    ({ rank := 0, op := "OpName.FW_multiref", ins := [9721], outs := [16004, 16008, 16012, 16016, 16020], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out pm_goal_3 s 0 9721 16004 16008 16012 16016 16020 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16012 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16012 =
      denoteGraph_ringAttn pm_goal_3 initPM 9721 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16012 9721 1085
    ({ rank := 0, op := "OpName.FW_multiref", ins := [9721], outs := [16004, 16008, 16012, 16016, 16020], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out pm_goal_3 s 0 9721 16004 16008 16012 16016 16020 (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16016 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16016 =
      denoteGraph_ringAttn pm_goal_3 initPM 9721 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16016 9721 1085
    ({ rank := 0, op := "OpName.FW_multiref", ins := [9721], outs := [16004, 16008, 16012, 16016, 16020], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out pm_goal_3 s 0 9721 16004 16008 16012 16016 16020 (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16020 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16020 =
      denoteGraph_ringAttn pm_goal_3 initPM 9721 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16020 9721 1085
    ({ rank := 0, op := "OpName.FW_multiref", ins := [9721], outs := [16004, 16008, 16012, 16016, 16020], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out pm_goal_3 s 0 9721 16004 16008 16012 16016 16020 (by decide) (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16031 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16031 =
      denoteGraph_ringAttn pm_goal_3 initPM 9722 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16031 9722 1086
    ({ rank := 1, op := "OpName.FW_multiref", ins := [9722], outs := [16027, 16031, 16035, 16039, 16043], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos1_out pm_goal_3 s 1 9722 16027 16031 16035 16039 16043 (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16035 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16035 =
      denoteGraph_ringAttn pm_goal_3 initPM 9722 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16035 9722 1086
    ({ rank := 1, op := "OpName.FW_multiref", ins := [9722], outs := [16027, 16031, 16035, 16039, 16043], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos2_out pm_goal_3 s 1 9722 16027 16031 16035 16039 16043 (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16039 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16039 =
      denoteGraph_ringAttn pm_goal_3 initPM 9722 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16039 9722 1086
    ({ rank := 1, op := "OpName.FW_multiref", ins := [9722], outs := [16027, 16031, 16035, 16039, 16043], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos3_out pm_goal_3 s 1 9722 16027 16031 16035 16039 16043 (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_16043 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 16043 =
      denoteGraph_ringAttn pm_goal_3 initPM 9722 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 16043 9722 1086
    ({ rank := 1, op := "OpName.FW_multiref", ins := [9722], outs := [16027, 16031, 16035, 16039, 16043], params := [5] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_multiref5_at_pos4_out pm_goal_3 s 1 9722 16027 16031 16035 16039 16043 (by decide) (by decide) (by decide) (by decide))
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9731 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9731 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 9729) 8
        ((((denoteGraph_ringAttn pm_goal_3 initPM 9729).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9731 9729 1103
    ({ rank := 0, op := "OpName.FW_topk_routing", ins := [9729], outs := [9731, 9733, 9735], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out pm_goal_3 s 0 9729 9731 9733 9735 [8])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9732 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9732 =
      (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 9730) 8
        ((((denoteGraph_ringAttn pm_goal_3 initPM 9730).shape.reverse.head?).getD 1))).fst :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9732 9730 1107
    ({ rank := 1, op := "OpName.FW_topk_routing", ins := [9730], outs := [9732, 9734, 9736], params := [8] })
    (fun a1 => (fw_topk_routing a1 8 (((a1.shape.reverse.head?).getD 1))).fst)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_topk_routing_probs_out pm_goal_3 s 1 9730 9732 9734 9736 [8])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9743 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9743 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16012) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9743 16012 1088
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16012], outs := [9743], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16012 9743 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9744 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9744 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16035) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9744 16035 1092
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16035], outs := [9744], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16035 9744 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9757 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9757 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16016) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9757 16016 1089
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16016], outs := [9757], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16016 9757 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9758 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9758 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16039) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9758 16039 1093
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16039], outs := [9758], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16039 9758 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9775 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9775 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16020) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9775 16020 1090
    ({ rank := 0, op := "OpName.FW_reshape", ins := [16020], outs := [9775], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 16020 9775 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9776 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9776 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 16043) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9776 16043 1094
    ({ rank := 1, op := "OpName.FW_reshape", ins := [16043], outs := [9776], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 16043 9776 [2048, 1024])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9747 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9747 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 9743) (initPM 5367) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9747 9743 5367 1096
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9743, 5367], outs := [9747] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 9743 5367 9747)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5367 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9748 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9748 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 9744) (initPM 5367) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9748 9744 5367 1100
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9744, 5367], outs := [9748] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 9744 5367 9748)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5367 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9761 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9761 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 9757) (initPM 5372) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9761 9757 5372 1097
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9757, 5372], outs := [9761] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 9757 5372 9761)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5372 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9762 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9762 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 9758) (initPM 5372) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9762 9758 5372 1101
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9758, 5372], outs := [9762] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 9758 5372 9762)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5372 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9779 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9779 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 9775) (initPM 5376) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9779 9775 5376 1098
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9775, 5376], outs := [9779] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 9775 5376 9779)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5376 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9780 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9780 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 9776) (initPM 5376) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9780 9776 5376 1102
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9776, 5376], outs := [9780] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 9776 5376 9780)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5376 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9753 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9753 =
      fw_view [2048, 1] (denoteGraph_ringAttn pm_goal_3 initPM 9747) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9753 9747 1104
    ({ rank := 0, op := "OpName.FW_view", ins := [9747], outs := [9753], params := [2048, 1] })
    (fun a1 => fw_view [2048, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1] 9747 9753)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9754 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9754 =
      fw_view [2048, 1] (denoteGraph_ringAttn pm_goal_3 initPM 9748) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9754 9748 1108
    ({ rank := 1, op := "OpName.FW_view", ins := [9748], outs := [9754], params := [2048, 1] })
    (fun a1 => fw_view [2048, 1] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1] 9748 9754)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9771 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9771 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 9761) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9771 9761 1105
    ({ rank := 0, op := "OpName.FW_view", ins := [9761], outs := [9771], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [512] 9761 9771)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9772 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9772 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 9762) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9772 9762 1109
    ({ rank := 1, op := "OpName.FW_view", ins := [9762], outs := [9772], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [512] 9762 9772)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9789 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9789 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 9779) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9789 9779 1106
    ({ rank := 0, op := "OpName.FW_view", ins := [9779], outs := [9789], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [512] 9779 9789)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9790 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9790 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 9780) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9790 9780 1110
    ({ rank := 1, op := "OpName.FW_view", ins := [9780], outs := [9790], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [512] 9780 9790)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9755 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9755 =
      fw_sigmoid (denoteGraph_ringAttn pm_goal_3 initPM 9753) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9755 9753 1112
    ({ rank := 0, op := "OpName.FW_sigmoid", ins := [9753], outs := [9755] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p pm_goal_3 s 0 9753 9755])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9756 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9756 =
      fw_sigmoid (denoteGraph_ringAttn pm_goal_3 initPM 9754) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9756 9754 1115
    ({ rank := 1, op := "OpName.FW_sigmoid", ins := [9754], outs := [9756] })
    (fun a1 => fw_sigmoid a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_sigmoid_out_1p pm_goal_3 s 1 9754 9756])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9793 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9793 =
      fw_swiglu (denoteGraph_ringAttn pm_goal_3 initPM 9771) (denoteGraph_ringAttn pm_goal_3 initPM 9789) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9793 9771 9789 1113
    ({ rank := 0, op := "OpName.FW_swiglu", ins := [9771, 9789], outs := [9793] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p pm_goal_3 s 0 9771 9789 9793])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9794 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9794 =
      fw_swiglu (denoteGraph_ringAttn pm_goal_3 initPM 9772) (denoteGraph_ringAttn pm_goal_3 initPM 9790) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9794 9772 9790 1116
    ({ rank := 1, op := "OpName.FW_swiglu", ins := [9772, 9790], outs := [9794] })
    (fun a1 a2 => fw_swiglu a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_swiglu_out_1p pm_goal_3 s 1 9772 9790 9794])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9795 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9795 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 9793) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9795 9793 1117
    ({ rank := 0, op := "OpName.FW_reshape", ins := [9793], outs := [9795], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 0 9793 9795 [2048, 512])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9796 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9796 =
      fw_view [2048, 512] (denoteGraph_ringAttn pm_goal_3 initPM 9794) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9796 9794 1118
    ({ rank := 1, op := "OpName.FW_reshape", ins := [9794], outs := [9796], params := [2048, 512] })
    (fun a1 => fw_view [2048, 512] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_reshape_out pm_goal_3 s 1 9794 9796 [2048, 512])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9801 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9801 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 9795) (initPM 5381) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9801 9795 5381 1119
    ({ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9795, 5381], outs := [9801] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 0 9795 5381 9801)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5381 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9802 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9802 =
      fw_linear (denoteGraph_ringAttn pm_goal_3 initPM 9796) (initPM 5381) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9802 9796 5381 1120
    ({ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9796, 5381], outs := [9802] })
    (fun a1 a2 => fw_linear a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_mix_precision_linear_out_1p pm_goal_3 s 1 9796 5381 9802)
    rfl
    (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 5381 (by decide) (by decide))


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9811 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9811 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9801) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9811 9801 1121
    ({ rank := 0, op := "OpName.FW_view", ins := [9801], outs := [9811], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 0 2048 [1024] 9801 9811)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9812 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9812 =
      fw_view [2048, 1024] (denoteGraph_ringAttn pm_goal_3 initPM 9802) :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9812 9802 1122
    ({ rank := 1, op := "OpName.FW_view", ins := [9802], outs := [9812], params := [2048, 1024] })
    (fun a1 => fw_view [2048, 1024] a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_view_out pm_goal_3 s 1 2048 [1024] 9802 9812)
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9815 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9815 =
      elemwiseMul (denoteGraph_ringAttn pm_goal_3 initPM 9755) (denoteGraph_ringAttn pm_goal_3 initPM 9811) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9815 9755 9811 1123
    ({ rank := 0, op := "OpName.FW_mul", ins := [9755, 9811], outs := [9815] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out pm_goal_3 s 0 9755 9811 9815])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9816 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9816 =
      elemwiseMul (denoteGraph_ringAttn pm_goal_3 initPM 9756) (denoteGraph_ringAttn pm_goal_3 initPM 9812) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9816 9756 9812 1124
    ({ rank := 1, op := "OpName.FW_mul", ins := [9756, 9812], outs := [9816] })
    (fun a1 a2 => elemwiseMul a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => by rw [applyNode_fw_mul_out pm_goal_3 s 1 9756 9812 9816])
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9819 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9819 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 9741) (denoteGraph_ringAttn pm_goal_3 initPM 9815) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9819 9741 9815 1125
    ({ rank := 0, op := "OpName.FW_add", ins := [9741, 9815], outs := [9819] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 9741 9815 9819)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9820 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9820 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 9742) (denoteGraph_ringAttn pm_goal_3 initPM 9816) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9820 9742 9816 1126
    ({ rank := 1, op := "OpName.FW_add", ins := [9742, 9816], outs := [9820] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 9742 9816 9820)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9825 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9825 =
      denoteGraph_ringAttn pm_goal_3 initPM 9819 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9825 9819 1127
    ({ rank := 0, op := "OpName.FW_float", ins := [9819], outs := [9825] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 0 9819 9825 [])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9826 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9826 =
      denoteGraph_ringAttn pm_goal_3 initPM 9820 :=
  DenoteUnfoldGeneric.dstep1 pm_goal_3 initPM 9826 9820 1128
    ({ rank := 1, op := "OpName.FW_float", ins := [9820], outs := [9826] })
    (fun a1 => a1)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_float_out pm_goal_3 s 1 9820 9826 [])
    rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9829 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9829 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 15989) (denoteGraph_ringAttn pm_goal_3 initPM 9825) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9829 15989 9825 1129
    ({ rank := 0, op := "OpName.FW_add", ins := [15989, 9825], outs := [9829] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 0 15989 9825 9829)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9830 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9830 =
      elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 15997) (denoteGraph_ringAttn pm_goal_3 initPM 9826) :=
  DenoteUnfoldGeneric.dstep2 pm_goal_3 initPM 9830 15997 9826 1130
    ({ rank := 1, op := "OpName.FW_add", ins := [15997, 9826], outs := [9830] })
    (fun a1 a2 => elemwiseAdd a1 a2)
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_add2_out pm_goal_3 s 1 15997 9826 9830)
    rfl rfl


set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_sm_goal_3_5365 (initSM : Store) :
    denoteGraph_ringAttn sm_goal_3 initSM 5365 =
      fw_all2all_moe_gmm
        (denoteGraph_ringAttn sm_goal_3 initSM 8162)
        (denoteGraph_ringAttn sm_goal_3 initSM 5360)
        (denoteGraph_ringAttn sm_goal_3 initSM 5361)
        (initSM 5363) (initSM 5364) 64 0 64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep5 sm_goal_3 initSM 5365 8162 5360 5361 5363 5364 526
    ({ rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8162, 5360, 5361, 5363, 5364], outs := [5365], params := [64, 0, 64, 8] })
    (fun a1 a2 a3 a4 a5 => fw_all2all_moe_gmm
        (a1)
        (a2)
        (a3)
        (a4) (a5) 64 0 64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_out_1p sm_goal_3 s 0 8162 5360 5361 5363 5364 5365 [64, 0, 64, 8])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5363 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val sm_goal_3 initSM 5364 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9741 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9741 =
      fw_all2all_moe_gmm_full
        (denoteGraph_ringAttn pm_goal_3 initPM 16008)
        (denoteGraph_ringAttn pm_goal_3 initPM 9731)
        (denoteGraph_ringAttn pm_goal_3 initPM 9733)
        [initPM 9737, initPM 9738] [initPM 9739, initPM 9740]
        64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep7 pm_goal_3 initPM 9741 16008 9731 9733 9737 9738 9739 9740 1111
    ({ rank := 0, op := "OpName.FW_all2all_moe_gmm_full", ins := [16008, 9731, 9733, 9737, 9738, 9739, 9740], outs := [9741], params := [64, 8, 10] })
    (fun a1 a2 a3 a4 a5 a6 a7 => fw_all2all_moe_gmm_full
        (a1)
        (a2)
        (a3)
        [a4, a5] [a6, a7]
        64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_3 s 0 16008 9731 9733 9737 9738 9739 9740 9741 [64, 8, 10])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 9737 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 9738 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 9739 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 9740 (by decide) (by decide))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem denote_pm_goal_3_9742 (initPM : Store) :
    denoteGraph_ringAttn pm_goal_3 initPM 9742 =
      fw_all2all_moe_gmm_full
        (denoteGraph_ringAttn pm_goal_3 initPM 16031)
        (denoteGraph_ringAttn pm_goal_3 initPM 9732)
        (denoteGraph_ringAttn pm_goal_3 initPM 9734)
        [initPM 9737, initPM 9738] [initPM 9739, initPM 9740]
        64 8 ((((10 : Nat) : Scalar))) :=
  DenoteUnfoldGeneric.dstep7 pm_goal_3 initPM 9742 16031 9732 9734 9737 9738 9739 9740 1114
    ({ rank := 1, op := "OpName.FW_all2all_moe_gmm_full", ins := [16031, 9732, 9734, 9737, 9738, 9739, 9740], outs := [9742], params := [64, 8, 10] })
    (fun a1 a2 a3 a4 a5 a6 a7 => fw_all2all_moe_gmm_full
        (a1)
        (a2)
        (a3)
        [a4, a5] [a6, a7]
        64 8 ((((10 : Nat) : Scalar))))
    (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun s => applyNode_fw_all2all_moe_gmm_full_out_1p_r2 pm_goal_3 s 1 16031 9732 9734 9737 9738 9739 9740 9742 [64, 8, 10])
    rfl rfl rfl (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 9737 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 9738 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 9739 (by decide) (by decide)) (DenoteUnfoldGeneric.denote_leaf_val pm_goal_3 initPM 9740 (by decide) (by decide))


-- L12 MoE gmm sublayer commute: SM 5365 = allGather0[PM 9741, 9742].
-- Adapted from the `mk_moe_gmm` macro template (Pattern_3.lean:11911) with the L12
-- (spike-layer) tid map and modular single-step SM denote bridges.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_moe_gmm_L12_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3InitEnv)
    (hcarry5354 : denoteGraph_ringAttn sm_goal_3 initSM 5354 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9717,
         denoteGraph_ringAttn pm_goal_3 initPM 9718])
    (h9717 : (denoteGraph_ringAttn pm_goal_3 initPM 9717).shape = [2048, 1024])
    (h9718 : (denoteGraph_ringAttn pm_goal_3 initPM 9718).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5365 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9741,
         denoteGraph_ringAttn pm_goal_3 initPM 9742] := by
  have hII : InitGoalsHold pm_goal_3.numRanks initGoals initSM initPM :=
    fun g hg => hInit g (by unfold goal_3_cut_initGoals; exact List.mem_append_left _ hg)
  have hb := L12_weight_eq initSM initPM hInit
  have hw5355 : initSM 5355 = initPM 5355 := hb initGoal_5355 (by decide) rfl
  have hw5358sh : (initPM 5358).shape = [64, 1024] := by
    have hgh := hII initGoal_5358 (by decide)
    unfold InitGoalHolds at hgh
    obtain ⟨_, hsh, _⟩ := hgh
    simpa [initGoal_5358] using hsh
  -- dual-sharded MoE weights: initSM tid = allGather of the two PM shard tids
  have h5363 : initSM 5363 = allGatherPrimDimN 0 2 0 [initPM 9737, initPM 9738] := by
    have hg := hII initGoal_5363 (by decide)
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simp only [initGoal_5363, List.map] at hval
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm_goal_3.numRanks 0 (initPM 9737) (initPM 9738) []
        (by rw [h_ss_pm 9737 [32,1024,1024] (by decide)]; decide)] at hval
    rw [show pm_goal_3.numRanks = 2 from rfl] at hval
    exact hval
  have h5364 : initSM 5364 = allGatherPrimDimN 0 2 0 [initPM 9739, initPM 9740] := by
    have hg := hII initGoal_5364 (by decide)
    unfold InitGoalHolds at hg
    obtain ⟨_, _, hval⟩ := hg
    simp only [initGoal_5364, List.map] at hval
    rw [reconstructWithDim_cons_cons_nonscalar 0 pm_goal_3.numRanks 0 (initPM 9739) (initPM 9740) []
        (by rw [h_ss_pm 9739 [32,1024,512] (by decide)]; decide)] at hval
    rw [show pm_goal_3.numRanks = 2 from rfl] at hval
    exact hval
  have hnl := sm_pm_nl_L12_commute initSM initPM hInit hcarry5354 h9717 h9718
  have hrouter := sm_pm_router_commute_L12 initSM initPM hInit hcarry5354 h9717 h9718
  -- PM rms output shapes [2048, 1024]
  have h9721sh : (denoteGraph_ringAttn pm_goal_3 initPM 9721).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9721, rms_sh]; exact h9717
  have h9722sh : (denoteGraph_ringAttn pm_goal_3 initPM 9722).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9722, rms_sh]; exact h9718
  -- PM nl output shapes [2048, 64]
  have h9729sh : (denoteGraph_ringAttn pm_goal_3 initPM 9729).shape = [2048, 64] := by
    rw [denote_pm_goal_3_9729, denote_pm_goal_3_9723, denote_pm_goal_3_9721]
    exact nl_sh 2048 1024 64 _ (initPM 5358) (by rw [rms_sh]; exact h9717) hw5358sh
  have h9730sh : (denoteGraph_ringAttn pm_goal_3 initPM 9730).shape = [2048, 64] := by
    rw [denote_pm_goal_3_9730, denote_pm_goal_3_9724, denote_pm_goal_3_9722]
    exact nl_sh 2048 1024 64 _ (initPM 5358) (by rw [rms_sh]; exact h9718) hw5358sh
  have hSM5359sh : (denoteGraph_ringAttn sm_goal_3 initSM 5359).shape = [4096, 64] := by
    rw [hnl]; exact aG0_2_shape _ _ 2048 64 h9729sh
  -- MoE weight shapes
  have hw9737 : (initPM 9737).shape = [32,1024,1024] := h_ss_pm 9737 [32,1024,1024] (by decide)
  have hw9738 : (initPM 9738).shape = [32,1024,1024] := h_ss_pm 9738 [32,1024,1024] (by decide)
  have hw9739 : (initPM 9739).shape = [32,1024,512] := h_ss_pm 9739 [32,1024,512] (by decide)
  have hw9740 : (initPM 9740).shape = [32,1024,512] := h_ss_pm 9740 [32,1024,512] (by decide)
  -- canonical topk-fst forms for the two routing-probs outputs
  have h9731canon : denoteGraph_ringAttn pm_goal_3 initPM 9731
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 9729) 8 64).fst := by
    rw [denote_pm_goal_3_9731,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 9729).shape.reverse.head?).getD 1 = 64 from by rw [h9729sh]; rfl]
  have h9732canon : denoteGraph_ringAttn pm_goal_3 initPM 9732
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 9730) 8 64).fst := by
    rw [denote_pm_goal_3_9732,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 9730).shape.reverse.head?).getD 1 = 64 from by rw [h9730sh]; rfl]
  -- topk-fst / topk-snd_fst output shapes [2048, 64]
  have h9731sh : (denoteGraph_ringAttn pm_goal_3 initPM 9731).shape = [2048, 64] := by
    rw [h9731canon]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h9729sh]; rfl)
  have h9732sh : (denoteGraph_ringAttn pm_goal_3 initPM 9732).shape = [2048, 64] := by
    rw [h9732canon]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [h9730sh]; rfl)
  have h9733canon : denoteGraph_ringAttn pm_goal_3 initPM 9733
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 9729) ([8].getD 0 1) 64).snd.fst := by
    rw [denote_pm_goal_3_9733,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 9729).shape.reverse.head?).getD ([8].getD 1 1) = 64 from by rw [h9729sh]; rfl]
  have h9734canon : denoteGraph_ringAttn pm_goal_3 initPM 9734
      = (fw_topk_routing (denoteGraph_ringAttn pm_goal_3 initPM 9730) ([8].getD 0 1) 64).snd.fst := by
    rw [denote_pm_goal_3_9734,
        show ((denoteGraph_ringAttn pm_goal_3 initPM 9730).shape.reverse.head?).getD ([8].getD 1 1) = 64 from by rw [h9730sh]; rfl]
  have h9733sh : (denoteGraph_ringAttn pm_goal_3 initPM 9733).shape = [2048, 64] := by
    rw [h9733canon]; exact topk_sf_sh _ 2048 ([8].getD 0 1) 64 h9729sh
  have h9734sh : (denoteGraph_ringAttn pm_goal_3 initPM 9734).shape = [2048, 64] := by
    rw [h9734canon]; exact topk_sf_sh _ 2048 ([8].getD 0 1) 64 h9730sh
  -- split-commute key: gmm_full on gathered inputs = allGather of per-rank gmm_full
  have key := fw_all2all_moe_gmm_full_split_commute_2
    (denoteGraph_ringAttn pm_goal_3 initPM 9721) (denoteGraph_ringAttn pm_goal_3 initPM 9722)
    (denoteGraph_ringAttn pm_goal_3 initPM 9731) (denoteGraph_ringAttn pm_goal_3 initPM 9732)
    (denoteGraph_ringAttn pm_goal_3 initPM 9733) (denoteGraph_ringAttn pm_goal_3 initPM 9734)
    (initPM 9737) (initPM 9738) (initPM 9739) (initPM 9740)
    2048 1024 32 8 1024 512 ((((10 : Nat) : Scalar)))
    (by omega) (by omega) (by omega) (by omega) (by omega) rfl
    h9721sh h9722sh h9731sh h9732sh h9733sh h9734sh hw9737 hw9738 hw9739 hw9740
  -- Rewrite RHS via denote unfolds + key
  rw [denote_pm_goal_3_9741, denote_pm_goal_3_9742, denote_pm_goal_3_16008, denote_pm_goal_3_16031,
      ← key]
  -- Transform LHS: unfold SM gmm and its routing inputs
  rw [denote_sm_goal_3_5365, denote_sm_goal_3_8162, denote_sm_goal_3_5356, denote_sm_goal_3_5360]
  rw [hrouter, h5363, h5364]
  -- normalize SM topk-fst k
  rw [show ((denoteGraph_ringAttn sm_goal_3 initSM 5359).shape.reverse.head?).getD 1 = 64 from by rw [hSM5359sh]; rfl]
  rw [hw5355, hcarry5354, hnl]
  -- rms commute, fold to PM rms denote form
  rw [fw_rms_norm_allGather0_commute_2 _ _ (initPM 5355) 2048 1024 (by omega) (by omega) h9717 h9718]
  rw [← denote_pm_goal_3_9721, ← denote_pm_goal_3_9722]
  -- topk-fst commute, fold to PM topk-fst denote form
  rw [fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) h9729sh h9730sh]
  rw [← h9731canon, ← h9732canon]
  unfold fw_all2all_moe_gmm_full
  rfl

-- L12 MoE gate·expert product commute: SM 5384 = allGather0[PM 9815, 9816].
-- Adapted from the `mk_gate_mul` macro template (Pattern_3.lean:12523) with the L12
-- tid map and modular single-step SM/PM denote bridges (which are expanded explicitly
-- since they are not monolithic like the L2..L10 layers').
set_option maxRecDepth 20000 in
set_option maxHeartbeats 40000000 in
theorem sm_pm_gate_mul_L12_commute (initSM initPM : Store)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (h_ss_pm : StoreShapesHold initPM pm_goal_3InitEnv)
    (hcarry5354 : denoteGraph_ringAttn sm_goal_3 initSM 5354 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9717,
         denoteGraph_ringAttn pm_goal_3 initPM 9718])
    (h9717 : (denoteGraph_ringAttn pm_goal_3 initPM 9717).shape = [2048, 1024])
    (h9718 : (denoteGraph_ringAttn pm_goal_3 initPM 9718).shape = [2048, 1024]) :
    denoteGraph_ringAttn sm_goal_3 initSM 5384
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 9815,
           denoteGraph_ringAttn pm_goal_3 initPM 9816] := by
  have hb := L12_weight_eq initSM initPM hInit
  have hw5355 : initSM 5355 = initPM 5355 := hb initGoal_5355 (by decide) rfl
  have hw5367 : initSM 5367 = initPM 5367 := hb initGoal_5367 (by decide) rfl
  have hw5372 : initSM 5372 = initPM 5372 := hb initGoal_5372 (by decide) rfl
  have hw5376 : initSM 5376 = initPM 5376 := hb initGoal_5376 (by decide) rfl
  have hw5381 : initSM 5381 = initPM 5381 := hb initGoal_5381 (by decide) rfl
  -- rms of the layer input commutes to the two PM rms-shard denote forms
  have hRMS : fw_rms_norm (denoteGraph_ringAttn sm_goal_3 initSM 5354) (initSM 5355)
      = allGatherPrimDimN 0 2 0
          [denoteGraph_ringAttn pm_goal_3 initPM 9721,
           denoteGraph_ringAttn pm_goal_3 initPM 9722] := by
    rw [hcarry5354, hw5355,
        fw_rms_norm_allGather0_commute_2 _ _ (initPM 5355) 2048 1024 (by omega) (by omega) h9717 h9718,
        ← denote_pm_goal_3_9721, ← denote_pm_goal_3_9722]
  -- Expand RHS PM gate tree (modular bridges) down to the two rms leaves 9721 / 9722
  rw [denote_pm_goal_3_9815, denote_pm_goal_3_9816,
      denote_pm_goal_3_9755, denote_pm_goal_3_9753, denote_pm_goal_3_9747, denote_pm_goal_3_9743, denote_pm_goal_3_16012,
      denote_pm_goal_3_9811, denote_pm_goal_3_9801, denote_pm_goal_3_9795, denote_pm_goal_3_9793,
      denote_pm_goal_3_9771, denote_pm_goal_3_9761, denote_pm_goal_3_9757, denote_pm_goal_3_16016,
      denote_pm_goal_3_9789, denote_pm_goal_3_9779, denote_pm_goal_3_9775, denote_pm_goal_3_16020,
      denote_pm_goal_3_9756, denote_pm_goal_3_9754, denote_pm_goal_3_9748, denote_pm_goal_3_9744, denote_pm_goal_3_16035,
      denote_pm_goal_3_9812, denote_pm_goal_3_9802, denote_pm_goal_3_9796, denote_pm_goal_3_9794,
      denote_pm_goal_3_9772, denote_pm_goal_3_9762, denote_pm_goal_3_9758, denote_pm_goal_3_16039,
      denote_pm_goal_3_9790, denote_pm_goal_3_9780, denote_pm_goal_3_9776, denote_pm_goal_3_16043]
  -- Expand LHS SM gate tree (modular bridges) down to the rms leaf 5356
  rw [denote_sm_goal_3_5384, denote_sm_goal_3_5370, denote_sm_goal_3_5369, denote_sm_goal_3_5368,
      denote_sm_goal_3_5366, denote_sm_goal_3_8166,
      denote_sm_goal_3_5383, denote_sm_goal_3_5382, denote_sm_goal_3_5380, denote_sm_goal_3_5379,
      denote_sm_goal_3_5374, denote_sm_goal_3_5373, denote_sm_goal_3_5371, denote_sm_goal_3_8170,
      denote_sm_goal_3_5378, denote_sm_goal_3_5377, denote_sm_goal_3_5375, denote_sm_goal_3_8174,
      denote_sm_goal_3_5356]
  rw [hRMS, hw5367, hw5372, hw5376, hw5381]
  -- Push allGather outward through the gate op chain (pure: uses proven _of variants)
  set A := denoteGraph_ringAttn pm_goal_3 initPM 9721 with hA
  set B := denoteGraph_ringAttn pm_goal_3 initPM 9722 with hB
  have hAsh : A.shape = [2048, 1024] := by
    rw [hA, denote_pm_goal_3_9721, rms_sh]; exact h9717
  have hBsh : B.shape = [2048, 1024] := by
    rw [hB, denote_pm_goal_3_9722, rms_sh]; exact h9718
  have linsh : ∀ (bb ii oo : Nat) (x w : Tensor), x.shape = [bb, ii] → w.shape = [oo, ii] → (fw_linear x w).shape = [bb, oo] := by
    intro bb ii oo x w hx hw
    rw [TrainVerify.Denote.fw_linear_is_matmul bb ii oo x w hx hw]; rfl
  have hw24 : (initPM 5367).shape = [1, 1024] := h_ss_pm 5367 [1, 1024] (by decide)
  have hw29 : (initPM 5372).shape = [512, 1024] := h_ss_pm 5372 [512, 1024] (by decide)
  have hw33 : (initPM 5376).shape = [512, 1024] := h_ss_pm 5376 [512, 1024] (by decide)
  have hw38 : (initPM 5381).shape = [1024, 512] := h_ss_pm 5381 [1024, 512] (by decide)
  -- view commute helpers (literal 4096 via defeq to 2048*2)
  have vcA1024 : fw_view [4096, 1024] (allGatherPrimDimN 0 2 0 [A, B])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1024] A, fw_view [2048, 1024] B] :=
    fw_view_allGather0_commute_2_of A B 2048 1024 (by omega) hAsh hBsh
  rw [vcA1024]
  have hVA : (fw_view [2048, 1024] A).shape = [2048, 1024] := fw_view_shape_eq _ _
  have hVB : (fw_view [2048, 1024] B).shape = [2048, 1024] := fw_view_shape_eq _ _
  rw [fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5367) 2048 1024 1 (by omega) (by omega) (by omega) hVA hVB hw24,
      fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5372) 2048 1024 512 (by omega) (by omega) (by omega) hVA hVB hw29,
      fw_linear_allGather0_commute_2_of (fw_view [2048, 1024] A) (fw_view [2048, 1024] B) (initPM 5376) 2048 1024 512 (by omega) (by omega) (by omega) hVA hVB hw33]
  have hL24A : (fw_linear (fw_view [2048, 1024] A) (initPM 5367)).shape = [2048, 1] := linsh 2048 1024 1 _ _ hVA hw24
  have hL24B : (fw_linear (fw_view [2048, 1024] B) (initPM 5367)).shape = [2048, 1] := linsh 2048 1024 1 _ _ hVB hw24
  have hL29A : (fw_linear (fw_view [2048, 1024] A) (initPM 5372)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVA hw29
  have hL29B : (fw_linear (fw_view [2048, 1024] B) (initPM 5372)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVB hw29
  have hL33A : (fw_linear (fw_view [2048, 1024] A) (initPM 5376)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVA hw33
  have hL33B : (fw_linear (fw_view [2048, 1024] B) (initPM 5376)).shape = [2048, 512] := linsh 2048 1024 512 _ _ hVB hw33
  have vc24 : fw_view [4096, 1] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5367), fw_linear (fw_view [2048, 1024] B) (initPM 5367)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5367)), fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5367))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 1 (by omega) hL24A hL24B
  have vc29 : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5372), fw_linear (fw_view [2048, 1024] B) (initPM 5372)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5372)), fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5372))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hL29A hL29B
  have vc33 : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 1024] A) (initPM 5376), fw_linear (fw_view [2048, 1024] B) (initPM 5376)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5376)), fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5376))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hL33A hL33B
  rw [vc24, vc29, vc33]
  rw [fw_sigmoid_allGather0_commute_2
        (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5367)))
        (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5367)))
        2048 1 (by omega) (by omega) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]
  rw [fw_swiglu_allGather0_commute_2
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5372)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5372)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5376)))
        (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5376)))
        2048 512 (by omega) (by omega) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]
  have hSWA : (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5372))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5376)))).shape = [2048, 512] := by
    rw [TrainVerify.Denote.fw_swiglu_shape]; exact fw_view_shape_eq _ _
  have hSWB : (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5372))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5376)))).shape = [2048, 512] := by
    rw [TrainVerify.Denote.fw_swiglu_shape]; exact fw_view_shape_eq _ _
  have vcSW : fw_view [4096, 512] (allGatherPrimDimN 0 2 0 [fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5372))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5376))), fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5372))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5376)))])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5372))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5376)))), fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5372))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5376))))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 512 (by omega) hSWA hSWB
  rw [vcSW]
  have hSVA : (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5372))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5376))))).shape = [2048, 512] := fw_view_shape_eq _ _
  have hSVB : (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5372))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5376))))).shape = [2048, 512] := fw_view_shape_eq _ _
  rw [fw_linear_allGather0_commute_2_of _ _ (initPM 5381) 2048 512 1024 (by omega) (by omega) (by omega) hSVA hSVB hw38]
  have hD38A : (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5372))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5376))))) (initPM 5381)).shape = [2048, 1024] := linsh 2048 512 1024 _ _ hSVA hw38
  have hD38B : (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5372))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5376))))) (initPM 5381)).shape = [2048, 1024] := linsh 2048 512 1024 _ _ hSVB hw38
  have vcD : fw_view [4096, 1024] (allGatherPrimDimN 0 2 0 [fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5372))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5376))))) (initPM 5381), fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5372))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5376))))) (initPM 5381)])
      = allGatherPrimDimN 0 2 0 [fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5372))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5376))))) (initPM 5381)), fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5372))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5376))))) (initPM 5381))] :=
    fw_view_allGather0_commute_2_of _ _ 2048 1024 (by omega) hD38A hD38B
  rw [vcD]
  rw [fw_mul_allGather0_commute_2_of_broadcast
        (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] A) (initPM 5367))))
        (fw_sigmoid (fw_view [2048, 1] (fw_linear (fw_view [2048, 1024] B) (initPM 5367))))
        (fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5372))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] A) (initPM 5376))))) (initPM 5381)))
        (fw_view [2048, 1024] (fw_linear (fw_view [2048, 512] (fw_swiglu (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5372))) (fw_view [2048, 512] (fw_linear (fw_view [2048, 1024] B) (initPM 5376))))) (initPM 5381)))
        2048 1024 (by omega) (by omega) (by decide) (by decide) (by decide)
        (by rw [TrainVerify.Denote.fw_sigmoid_shape]; exact fw_view_shape_eq _ _) (by rw [TrainVerify.Denote.fw_sigmoid_shape]; exact fw_view_shape_eq _ _) (fw_view_shape_eq _ _) (fw_view_shape_eq _ _)]

-- L12 -> L13 MoE-bridge boundary residual carry: SM 5387 = allGather0[PM 9829, 9830].
-- SM 5387 = elemwiseAdd(SM 5354, elemwiseAdd(SM 5365 [moe_gmm], SM 5384 [gate·expert])).
-- The three sublayer commutes (residual carry / gmm / gate·mul) are combined with the
-- allGather-through-add primitive `fw_add_allGather0_commute_2_2048_1024` (twice).
-- All attention / carry hypotheses are discharged internally from the two `StoreShapesHold`
-- facts, the cut init goals, and the cu_seqlens value pin (mirroring the derivation inside
-- `sm_pm_router_commute_L12_full` and `sm_pm_router_commute_L12_from_attention`).
set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem sm_pm_carry_5387_commute (initSM initPM : Store)
    (hSM : StoreShapesHold initSM sm_goal_3InitEnv)
    (hPM : StoreShapesHold initPM pm_goal_3InitEnv)
    (hInit : InitGoalsHold pm_goal_3.numRanks goal_3_cut_initGoals initSM initPM)
    (hp5346 : initPM 5346 = cu_pin_value) :
    denoteGraph_ringAttn sm_goal_3 initSM 5387 =
      allGatherPrimDimN 0 2 0
        [denoteGraph_ringAttn pm_goal_3 initPM 9829,
         denoteGraph_ringAttn pm_goal_3 initPM 9830] := by
  -- cu_seqlens well-formed bound from the value pin
  have h_bound := cu_bound_of_value_pin (initPM 5346) hp5346
  -- === attention block (from `sm_pm_router_commute_L12_full`) ===
  have hcarry5330 := sm_pm_carry_5330_commute initSM initPM hSM hPM hInit
  have hattn := sm_pm_attention_L12_commute' initSM initPM hSM hPM hInit h_bound
  have h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9625 initPM hPM
  have h9626 : (denoteGraph_ringAttn pm_goal_3 initPM 9626).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9626 initPM hPM
  have hw5341 : (initPM 5341).shape = [16, 64, 1024] := hPM 5341 [16, 64, 1024] (by decide)
  have hw5350 : (initPM 5350).shape = [1024, 1024] := hPM 5350 [1024, 1024] (by decide)
  have h13257 : (denoteGraph_ringAttn pm_goal_3 initPM 13257).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_13257]; exact h9625
  have h9655 : (denoteGraph_ringAttn pm_goal_3 initPM 9655).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9655, fw_maybe_shuffle_shape]; exact h13257
  have h9657 : (denoteGraph_ringAttn pm_goal_3 initPM 9657).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9657, rms_sh]; exact h9655
  have h9659d : (denoteGraph_ringAttn pm_goal_3 initPM 9659).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_9659]; exact ph_lin_shape_gen _ _ 2048 16 h9657 hw5341
  have h13258 : (denoteGraph_ringAttn pm_goal_3 initPM 13258).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_13258]; exact h9626
  have h9656 : (denoteGraph_ringAttn pm_goal_3 initPM 9656).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9656, fw_maybe_shuffle_shape]; exact h13258
  have h9658 : (denoteGraph_ringAttn pm_goal_3 initPM 9658).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9658, rms_sh]; exact h9656
  have h9660d : (denoteGraph_ringAttn pm_goal_3 initPM 9660).shape = [2048, 16, 64] := by
    rw [denote_pm_goal_3_9660]; exact ph_lin_shape_gen _ _ 2048 16 h9658 hw5341
  have b1067_9659 : (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 9659
      = denoteGraph_ringAttn pm_goal_3 initPM 9659 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9659 1067 (by decide) (by decide)).symm
  have b1067_9660 : (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM 9660
      = denoteGraph_ringAttn pm_goal_3 initPM 9660 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9660 1067 (by decide) (by decide)).symm
  have b1068_9659 : (pm_goal_3.nodes.take 1068).foldl (applyNodeRingAttn pm_goal_3) initPM 9659
      = denoteGraph_ringAttn pm_goal_3 initPM 9659 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9659 1068 (by decide) (by decide)).symm
  have b1068_9660 : (pm_goal_3.nodes.take 1068).foldl (applyNodeRingAttn pm_goal_3) initPM 9660
      = denoteGraph_ringAttn pm_goal_3 initPM 9660 :=
    (foldl_prefix_eq_full_ringAttn pm_goal_3 pm_goal_3.nodes initPM 9660 1068 (by decide) (by decide)).symm
  have h9687 : (denoteGraph_ringAttn pm_goal_3 initPM 9687).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L12_r0_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR0_12 nR0_12 nR1_12 0 buddy_r0_12 (by decide)]
    have e0 : nR0_12.ins.getD 0 0 = 9659 := by decide
    have e1 : nR1_12.ins.getD 0 0 = 9660 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_12.ins.getD 0 0),
         (pm_goal_3.nodes.take 1067).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_12.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1067_9659, b1067_9660]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h9659d)
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  have h9688 : (denoteGraph_ringAttn pm_goal_3 initPM 9688).shape = [2048, 16, 64] := by
    rw [denote_pm_attn_L12_r1_bridge,
        applyNodeRingAttn_zigzag_pair_eq_chunk pm_goal_3 _ nR1_12 nR0_12 nR1_12 1 buddy_r1_12 (by decide)]
    have e0 : nR0_12.ins.getD 0 0 = 9659 := by decide
    have e1 : nR1_12.ins.getD 0 0 = 9660 := by decide
    have hq : (allGatherPrimDimN 0 2 0
        [(pm_goal_3.nodes.take 1068).foldl (applyNodeRingAttn pm_goal_3) initPM (nR0_12.ins.getD 0 0),
         (pm_goal_3.nodes.take 1068).foldl (applyNodeRingAttn pm_goal_3) initPM (nR1_12.ins.getD 0 0)]).shape
        = [4096, 16, 64] := by
      rw [e0, e1, b1068_9659, b1068_9660]
      exact allGatherPrimDimN_shape 0 2 _ [2048, 16, 64] (by exact h9659d)
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * 2048, 16, 64] (by rw [fw_attn_varlen_shape_p3, hq]; rfl) (by omega)]
    rfl
  -- === carry-5354 block (from `sm_pm_router_commute_L12_from_attention`) ===
  have hshuffle := sm_pm_shuffle_carry_commute initSM initPM hcarry5330
  have hreshape := sm_pm_reshape_float_5353_commute initSM initPM hInit hattn h9687 h9688 hw5350
  have h15973 : (denoteGraph_ringAttn pm_goal_3 initPM 15973).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_15973, denote_pm_goal_3_9655, fw_maybe_shuffle_shape, denote_pm_goal_3_13257]
    exact h9625
  have h15981 : (denoteGraph_ringAttn pm_goal_3 initPM 15981).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_15981, denote_pm_goal_3_9656, fw_maybe_shuffle_shape, denote_pm_goal_3_13258]
    exact h9626
  have h9713 : (denoteGraph_ringAttn pm_goal_3 initPM 9713).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9713, denote_pm_goal_3_9709]; rfl
  have h9714 : (denoteGraph_ringAttn pm_goal_3 initPM 9714).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9714, denote_pm_goal_3_9710]; rfl
  have hcarry5354 := sm_pm_carry_5354_commute initSM initPM hshuffle hreshape h15973 h15981 h9713 h9714
  have h9717 : (denoteGraph_ringAttn pm_goal_3 initPM 9717).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9717]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h15973 h9713
  have h9718 : (denoteGraph_ringAttn pm_goal_3 initPM 9718).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9718]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h15981 h9714
  -- === the two MoE sublayer commutes ===
  have hgmm := sm_pm_moe_gmm_L12_commute initSM initPM hInit hPM hcarry5354 h9717 h9718
  have hgate := sm_pm_gate_mul_L12_commute initSM initPM hInit hPM hcarry5354 h9717 h9718
  -- === shard shapes of the gmm / gate outputs (both [2048, 1024]) ===
  have h9721sh : (denoteGraph_ringAttn pm_goal_3 initPM 9721).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9721, rms_sh]; exact h9717
  have h9722sh : (denoteGraph_ringAttn pm_goal_3 initPM 9722).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9722, rms_sh]; exact h9718
  have h9741sh : (denoteGraph_ringAttn pm_goal_3 initPM 9741).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9741, denote_pm_goal_3_16008]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h9721sh]; rfl) (by rw [h9721sh]; rfl)
  have h9742sh : (denoteGraph_ringAttn pm_goal_3 initPM 9742).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9742, denote_pm_goal_3_16031]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h9722sh]; rfl) (by rw [h9722sh]; rfl)
  have h9755sh : (denoteGraph_ringAttn pm_goal_3 initPM 9755).shape = [2048, 1] := by
    rw [denote_pm_goal_3_9755, TrainVerify.Denote.fw_sigmoid_shape, denote_pm_goal_3_9753]
    exact fw_view_shape_eq _ _
  have h9811sh : (denoteGraph_ringAttn pm_goal_3 initPM 9811).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9811]; exact fw_view_shape_eq _ _
  have h9815sh : (denoteGraph_ringAttn pm_goal_3 initPM 9815).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9815, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h9755sh h9811sh]; rfl
  have h9756sh : (denoteGraph_ringAttn pm_goal_3 initPM 9756).shape = [2048, 1] := by
    rw [denote_pm_goal_3_9756, TrainVerify.Denote.fw_sigmoid_shape, denote_pm_goal_3_9754]
    exact fw_view_shape_eq _ _
  have h9812sh : (denoteGraph_ringAttn pm_goal_3 initPM 9812).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9812]; exact fw_view_shape_eq _ _
  have h9816sh : (denoteGraph_ringAttn pm_goal_3 initPM 9816).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9816, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h9756sh h9812sh]; rfl
  -- inner-add shard shapes
  have hinnerA : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 9741) (denoteGraph_ringAttn pm_goal_3 initPM 9815)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h9741sh h9815sh
  have hinnerB : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 9742) (denoteGraph_ringAttn pm_goal_3 initPM 9816)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h9742sh h9816sh
  -- === assemble ===
  rw [denote_pm_goal_3_9829, denote_pm_goal_3_15989, denote_pm_goal_3_9825, denote_pm_goal_3_9819,
      denote_pm_goal_3_9830, denote_pm_goal_3_15997, denote_pm_goal_3_9826, denote_pm_goal_3_9820]
  rw [denote_sm_goal_3_5387, denote_sm_goal_3_8151, denote_sm_goal_3_5386, denote_sm_goal_3_5385]
  rw [hcarry5354, hgmm, hgate]
  rw [fw_add_allGather0_commute_2_2048_1024
        (denoteGraph_ringAttn pm_goal_3 initPM 9741) (denoteGraph_ringAttn pm_goal_3 initPM 9742)
        (denoteGraph_ringAttn pm_goal_3 initPM 9815) (denoteGraph_ringAttn pm_goal_3 initPM 9816)
        h9741sh h9742sh h9815sh h9816sh]
  rw [fw_add_allGather0_commute_2_2048_1024
        (denoteGraph_ringAttn pm_goal_3 initPM 9717) (denoteGraph_ringAttn pm_goal_3 initPM 9718)
        (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 9741) (denoteGraph_ringAttn pm_goal_3 initPM 9815))
        (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 9742) (denoteGraph_ringAttn pm_goal_3 initPM 9816))
        h9717 h9718 hinnerA hinnerB]

-- Shape of the L13-entry residual pm 9829 = elemwiseAdd (pm 15989) (pm 9825).
-- pm 15989 = pm 9717 ([2048,1024]); pm 9825 = pm 9819 = elemwiseAdd (pm 9741) (pm 9815).
-- Lifted from the shape haves in `sm_pm_carry_5387_commute` above.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem pm_goal_3_9829_shape
    (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 9829).shape = [2048, 1024] := by
  have h9625 : (denoteGraph_ringAttn pm_goal_3 initPM 9625).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9625 initPM hPM
  have h15973 : (denoteGraph_ringAttn pm_goal_3 initPM 15973).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_15973, denote_pm_goal_3_9655, fw_maybe_shuffle_shape, denote_pm_goal_3_13257]
    exact h9625
  have h9713 : (denoteGraph_ringAttn pm_goal_3 initPM 9713).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9713, denote_pm_goal_3_9709]; rfl
  have h9717 : (denoteGraph_ringAttn pm_goal_3 initPM 9717).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9717]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h15973 h9713
  have h9721sh : (denoteGraph_ringAttn pm_goal_3 initPM 9721).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9721, rms_sh]; exact h9717
  have h9741sh : (denoteGraph_ringAttn pm_goal_3 initPM 9741).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9741, denote_pm_goal_3_16008]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h9721sh]; rfl) (by rw [h9721sh]; rfl)
  have h9755sh : (denoteGraph_ringAttn pm_goal_3 initPM 9755).shape = [2048, 1] := by
    rw [denote_pm_goal_3_9755, TrainVerify.Denote.fw_sigmoid_shape, denote_pm_goal_3_9753]
    exact fw_view_shape_eq _ _
  have h9811sh : (denoteGraph_ringAttn pm_goal_3 initPM 9811).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9811]; exact fw_view_shape_eq _ _
  have h9815sh : (denoteGraph_ringAttn pm_goal_3 initPM 9815).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9815, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h9755sh h9811sh]; rfl
  have hinnerA : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 9741) (denoteGraph_ringAttn pm_goal_3 initPM 9815)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h9741sh h9815sh
  have h15989sh : (denoteGraph_ringAttn pm_goal_3 initPM 15989).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_15989]; exact h9717
  have h9825sh : (denoteGraph_ringAttn pm_goal_3 initPM 9825).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9825, denote_pm_goal_3_9819]; exact hinnerA
  rw [denote_pm_goal_3_9829]
  exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h15989sh h9825sh

-- Shape of the L13-entry residual pm 9830 = elemwiseAdd (pm 15997) (pm 9826) (rank-1 mirror).
set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem pm_goal_3_9830_shape
    (initPM : Store) (hPM : StoreShapesHold initPM pm_goal_3InitEnv) :
    (denoteGraph_ringAttn pm_goal_3 initPM 9830).shape = [2048, 1024] := by
  have h9626 : (denoteGraph_ringAttn pm_goal_3 initPM 9626).shape = [2048, 1024] :=
    RouterShapesHelpers.hs_9626 initPM hPM
  have h15981 : (denoteGraph_ringAttn pm_goal_3 initPM 15981).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_15981, denote_pm_goal_3_9656, fw_maybe_shuffle_shape, denote_pm_goal_3_13258]
    exact h9626
  have h9714 : (denoteGraph_ringAttn pm_goal_3 initPM 9714).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9714, denote_pm_goal_3_9710]; rfl
  have h9718 : (denoteGraph_ringAttn pm_goal_3 initPM 9718).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9718]; exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h15981 h9714
  have h9722sh : (denoteGraph_ringAttn pm_goal_3 initPM 9722).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9722, rms_sh]; exact h9718
  have h9742sh : (denoteGraph_ringAttn pm_goal_3 initPM 9742).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9742, denote_pm_goal_3_16031]
    exact TrainVerify.Denote.fw_all2all_moe_gmm_full_shape _ _ _ _ _ _ _ _ 2048 1024
      (by rw [h9722sh]; rfl) (by rw [h9722sh]; rfl)
  have h9756sh : (denoteGraph_ringAttn pm_goal_3 initPM 9756).shape = [2048, 1] := by
    rw [denote_pm_goal_3_9756, TrainVerify.Denote.fw_sigmoid_shape, denote_pm_goal_3_9754]
    exact fw_view_shape_eq _ _
  have h9812sh : (denoteGraph_ringAttn pm_goal_3 initPM 9812).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9812]; exact fw_view_shape_eq _ _
  have h9816sh : (denoteGraph_ringAttn pm_goal_3 initPM 9816).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9816, RouterShapesHelpers.elemwiseMul_shape2 _ _ [2048, 1] [2048, 1024] h9756sh h9812sh]; rfl
  have hinnerB : (elemwiseAdd (denoteGraph_ringAttn pm_goal_3 initPM 9742) (denoteGraph_ringAttn pm_goal_3 initPM 9816)).shape = [2048, 1024] :=
    elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h9742sh h9816sh
  have h15997sh : (denoteGraph_ringAttn pm_goal_3 initPM 15997).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_15997]; exact h9718
  have h9826sh : (denoteGraph_ringAttn pm_goal_3 initPM 9826).shape = [2048, 1024] := by
    rw [denote_pm_goal_3_9826, denote_pm_goal_3_9820]; exact hinnerB
  rw [denote_pm_goal_3_9830]
  exact elemwiseAdd_shape_of_shapes _ _ [2048, 1024] h15997sh h9826sh

-- Vacuity witness for the `h_bound` well-formed-input hypothesis (AGENTS.md #29):
-- the all-zero cu_seqlens store satisfies the bound, so the hypothesis is not vacuous.
theorem sm_pm_router_L12_hbound_witness :
    ∃ initPM : Store, ∀ t, (decodeCuSeqlens (initPM 5346)).getD (t+1) 0 ≤ 4096 := by
  refine ⟨fun _ => zeroTensor [0], ?_⟩
  intro t
  have hnil : decodeCuSeqlens (zeroTensor [0]) = [] := by
    simp [decodeCuSeqlens, zeroTensor, Tensor.mkShape, prodShape]
  rw [hnil]
  exact Nat.zero_le _

end TrainVerify.Denote.GeneratedPatterns

-- Axiom audit for the newly ported zigzag primitives (should be kernel-only).
#print axioms TrainVerify.Denote.GeneratedPatterns.applyNodeRingAttn_zigzag_reconstruction_2_of_buddy_pair
#print axioms TrainVerify.Denote.GeneratedPatterns.denote_sm_goal_3_5342
-- PM-side denote chain audits (context-parallel L12 layout)
#print axioms TrainVerify.Denote.GeneratedPatterns.denote_pm_goal_3_9659
#print axioms TrainVerify.Denote.GeneratedPatterns.denote_pm_goal_3_9660
#print axioms TrainVerify.Denote.GeneratedPatterns.denote_pm_goal_3_5343
#print axioms TrainVerify.Denote.GeneratedPatterns.denote_pm_goal_3_5344
#print axioms TrainVerify.Denote.GeneratedPatterns.denote_pm_goal_3_11917
#print axioms TrainVerify.Denote.GeneratedPatterns.applyNodeRingAttn_zigzag_reconstruction_2_cp

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_rms_L12_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_krepl_L12_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_vrepl_L12_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_attention_L12_commute

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_qfull_L12_commute

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_carry_5330_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_shuffle_carry_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_reshape_float_5353_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_nl_L12_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_carry_5354_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L12
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L12_from_attention

#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_attention_L12_commute'
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_commute_L12_full
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_router_L12_hbound_witness
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_moe_gmm_L12_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_gate_mul_L12_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.sm_pm_carry_5387_commute
#print axioms TrainVerify.Denote.GeneratedPatterns.pm_goal_3_9829_shape
#print axioms TrainVerify.Denote.GeneratedPatterns.pm_goal_3_9830_shape
