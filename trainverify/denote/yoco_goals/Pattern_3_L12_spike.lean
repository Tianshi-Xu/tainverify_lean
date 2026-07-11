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
