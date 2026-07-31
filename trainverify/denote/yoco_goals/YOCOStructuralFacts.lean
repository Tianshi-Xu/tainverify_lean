/- Concrete structural facts for the generated YOCO graphs. -/
import denote.yoco_goals.structural.SM_00
import denote.yoco_goals.structural.SM_01
import denote.yoco_goals.structural.SM_02
import denote.yoco_goals.structural.SM_03
import denote.yoco_goals.structural.SM_04
import denote.yoco_goals.structural.SM_05
import denote.yoco_goals.structural.SM_06
import denote.yoco_goals.structural.SM_07
import denote.yoco_goals.structural.SM_08
import denote.yoco_goals.structural.SM_09
import denote.yoco_goals.structural.SM_10
import denote.yoco_goals.structural.SM_11
import denote.yoco_goals.structural.SM_12
import denote.yoco_goals.structural.SM_13
import denote.yoco_goals.structural.SM_14
import denote.yoco_goals.structural.SM_15
import denote.yoco_goals.structural.SM_16
import denote.yoco_goals.structural.SM_17
import denote.yoco_goals.structural.SM_18
import denote.yoco_goals.structural.SM_19
import denote.yoco_goals.structural.SM_20
import denote.yoco_goals.structural.SM_21
import denote.yoco_goals.structural.SM_22
import denote.yoco_goals.structural.SM_23
import denote.yoco_goals.structural.PM_00
import denote.yoco_goals.structural.PM_01
import denote.yoco_goals.structural.PM_02
import denote.yoco_goals.structural.PM_03
import denote.yoco_goals.structural.PM_04
import denote.yoco_goals.structural.PM_05
import denote.yoco_goals.structural.PM_06
import denote.yoco_goals.structural.PM_07
import denote.yoco_goals.structural.PM_08
import denote.yoco_goals.structural.PM_09
import denote.yoco_goals.structural.PM_10
import denote.yoco_goals.structural.PM_11
import denote.yoco_goals.structural.PM_12
import denote.yoco_goals.structural.PM_13
import denote.yoco_goals.structural.PM_14
import denote.yoco_goals.structural.PM_15
import denote.yoco_goals.structural.PM_16
import denote.yoco_goals.structural.PM_17
import denote.yoco_goals.structural.PM_18
import denote.yoco_goals.structural.PM_19
import denote.yoco_goals.structural.PM_20
import denote.yoco_goals.structural.PM_21
import denote.yoco_goals.structural.PM_22
import denote.yoco_goals.structural.PM_23
import denote.yoco_goals.structural.PM_24
import denote.yoco_goals.structural.PM_25
import denote.yoco_goals.structural.PM_26
import denote.yoco_goals.structural.PM_27
import denote.yoco_goals.structural.PM_28
import denote.yoco_goals.structural.PM_29
import denote.yoco_goals.structural.PM_30
import denote.yoco_goals.structural.PM_31
import denote.yoco_goals.structural.PM_32
import denote.yoco_goals.structural.PM_33
import denote.yoco_goals.structural.PM_34
import denote.yoco_goals.structural.PM_35
import denote.yoco_goals.structural.PM_36
import denote.yoco_goals.structural.PM_37
import denote.yoco_goals.structural.PM_38
import denote.yoco_goals.structural.PM_39
import denote.yoco_goals.structural.PM_40
import denote.yoco_goals.structural.PM_41
import denote.yoco_goals.structural.PM_42
import denote.yoco_goals.structural.PM_43
import denote.yoco_goals.structural.PM_44
import denote.yoco_goals.structural.PM_45
import denote.yoco_goals.structural.PM_46
import denote.yoco_goals.structural.PM_47

set_option linter.style.longLine false
set_option maxRecDepth 1000000
namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

def smChunk_0 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_embedding", ins := [4677, 4679], outs := [4680] }, { rank := 0, op := "OpName.FW_float", ins := [4680], outs := [4681] }, { rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [7383, 7387], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [7383, 4682], outs := [4683] }, { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [7392, 7396, 7400], params := [3] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7392, 4684], outs := [4685] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7396, 4686], outs := [4687] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7400, 4688], outs := [4689] }, { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4690, 4685, 4687], outs := [4692, 4693], params := [16, 4] }, { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4692, 4693, 4689, 4694, 4695], outs := [4696], params := [16, 4, 64, 64, 1, 512] }, { rank := 0, op := "OpName.FW_reshape", ins := [4696], outs := [4697], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [4697], outs := [4698], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4698, 4699], outs := [4700] }, { rank := 0, op := "OpName.FW_view", ins := [4700], outs := [4701], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [4701], outs := [4702] }, { rank := 0, op := "OpName.FW_add", ins := [7387, 4702], outs := [4703] }, { rank := 0, op := "OpName.FW_multiref", ins := [4703], outs := [7404, 7408], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [7404, 4704], outs := [4705] }, { rank := 0, op := "OpName.FW_multiref", ins := [4705], outs := [7415, 7419, 7423, 7427, 7431], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [7415], outs := [4706] }, { rank := 0, op := "OpName.FW_reshape", ins := [7423], outs := [4715], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7427], outs := [4720], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7431], outs := [4724], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [4706, 4707], outs := [4708] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4715, 4716], outs := [4717] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4720, 4721], outs := [4722] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4724, 4725], outs := [4726] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [4708], outs := [4709, 4710, 4711], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [4717], outs := [4718], params := [4096, 1] }, { rank := 0, op := "OpName.FW_view", ins := [4722], outs := [4723], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [4726], outs := [4727], params := [4096, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7419, 4709, 4710, 4712, 4713], outs := [4714], params := [64, 0, 64, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [4718], outs := [4719] }, { rank := 0, op := "OpName.FW_swiglu", ins := [4723, 4727], outs := [4728] }, { rank := 0, op := "OpName.FW_reshape", ins := [4728], outs := [4729], params := [4096, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4729, 4730], outs := [4731] }, { rank := 0, op := "OpName.FW_view", ins := [4731], outs := [4732], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [4719, 4732], outs := [4733] }, { rank := 0, op := "OpName.FW_add", ins := [4714, 4733], outs := [4734] }, { rank := 0, op := "OpName.FW_float", ins := [4734], outs := [4735] }]

theorem smChunk_0_wf : ∀ n ∈ smChunk_0, IsWellFormedNode sm n := by
  intro n hn
  simp only [smChunk_0, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact sm_node_0_wf
  · rw [h1]
    exact sm_node_1_wf
  · rw [h2]
    exact sm_node_2_wf
  · rw [h3]
    exact sm_node_3_wf
  · rw [h4]
    exact sm_node_4_wf
  · rw [h5]
    exact sm_node_5_wf
  · rw [h6]
    exact sm_node_6_wf
  · rw [h7]
    exact sm_node_7_wf
  · rw [h8]
    exact sm_node_8_wf
  · rw [h9]
    exact sm_node_9_wf
  · rw [h10]
    exact sm_node_10_wf
  · rw [h11]
    exact sm_node_11_wf
  · rw [h12]
    exact sm_node_12_wf
  · rw [h13]
    exact sm_node_13_wf
  · rw [h14]
    exact sm_node_14_wf
  · rw [h15]
    exact sm_node_15_wf
  · rw [h16]
    exact sm_node_16_wf
  · rw [h17]
    exact sm_node_17_wf
  · rw [h18]
    exact sm_node_18_wf
  · rw [h19]
    exact sm_node_19_wf
  · rw [h20]
    exact sm_node_20_wf
  · rw [h21]
    exact sm_node_21_wf
  · rw [h22]
    exact sm_node_22_wf
  · rw [h23]
    exact sm_node_23_wf
  · rw [h24]
    exact sm_node_24_wf
  · rw [h25]
    exact sm_node_25_wf
  · rw [h26]
    exact sm_node_26_wf
  · rw [h27]
    exact sm_node_27_wf
  · rw [h28]
    exact sm_node_28_wf
  · rw [h29]
    exact sm_node_29_wf
  · rw [h30]
    exact sm_node_30_wf
  · rw [h31]
    exact sm_node_31_wf
  · rw [h32]
    exact sm_node_32_wf
  · rw [h33]
    exact sm_node_33_wf
  · rw [h34]
    exact sm_node_34_wf
  · rw [h35]
    exact sm_node_35_wf
  · rw [h36]
    exact sm_node_36_wf
  · rw [h37]
    exact sm_node_37_wf
  · rw [h38]
    exact sm_node_38_wf
  · rw [h39]
    exact sm_node_39_wf

def smChunk_1 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_add", ins := [7408, 4735], outs := [4736] }, { rank := 0, op := "OpName.FW_multiref", ins := [4736], outs := [7435, 7439], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [7435, 4737], outs := [4738] }, { rank := 0, op := "OpName.FW_multiref", ins := [4738], outs := [7444, 7448, 7452], params := [3] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7444, 4739], outs := [4740] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7448, 4741], outs := [4742] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7452, 4743], outs := [4744] }, { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4745, 4740, 4742], outs := [4746, 4747], params := [16, 4] }, { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4746, 4747, 4744, 4748, 4749], outs := [4750], params := [16, 4, 64, 64, 1, 512] }, { rank := 0, op := "OpName.FW_reshape", ins := [4750], outs := [4751], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [4751], outs := [4752], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4752, 4753], outs := [4754] }, { rank := 0, op := "OpName.FW_view", ins := [4754], outs := [4755], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [4755], outs := [4756] }, { rank := 0, op := "OpName.FW_add", ins := [7439, 4756], outs := [4757] }, { rank := 0, op := "OpName.FW_multiref", ins := [4757], outs := [7456, 7460], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [7456, 4758], outs := [4759] }, { rank := 0, op := "OpName.FW_multiref", ins := [4759], outs := [7467, 7471, 7475, 7479, 7483], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [7467], outs := [4760] }, { rank := 0, op := "OpName.FW_reshape", ins := [7475], outs := [4769], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7479], outs := [4774], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7483], outs := [4778], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [4760, 4761], outs := [4762] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4769, 4770], outs := [4771] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4774, 4775], outs := [4776] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4778, 4779], outs := [4780] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [4762], outs := [4763, 4764, 4765], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [4771], outs := [4772], params := [4096, 1] }, { rank := 0, op := "OpName.FW_view", ins := [4776], outs := [4777], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [4780], outs := [4781], params := [4096, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7471, 4763, 4764, 4766, 4767], outs := [4768], params := [64, 0, 64, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [4772], outs := [4773] }, { rank := 0, op := "OpName.FW_swiglu", ins := [4777, 4781], outs := [4782] }, { rank := 0, op := "OpName.FW_reshape", ins := [4782], outs := [4783], params := [4096, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4783, 4784], outs := [4785] }, { rank := 0, op := "OpName.FW_view", ins := [4785], outs := [4786], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [4773, 4786], outs := [4787] }, { rank := 0, op := "OpName.FW_add", ins := [4768, 4787], outs := [4788] }, { rank := 0, op := "OpName.FW_float", ins := [4788], outs := [4789] }, { rank := 0, op := "OpName.FW_add", ins := [7460, 4789], outs := [4790] }]

theorem smChunk_1_wf : ∀ n ∈ smChunk_1, IsWellFormedNode sm n := by
  intro n hn
  simp only [smChunk_1, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact sm_node_40_wf
  · rw [h1]
    exact sm_node_41_wf
  · rw [h2]
    exact sm_node_42_wf
  · rw [h3]
    exact sm_node_43_wf
  · rw [h4]
    exact sm_node_44_wf
  · rw [h5]
    exact sm_node_45_wf
  · rw [h6]
    exact sm_node_46_wf
  · rw [h7]
    exact sm_node_47_wf
  · rw [h8]
    exact sm_node_48_wf
  · rw [h9]
    exact sm_node_49_wf
  · rw [h10]
    exact sm_node_50_wf
  · rw [h11]
    exact sm_node_51_wf
  · rw [h12]
    exact sm_node_52_wf
  · rw [h13]
    exact sm_node_53_wf
  · rw [h14]
    exact sm_node_54_wf
  · rw [h15]
    exact sm_node_55_wf
  · rw [h16]
    exact sm_node_56_wf
  · rw [h17]
    exact sm_node_57_wf
  · rw [h18]
    exact sm_node_58_wf
  · rw [h19]
    exact sm_node_59_wf
  · rw [h20]
    exact sm_node_60_wf
  · rw [h21]
    exact sm_node_61_wf
  · rw [h22]
    exact sm_node_62_wf
  · rw [h23]
    exact sm_node_63_wf
  · rw [h24]
    exact sm_node_64_wf
  · rw [h25]
    exact sm_node_65_wf
  · rw [h26]
    exact sm_node_66_wf
  · rw [h27]
    exact sm_node_67_wf
  · rw [h28]
    exact sm_node_68_wf
  · rw [h29]
    exact sm_node_69_wf
  · rw [h30]
    exact sm_node_70_wf
  · rw [h31]
    exact sm_node_71_wf
  · rw [h32]
    exact sm_node_72_wf
  · rw [h33]
    exact sm_node_73_wf
  · rw [h34]
    exact sm_node_74_wf
  · rw [h35]
    exact sm_node_75_wf
  · rw [h36]
    exact sm_node_76_wf
  · rw [h37]
    exact sm_node_77_wf
  · rw [h38]
    exact sm_node_78_wf
  · rw [h39]
    exact sm_node_79_wf

def smChunk_2 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_multiref", ins := [4790], outs := [7487, 7491], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [7487, 4791], outs := [4792] }, { rank := 0, op := "OpName.FW_multiref", ins := [4792], outs := [7496, 7500, 7504], params := [3] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7496, 4793], outs := [4794] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7500, 4795], outs := [4796] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7504, 4797], outs := [4798] }, { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4799, 4794, 4796], outs := [4800, 4801], params := [16, 4] }, { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4800, 4801, 4798, 4802, 4803], outs := [4804], params := [16, 4, 64, 64, 1, 512] }, { rank := 0, op := "OpName.FW_reshape", ins := [4804], outs := [4805], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [4805], outs := [4806], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4806, 4807], outs := [4808] }, { rank := 0, op := "OpName.FW_view", ins := [4808], outs := [4809], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [4809], outs := [4810] }, { rank := 0, op := "OpName.FW_add", ins := [7491, 4810], outs := [4811] }, { rank := 0, op := "OpName.FW_multiref", ins := [4811], outs := [7508, 7512], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [7508, 4812], outs := [4813] }, { rank := 0, op := "OpName.FW_multiref", ins := [4813], outs := [7519, 7523, 7527, 7531, 7535], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [7519], outs := [4814] }, { rank := 0, op := "OpName.FW_reshape", ins := [7527], outs := [4823], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7531], outs := [4828], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7535], outs := [4832], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [4814, 4815], outs := [4816] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4823, 4824], outs := [4825] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4828, 4829], outs := [4830] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4832, 4833], outs := [4834] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [4816], outs := [4817, 4818, 4819], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [4825], outs := [4826], params := [4096, 1] }, { rank := 0, op := "OpName.FW_view", ins := [4830], outs := [4831], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [4834], outs := [4835], params := [4096, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7523, 4817, 4818, 4820, 4821], outs := [4822], params := [64, 0, 64, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [4826], outs := [4827] }, { rank := 0, op := "OpName.FW_swiglu", ins := [4831, 4835], outs := [4836] }, { rank := 0, op := "OpName.FW_reshape", ins := [4836], outs := [4837], params := [4096, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4837, 4838], outs := [4839] }, { rank := 0, op := "OpName.FW_view", ins := [4839], outs := [4840], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [4827, 4840], outs := [4841] }, { rank := 0, op := "OpName.FW_add", ins := [4822, 4841], outs := [4842] }, { rank := 0, op := "OpName.FW_float", ins := [4842], outs := [4843] }, { rank := 0, op := "OpName.FW_add", ins := [7512, 4843], outs := [4844] }, { rank := 0, op := "OpName.FW_multiref", ins := [4844], outs := [7539, 7543], params := [2] }]

theorem smChunk_2_wf : ∀ n ∈ smChunk_2, IsWellFormedNode sm n := by
  intro n hn
  simp only [smChunk_2, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact sm_node_80_wf
  · rw [h1]
    exact sm_node_81_wf
  · rw [h2]
    exact sm_node_82_wf
  · rw [h3]
    exact sm_node_83_wf
  · rw [h4]
    exact sm_node_84_wf
  · rw [h5]
    exact sm_node_85_wf
  · rw [h6]
    exact sm_node_86_wf
  · rw [h7]
    exact sm_node_87_wf
  · rw [h8]
    exact sm_node_88_wf
  · rw [h9]
    exact sm_node_89_wf
  · rw [h10]
    exact sm_node_90_wf
  · rw [h11]
    exact sm_node_91_wf
  · rw [h12]
    exact sm_node_92_wf
  · rw [h13]
    exact sm_node_93_wf
  · rw [h14]
    exact sm_node_94_wf
  · rw [h15]
    exact sm_node_95_wf
  · rw [h16]
    exact sm_node_96_wf
  · rw [h17]
    exact sm_node_97_wf
  · rw [h18]
    exact sm_node_98_wf
  · rw [h19]
    exact sm_node_99_wf
  · rw [h20]
    exact sm_node_100_wf
  · rw [h21]
    exact sm_node_101_wf
  · rw [h22]
    exact sm_node_102_wf
  · rw [h23]
    exact sm_node_103_wf
  · rw [h24]
    exact sm_node_104_wf
  · rw [h25]
    exact sm_node_105_wf
  · rw [h26]
    exact sm_node_106_wf
  · rw [h27]
    exact sm_node_107_wf
  · rw [h28]
    exact sm_node_108_wf
  · rw [h29]
    exact sm_node_109_wf
  · rw [h30]
    exact sm_node_110_wf
  · rw [h31]
    exact sm_node_111_wf
  · rw [h32]
    exact sm_node_112_wf
  · rw [h33]
    exact sm_node_113_wf
  · rw [h34]
    exact sm_node_114_wf
  · rw [h35]
    exact sm_node_115_wf
  · rw [h36]
    exact sm_node_116_wf
  · rw [h37]
    exact sm_node_117_wf
  · rw [h38]
    exact sm_node_118_wf
  · rw [h39]
    exact sm_node_119_wf

def smChunk_3 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_rms_norm", ins := [7539, 4845], outs := [4846] }, { rank := 0, op := "OpName.FW_multiref", ins := [4846], outs := [7548, 7552, 7556], params := [3] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7548, 4847], outs := [4848] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7552, 4849], outs := [4850] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7556, 4851], outs := [4852] }, { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4853, 4848, 4850], outs := [4854, 4855], params := [16, 4] }, { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4854, 4855, 4852, 4856, 4857], outs := [4858], params := [16, 4, 64, 64, 1, 512] }, { rank := 0, op := "OpName.FW_reshape", ins := [4858], outs := [4859], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [4859], outs := [4860], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4860, 4861], outs := [4862] }, { rank := 0, op := "OpName.FW_view", ins := [4862], outs := [4863], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [4863], outs := [4864] }, { rank := 0, op := "OpName.FW_add", ins := [7543, 4864], outs := [4865] }, { rank := 0, op := "OpName.FW_multiref", ins := [4865], outs := [7560, 7564], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [7560, 4866], outs := [4867] }, { rank := 0, op := "OpName.FW_multiref", ins := [4867], outs := [7571, 7575, 7579, 7583, 7587], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [7571], outs := [4868] }, { rank := 0, op := "OpName.FW_reshape", ins := [7579], outs := [4877], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7583], outs := [4882], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7587], outs := [4886], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [4868, 4869], outs := [4870] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4877, 4878], outs := [4879] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4882, 4883], outs := [4884] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4886, 4887], outs := [4888] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [4870], outs := [4871, 4872, 4873], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [4879], outs := [4880], params := [4096, 1] }, { rank := 0, op := "OpName.FW_view", ins := [4884], outs := [4885], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [4888], outs := [4889], params := [4096, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7575, 4871, 4872, 4874, 4875], outs := [4876], params := [64, 0, 64, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [4880], outs := [4881] }, { rank := 0, op := "OpName.FW_swiglu", ins := [4885, 4889], outs := [4890] }, { rank := 0, op := "OpName.FW_reshape", ins := [4890], outs := [4891], params := [4096, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4891, 4892], outs := [4893] }, { rank := 0, op := "OpName.FW_view", ins := [4893], outs := [4894], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [4881, 4894], outs := [4895] }, { rank := 0, op := "OpName.FW_add", ins := [4876, 4895], outs := [4896] }, { rank := 0, op := "OpName.FW_float", ins := [4896], outs := [4897] }, { rank := 0, op := "OpName.FW_add", ins := [7564, 4897], outs := [4898] }, { rank := 0, op := "OpName.FW_multiref", ins := [4898], outs := [7591, 7595], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [7591, 4899], outs := [4900] }]

theorem smChunk_3_wf : ∀ n ∈ smChunk_3, IsWellFormedNode sm n := by
  intro n hn
  simp only [smChunk_3, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact sm_node_120_wf
  · rw [h1]
    exact sm_node_121_wf
  · rw [h2]
    exact sm_node_122_wf
  · rw [h3]
    exact sm_node_123_wf
  · rw [h4]
    exact sm_node_124_wf
  · rw [h5]
    exact sm_node_125_wf
  · rw [h6]
    exact sm_node_126_wf
  · rw [h7]
    exact sm_node_127_wf
  · rw [h8]
    exact sm_node_128_wf
  · rw [h9]
    exact sm_node_129_wf
  · rw [h10]
    exact sm_node_130_wf
  · rw [h11]
    exact sm_node_131_wf
  · rw [h12]
    exact sm_node_132_wf
  · rw [h13]
    exact sm_node_133_wf
  · rw [h14]
    exact sm_node_134_wf
  · rw [h15]
    exact sm_node_135_wf
  · rw [h16]
    exact sm_node_136_wf
  · rw [h17]
    exact sm_node_137_wf
  · rw [h18]
    exact sm_node_138_wf
  · rw [h19]
    exact sm_node_139_wf
  · rw [h20]
    exact sm_node_140_wf
  · rw [h21]
    exact sm_node_141_wf
  · rw [h22]
    exact sm_node_142_wf
  · rw [h23]
    exact sm_node_143_wf
  · rw [h24]
    exact sm_node_144_wf
  · rw [h25]
    exact sm_node_145_wf
  · rw [h26]
    exact sm_node_146_wf
  · rw [h27]
    exact sm_node_147_wf
  · rw [h28]
    exact sm_node_148_wf
  · rw [h29]
    exact sm_node_149_wf
  · rw [h30]
    exact sm_node_150_wf
  · rw [h31]
    exact sm_node_151_wf
  · rw [h32]
    exact sm_node_152_wf
  · rw [h33]
    exact sm_node_153_wf
  · rw [h34]
    exact sm_node_154_wf
  · rw [h35]
    exact sm_node_155_wf
  · rw [h36]
    exact sm_node_156_wf
  · rw [h37]
    exact sm_node_157_wf
  · rw [h38]
    exact sm_node_158_wf
  · rw [h39]
    exact sm_node_159_wf

def smChunk_4 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_multiref", ins := [4900], outs := [7600, 7604, 7608], params := [3] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7600, 4901], outs := [4902] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7604, 4903], outs := [4904] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7608, 4905], outs := [4906] }, { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4907, 4902, 4904], outs := [4908, 4909], params := [16, 4] }, { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4908, 4909, 4906, 4910, 4911], outs := [4912], params := [16, 4, 64, 64, 1, 512] }, { rank := 0, op := "OpName.FW_reshape", ins := [4912], outs := [4913], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [4913], outs := [4914], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4914, 4915], outs := [4916] }, { rank := 0, op := "OpName.FW_view", ins := [4916], outs := [4917], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [4917], outs := [4918] }, { rank := 0, op := "OpName.FW_add", ins := [7595, 4918], outs := [4919] }, { rank := 0, op := "OpName.FW_multiref", ins := [4919], outs := [7612, 7616], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [7612, 4920], outs := [4921] }, { rank := 0, op := "OpName.FW_multiref", ins := [4921], outs := [7623, 7627, 7631, 7635, 7639], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [7623], outs := [4922] }, { rank := 0, op := "OpName.FW_reshape", ins := [7631], outs := [4931], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7635], outs := [4936], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7639], outs := [4940], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [4922, 4923], outs := [4924] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4931, 4932], outs := [4933] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4936, 4937], outs := [4938] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4940, 4941], outs := [4942] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [4924], outs := [4925, 4926, 4927], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [4933], outs := [4934], params := [4096, 1] }, { rank := 0, op := "OpName.FW_view", ins := [4938], outs := [4939], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [4942], outs := [4943], params := [4096, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7627, 4925, 4926, 4928, 4929], outs := [4930], params := [64, 0, 64, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [4934], outs := [4935] }, { rank := 0, op := "OpName.FW_swiglu", ins := [4939, 4943], outs := [4944] }, { rank := 0, op := "OpName.FW_reshape", ins := [4944], outs := [4945], params := [4096, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4945, 4946], outs := [4947] }, { rank := 0, op := "OpName.FW_view", ins := [4947], outs := [4948], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [4935, 4948], outs := [4949] }, { rank := 0, op := "OpName.FW_add", ins := [4930, 4949], outs := [4950] }, { rank := 0, op := "OpName.FW_float", ins := [4950], outs := [4951] }, { rank := 0, op := "OpName.FW_add", ins := [7616, 4951], outs := [4952] }, { rank := 0, op := "OpName.FW_multiref", ins := [4952], outs := [7643, 7647], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [7643, 4953], outs := [4954] }, { rank := 0, op := "OpName.FW_multiref", ins := [4954], outs := [7652, 7656, 7660], params := [3] }]

theorem smChunk_4_wf : ∀ n ∈ smChunk_4, IsWellFormedNode sm n := by
  intro n hn
  simp only [smChunk_4, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact sm_node_160_wf
  · rw [h1]
    exact sm_node_161_wf
  · rw [h2]
    exact sm_node_162_wf
  · rw [h3]
    exact sm_node_163_wf
  · rw [h4]
    exact sm_node_164_wf
  · rw [h5]
    exact sm_node_165_wf
  · rw [h6]
    exact sm_node_166_wf
  · rw [h7]
    exact sm_node_167_wf
  · rw [h8]
    exact sm_node_168_wf
  · rw [h9]
    exact sm_node_169_wf
  · rw [h10]
    exact sm_node_170_wf
  · rw [h11]
    exact sm_node_171_wf
  · rw [h12]
    exact sm_node_172_wf
  · rw [h13]
    exact sm_node_173_wf
  · rw [h14]
    exact sm_node_174_wf
  · rw [h15]
    exact sm_node_175_wf
  · rw [h16]
    exact sm_node_176_wf
  · rw [h17]
    exact sm_node_177_wf
  · rw [h18]
    exact sm_node_178_wf
  · rw [h19]
    exact sm_node_179_wf
  · rw [h20]
    exact sm_node_180_wf
  · rw [h21]
    exact sm_node_181_wf
  · rw [h22]
    exact sm_node_182_wf
  · rw [h23]
    exact sm_node_183_wf
  · rw [h24]
    exact sm_node_184_wf
  · rw [h25]
    exact sm_node_185_wf
  · rw [h26]
    exact sm_node_186_wf
  · rw [h27]
    exact sm_node_187_wf
  · rw [h28]
    exact sm_node_188_wf
  · rw [h29]
    exact sm_node_189_wf
  · rw [h30]
    exact sm_node_190_wf
  · rw [h31]
    exact sm_node_191_wf
  · rw [h32]
    exact sm_node_192_wf
  · rw [h33]
    exact sm_node_193_wf
  · rw [h34]
    exact sm_node_194_wf
  · rw [h35]
    exact sm_node_195_wf
  · rw [h36]
    exact sm_node_196_wf
  · rw [h37]
    exact sm_node_197_wf
  · rw [h38]
    exact sm_node_198_wf
  · rw [h39]
    exact sm_node_199_wf

def smChunk_5 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7652, 4955], outs := [4956] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7656, 4957], outs := [4958] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7660, 4959], outs := [4960] }, { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4961, 4956, 4958], outs := [4962, 4963], params := [16, 4] }, { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4962, 4963, 4960, 4964, 4965], outs := [4966], params := [16, 4, 64, 64, 1, 512] }, { rank := 0, op := "OpName.FW_reshape", ins := [4966], outs := [4967], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [4967], outs := [4968], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4968, 4969], outs := [4970] }, { rank := 0, op := "OpName.FW_view", ins := [4970], outs := [4971], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [4971], outs := [4972] }, { rank := 0, op := "OpName.FW_add", ins := [7647, 4972], outs := [4973] }, { rank := 0, op := "OpName.FW_multiref", ins := [4973], outs := [7664, 7668], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [7664, 4974], outs := [4975] }, { rank := 0, op := "OpName.FW_multiref", ins := [4975], outs := [7675, 7679, 7683, 7687, 7691], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [7675], outs := [4976] }, { rank := 0, op := "OpName.FW_reshape", ins := [7683], outs := [4985], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7687], outs := [4990], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7691], outs := [4994], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [4976, 4977], outs := [4978] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4985, 4986], outs := [4987] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4990, 4991], outs := [4992] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4994, 4995], outs := [4996] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [4978], outs := [4979, 4980, 4981], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [4987], outs := [4988], params := [4096, 1] }, { rank := 0, op := "OpName.FW_view", ins := [4992], outs := [4993], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [4996], outs := [4997], params := [4096, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7679, 4979, 4980, 4982, 4983], outs := [4984], params := [64, 0, 64, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [4988], outs := [4989] }, { rank := 0, op := "OpName.FW_swiglu", ins := [4993, 4997], outs := [4998] }, { rank := 0, op := "OpName.FW_reshape", ins := [4998], outs := [4999], params := [4096, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4999, 5000], outs := [5001] }, { rank := 0, op := "OpName.FW_view", ins := [5001], outs := [5002], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [4989, 5002], outs := [5003] }, { rank := 0, op := "OpName.FW_add", ins := [4984, 5003], outs := [5004] }, { rank := 0, op := "OpName.FW_float", ins := [5004], outs := [5005] }, { rank := 0, op := "OpName.FW_add", ins := [7668, 5005], outs := [5006] }, { rank := 0, op := "OpName.FW_multiref", ins := [5006], outs := [7695, 7699], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [7695, 5007], outs := [5008] }, { rank := 0, op := "OpName.FW_multiref", ins := [5008], outs := [7704, 7708, 7712], params := [3] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7704, 5009], outs := [5010] }]

theorem smChunk_5_wf : ∀ n ∈ smChunk_5, IsWellFormedNode sm n := by
  intro n hn
  simp only [smChunk_5, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact sm_node_200_wf
  · rw [h1]
    exact sm_node_201_wf
  · rw [h2]
    exact sm_node_202_wf
  · rw [h3]
    exact sm_node_203_wf
  · rw [h4]
    exact sm_node_204_wf
  · rw [h5]
    exact sm_node_205_wf
  · rw [h6]
    exact sm_node_206_wf
  · rw [h7]
    exact sm_node_207_wf
  · rw [h8]
    exact sm_node_208_wf
  · rw [h9]
    exact sm_node_209_wf
  · rw [h10]
    exact sm_node_210_wf
  · rw [h11]
    exact sm_node_211_wf
  · rw [h12]
    exact sm_node_212_wf
  · rw [h13]
    exact sm_node_213_wf
  · rw [h14]
    exact sm_node_214_wf
  · rw [h15]
    exact sm_node_215_wf
  · rw [h16]
    exact sm_node_216_wf
  · rw [h17]
    exact sm_node_217_wf
  · rw [h18]
    exact sm_node_218_wf
  · rw [h19]
    exact sm_node_219_wf
  · rw [h20]
    exact sm_node_220_wf
  · rw [h21]
    exact sm_node_221_wf
  · rw [h22]
    exact sm_node_222_wf
  · rw [h23]
    exact sm_node_223_wf
  · rw [h24]
    exact sm_node_224_wf
  · rw [h25]
    exact sm_node_225_wf
  · rw [h26]
    exact sm_node_226_wf
  · rw [h27]
    exact sm_node_227_wf
  · rw [h28]
    exact sm_node_228_wf
  · rw [h29]
    exact sm_node_229_wf
  · rw [h30]
    exact sm_node_230_wf
  · rw [h31]
    exact sm_node_231_wf
  · rw [h32]
    exact sm_node_232_wf
  · rw [h33]
    exact sm_node_233_wf
  · rw [h34]
    exact sm_node_234_wf
  · rw [h35]
    exact sm_node_235_wf
  · rw [h36]
    exact sm_node_236_wf
  · rw [h37]
    exact sm_node_237_wf
  · rw [h38]
    exact sm_node_238_wf
  · rw [h39]
    exact sm_node_239_wf

def smChunk_6 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7708, 5011], outs := [5012] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7712, 5013], outs := [5014] }, { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5015, 5010, 5012], outs := [5016, 5017], params := [16, 4] }, { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [5016, 5017, 5014, 5018, 5019], outs := [5020], params := [16, 4, 64, 64, 1, 512] }, { rank := 0, op := "OpName.FW_reshape", ins := [5020], outs := [5021], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [5021], outs := [5022], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5022, 5023], outs := [5024] }, { rank := 0, op := "OpName.FW_view", ins := [5024], outs := [5025], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [5025], outs := [5026] }, { rank := 0, op := "OpName.FW_add", ins := [7699, 5026], outs := [5027] }, { rank := 0, op := "OpName.FW_multiref", ins := [5027], outs := [7716, 7720], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [7716, 5028], outs := [5029] }, { rank := 0, op := "OpName.FW_multiref", ins := [5029], outs := [7727, 7731, 7735, 7739, 7743], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [7727], outs := [5030] }, { rank := 0, op := "OpName.FW_reshape", ins := [7735], outs := [5039], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7739], outs := [5044], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7743], outs := [5048], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [5030, 5031], outs := [5032] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5039, 5040], outs := [5041] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5044, 5045], outs := [5046] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5048, 5049], outs := [5050] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [5032], outs := [5033, 5034, 5035], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5041], outs := [5042], params := [4096, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5046], outs := [5047], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [5050], outs := [5051], params := [4096, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7731, 5033, 5034, 5036, 5037], outs := [5038], params := [64, 0, 64, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [5042], outs := [5043] }, { rank := 0, op := "OpName.FW_swiglu", ins := [5047, 5051], outs := [5052] }, { rank := 0, op := "OpName.FW_reshape", ins := [5052], outs := [5053], params := [4096, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5053, 5054], outs := [5055] }, { rank := 0, op := "OpName.FW_view", ins := [5055], outs := [5056], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [5043, 5056], outs := [5057] }, { rank := 0, op := "OpName.FW_add", ins := [5038, 5057], outs := [5058] }, { rank := 0, op := "OpName.FW_float", ins := [5058], outs := [5059] }, { rank := 0, op := "OpName.FW_add", ins := [7720, 5059], outs := [5060] }, { rank := 0, op := "OpName.FW_multiref", ins := [5060], outs := [7747, 7751], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [7747, 5061], outs := [5062] }, { rank := 0, op := "OpName.FW_multiref", ins := [5062], outs := [7756, 7760, 7764], params := [3] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7756, 5063], outs := [5064] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7760, 5065], outs := [5066] }]

theorem smChunk_6_wf : ∀ n ∈ smChunk_6, IsWellFormedNode sm n := by
  intro n hn
  simp only [smChunk_6, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact sm_node_240_wf
  · rw [h1]
    exact sm_node_241_wf
  · rw [h2]
    exact sm_node_242_wf
  · rw [h3]
    exact sm_node_243_wf
  · rw [h4]
    exact sm_node_244_wf
  · rw [h5]
    exact sm_node_245_wf
  · rw [h6]
    exact sm_node_246_wf
  · rw [h7]
    exact sm_node_247_wf
  · rw [h8]
    exact sm_node_248_wf
  · rw [h9]
    exact sm_node_249_wf
  · rw [h10]
    exact sm_node_250_wf
  · rw [h11]
    exact sm_node_251_wf
  · rw [h12]
    exact sm_node_252_wf
  · rw [h13]
    exact sm_node_253_wf
  · rw [h14]
    exact sm_node_254_wf
  · rw [h15]
    exact sm_node_255_wf
  · rw [h16]
    exact sm_node_256_wf
  · rw [h17]
    exact sm_node_257_wf
  · rw [h18]
    exact sm_node_258_wf
  · rw [h19]
    exact sm_node_259_wf
  · rw [h20]
    exact sm_node_260_wf
  · rw [h21]
    exact sm_node_261_wf
  · rw [h22]
    exact sm_node_262_wf
  · rw [h23]
    exact sm_node_263_wf
  · rw [h24]
    exact sm_node_264_wf
  · rw [h25]
    exact sm_node_265_wf
  · rw [h26]
    exact sm_node_266_wf
  · rw [h27]
    exact sm_node_267_wf
  · rw [h28]
    exact sm_node_268_wf
  · rw [h29]
    exact sm_node_269_wf
  · rw [h30]
    exact sm_node_270_wf
  · rw [h31]
    exact sm_node_271_wf
  · rw [h32]
    exact sm_node_272_wf
  · rw [h33]
    exact sm_node_273_wf
  · rw [h34]
    exact sm_node_274_wf
  · rw [h35]
    exact sm_node_275_wf
  · rw [h36]
    exact sm_node_276_wf
  · rw [h37]
    exact sm_node_277_wf
  · rw [h38]
    exact sm_node_278_wf
  · rw [h39]
    exact sm_node_279_wf

def smChunk_7 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7764, 5067], outs := [5068] }, { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5069, 5064, 5066], outs := [5070, 5071], params := [16, 4] }, { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [5070, 5071, 5068, 5072, 5073], outs := [5074], params := [16, 4, 64, 64, 1, 512] }, { rank := 0, op := "OpName.FW_reshape", ins := [5074], outs := [5075], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [5075], outs := [5076], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5076, 5077], outs := [5078] }, { rank := 0, op := "OpName.FW_view", ins := [5078], outs := [5079], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [5079], outs := [5080] }, { rank := 0, op := "OpName.FW_add", ins := [7751, 5080], outs := [5081] }, { rank := 0, op := "OpName.FW_multiref", ins := [5081], outs := [7768, 7772], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [7768, 5082], outs := [5083] }, { rank := 0, op := "OpName.FW_multiref", ins := [5083], outs := [7779, 7783, 7787, 7791, 7795], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [7779], outs := [5084] }, { rank := 0, op := "OpName.FW_reshape", ins := [7787], outs := [5093], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7791], outs := [5098], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7795], outs := [5102], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [5084, 5085], outs := [5086] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5093, 5094], outs := [5095] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5098, 5099], outs := [5100] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5102, 5103], outs := [5104] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [5086], outs := [5087, 5088, 5089], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5095], outs := [5096], params := [4096, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5100], outs := [5101], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [5104], outs := [5105], params := [4096, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7783, 5087, 5088, 5090, 5091], outs := [5092], params := [64, 0, 64, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [5096], outs := [5097] }, { rank := 0, op := "OpName.FW_swiglu", ins := [5101, 5105], outs := [5106] }, { rank := 0, op := "OpName.FW_reshape", ins := [5106], outs := [5107], params := [4096, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5107, 5108], outs := [5109] }, { rank := 0, op := "OpName.FW_view", ins := [5109], outs := [5110], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [5097, 5110], outs := [5111] }, { rank := 0, op := "OpName.FW_add", ins := [5092, 5111], outs := [5112] }, { rank := 0, op := "OpName.FW_float", ins := [5112], outs := [5113] }, { rank := 0, op := "OpName.FW_add", ins := [7772, 5113], outs := [5114] }, { rank := 0, op := "OpName.FW_multiref", ins := [5114], outs := [7799, 7803], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [7799, 5115], outs := [5116] }, { rank := 0, op := "OpName.FW_multiref", ins := [5116], outs := [7808, 7812, 7816], params := [3] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7808, 5117], outs := [5118] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7812, 5119], outs := [5120] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7816, 5121], outs := [5122] }]

theorem smChunk_7_wf : ∀ n ∈ smChunk_7, IsWellFormedNode sm n := by
  intro n hn
  simp only [smChunk_7, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact sm_node_280_wf
  · rw [h1]
    exact sm_node_281_wf
  · rw [h2]
    exact sm_node_282_wf
  · rw [h3]
    exact sm_node_283_wf
  · rw [h4]
    exact sm_node_284_wf
  · rw [h5]
    exact sm_node_285_wf
  · rw [h6]
    exact sm_node_286_wf
  · rw [h7]
    exact sm_node_287_wf
  · rw [h8]
    exact sm_node_288_wf
  · rw [h9]
    exact sm_node_289_wf
  · rw [h10]
    exact sm_node_290_wf
  · rw [h11]
    exact sm_node_291_wf
  · rw [h12]
    exact sm_node_292_wf
  · rw [h13]
    exact sm_node_293_wf
  · rw [h14]
    exact sm_node_294_wf
  · rw [h15]
    exact sm_node_295_wf
  · rw [h16]
    exact sm_node_296_wf
  · rw [h17]
    exact sm_node_297_wf
  · rw [h18]
    exact sm_node_298_wf
  · rw [h19]
    exact sm_node_299_wf
  · rw [h20]
    exact sm_node_300_wf
  · rw [h21]
    exact sm_node_301_wf
  · rw [h22]
    exact sm_node_302_wf
  · rw [h23]
    exact sm_node_303_wf
  · rw [h24]
    exact sm_node_304_wf
  · rw [h25]
    exact sm_node_305_wf
  · rw [h26]
    exact sm_node_306_wf
  · rw [h27]
    exact sm_node_307_wf
  · rw [h28]
    exact sm_node_308_wf
  · rw [h29]
    exact sm_node_309_wf
  · rw [h30]
    exact sm_node_310_wf
  · rw [h31]
    exact sm_node_311_wf
  · rw [h32]
    exact sm_node_312_wf
  · rw [h33]
    exact sm_node_313_wf
  · rw [h34]
    exact sm_node_314_wf
  · rw [h35]
    exact sm_node_315_wf
  · rw [h36]
    exact sm_node_316_wf
  · rw [h37]
    exact sm_node_317_wf
  · rw [h38]
    exact sm_node_318_wf
  · rw [h39]
    exact sm_node_319_wf

def smChunk_8 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5123, 5118, 5120], outs := [5124, 5125], params := [16, 4] }, { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [5124, 5125, 5122, 5126, 5127], outs := [5128], params := [16, 4, 64, 64, 1, 512] }, { rank := 0, op := "OpName.FW_reshape", ins := [5128], outs := [5129], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [5129], outs := [5130], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5130, 5131], outs := [5132] }, { rank := 0, op := "OpName.FW_view", ins := [5132], outs := [5133], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [5133], outs := [5134] }, { rank := 0, op := "OpName.FW_add", ins := [7803, 5134], outs := [5135] }, { rank := 0, op := "OpName.FW_multiref", ins := [5135], outs := [7820, 7824], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [7820, 5136], outs := [5137] }, { rank := 0, op := "OpName.FW_multiref", ins := [5137], outs := [7831, 7835, 7839, 7843, 7847], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [7831], outs := [5138] }, { rank := 0, op := "OpName.FW_reshape", ins := [7839], outs := [5147], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7843], outs := [5152], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7847], outs := [5156], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [5138, 5139], outs := [5140] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5147, 5148], outs := [5149] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5152, 5153], outs := [5154] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5156, 5157], outs := [5158] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [5140], outs := [5141, 5142, 5143], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5149], outs := [5150], params := [4096, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5154], outs := [5155], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [5158], outs := [5159], params := [4096, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7835, 5141, 5142, 5144, 5145], outs := [5146], params := [64, 0, 64, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [5150], outs := [5151] }, { rank := 0, op := "OpName.FW_swiglu", ins := [5155, 5159], outs := [5160] }, { rank := 0, op := "OpName.FW_reshape", ins := [5160], outs := [5161], params := [4096, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5161, 5162], outs := [5163] }, { rank := 0, op := "OpName.FW_view", ins := [5163], outs := [5164], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [5151, 5164], outs := [5165] }, { rank := 0, op := "OpName.FW_add", ins := [5146, 5165], outs := [5166] }, { rank := 0, op := "OpName.FW_float", ins := [5166], outs := [5167] }, { rank := 0, op := "OpName.FW_add", ins := [7824, 5167], outs := [5168] }, { rank := 0, op := "OpName.FW_multiref", ins := [5168], outs := [7851, 7855], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [7851, 5169], outs := [5170] }, { rank := 0, op := "OpName.FW_multiref", ins := [5170], outs := [7860, 7864, 7868], params := [3] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7860, 5171], outs := [5172] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7864, 5173], outs := [5174] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7868, 5175], outs := [5176] }, { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5177, 5172, 5174], outs := [5178, 5179], params := [16, 4] }]

theorem smChunk_8_wf : ∀ n ∈ smChunk_8, IsWellFormedNode sm n := by
  intro n hn
  simp only [smChunk_8, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact sm_node_320_wf
  · rw [h1]
    exact sm_node_321_wf
  · rw [h2]
    exact sm_node_322_wf
  · rw [h3]
    exact sm_node_323_wf
  · rw [h4]
    exact sm_node_324_wf
  · rw [h5]
    exact sm_node_325_wf
  · rw [h6]
    exact sm_node_326_wf
  · rw [h7]
    exact sm_node_327_wf
  · rw [h8]
    exact sm_node_328_wf
  · rw [h9]
    exact sm_node_329_wf
  · rw [h10]
    exact sm_node_330_wf
  · rw [h11]
    exact sm_node_331_wf
  · rw [h12]
    exact sm_node_332_wf
  · rw [h13]
    exact sm_node_333_wf
  · rw [h14]
    exact sm_node_334_wf
  · rw [h15]
    exact sm_node_335_wf
  · rw [h16]
    exact sm_node_336_wf
  · rw [h17]
    exact sm_node_337_wf
  · rw [h18]
    exact sm_node_338_wf
  · rw [h19]
    exact sm_node_339_wf
  · rw [h20]
    exact sm_node_340_wf
  · rw [h21]
    exact sm_node_341_wf
  · rw [h22]
    exact sm_node_342_wf
  · rw [h23]
    exact sm_node_343_wf
  · rw [h24]
    exact sm_node_344_wf
  · rw [h25]
    exact sm_node_345_wf
  · rw [h26]
    exact sm_node_346_wf
  · rw [h27]
    exact sm_node_347_wf
  · rw [h28]
    exact sm_node_348_wf
  · rw [h29]
    exact sm_node_349_wf
  · rw [h30]
    exact sm_node_350_wf
  · rw [h31]
    exact sm_node_351_wf
  · rw [h32]
    exact sm_node_352_wf
  · rw [h33]
    exact sm_node_353_wf
  · rw [h34]
    exact sm_node_354_wf
  · rw [h35]
    exact sm_node_355_wf
  · rw [h36]
    exact sm_node_356_wf
  · rw [h37]
    exact sm_node_357_wf
  · rw [h38]
    exact sm_node_358_wf
  · rw [h39]
    exact sm_node_359_wf

def smChunk_9 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_attn_sliding_window", ins := [5178, 5179, 5176, 5180, 5181], outs := [5182], params := [16, 4, 64, 64, 1, 512] }, { rank := 0, op := "OpName.FW_reshape", ins := [5182], outs := [5183], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [5183], outs := [5184], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5184, 5185], outs := [5186] }, { rank := 0, op := "OpName.FW_view", ins := [5186], outs := [5187], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [5187], outs := [5188] }, { rank := 0, op := "OpName.FW_add", ins := [7855, 5188], outs := [5189] }, { rank := 0, op := "OpName.FW_multiref", ins := [5189], outs := [7872, 7876], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [7872, 5190], outs := [5191] }, { rank := 0, op := "OpName.FW_multiref", ins := [5191], outs := [7883, 7887, 7891, 7895, 7899], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [7883], outs := [5192] }, { rank := 0, op := "OpName.FW_reshape", ins := [7891], outs := [5201], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7895], outs := [5206], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7899], outs := [5210], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [5192, 5193], outs := [5194] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5201, 5202], outs := [5203] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5206, 5207], outs := [5208] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5210, 5211], outs := [5212] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [5194], outs := [5195, 5196, 5197], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5203], outs := [5204], params := [4096, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5208], outs := [5209], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [5212], outs := [5213], params := [4096, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7887, 5195, 5196, 5198, 5199], outs := [5200], params := [64, 0, 64, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [5204], outs := [5205] }, { rank := 0, op := "OpName.FW_swiglu", ins := [5209, 5213], outs := [5214] }, { rank := 0, op := "OpName.FW_reshape", ins := [5214], outs := [5215], params := [4096, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5215, 5216], outs := [5217] }, { rank := 0, op := "OpName.FW_view", ins := [5217], outs := [5218], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [5205, 5218], outs := [5219] }, { rank := 0, op := "OpName.FW_add", ins := [5200, 5219], outs := [5220] }, { rank := 0, op := "OpName.FW_float", ins := [5220], outs := [5221] }, { rank := 0, op := "OpName.FW_add", ins := [7876, 5221], outs := [5222] }, { rank := 0, op := "OpName.FW_multiref", ins := [5222], outs := [7903, 7907], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [7903, 5223], outs := [5224] }, { rank := 0, op := "OpName.FW_multiref", ins := [5224], outs := [7912, 7916, 7920], params := [3] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7912, 5225], outs := [5226] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7916, 5227], outs := [5228] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7920, 5229], outs := [5230] }, { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5231, 5226, 5228], outs := [5232, 5233], params := [16, 4] }, { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [5232, 5233, 5230, 5234, 5235], outs := [5236], params := [16, 4, 64, 64, 1, 512] }]

theorem smChunk_9_wf : ∀ n ∈ smChunk_9, IsWellFormedNode sm n := by
  intro n hn
  simp only [smChunk_9, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact sm_node_360_wf
  · rw [h1]
    exact sm_node_361_wf
  · rw [h2]
    exact sm_node_362_wf
  · rw [h3]
    exact sm_node_363_wf
  · rw [h4]
    exact sm_node_364_wf
  · rw [h5]
    exact sm_node_365_wf
  · rw [h6]
    exact sm_node_366_wf
  · rw [h7]
    exact sm_node_367_wf
  · rw [h8]
    exact sm_node_368_wf
  · rw [h9]
    exact sm_node_369_wf
  · rw [h10]
    exact sm_node_370_wf
  · rw [h11]
    exact sm_node_371_wf
  · rw [h12]
    exact sm_node_372_wf
  · rw [h13]
    exact sm_node_373_wf
  · rw [h14]
    exact sm_node_374_wf
  · rw [h15]
    exact sm_node_375_wf
  · rw [h16]
    exact sm_node_376_wf
  · rw [h17]
    exact sm_node_377_wf
  · rw [h18]
    exact sm_node_378_wf
  · rw [h19]
    exact sm_node_379_wf
  · rw [h20]
    exact sm_node_380_wf
  · rw [h21]
    exact sm_node_381_wf
  · rw [h22]
    exact sm_node_382_wf
  · rw [h23]
    exact sm_node_383_wf
  · rw [h24]
    exact sm_node_384_wf
  · rw [h25]
    exact sm_node_385_wf
  · rw [h26]
    exact sm_node_386_wf
  · rw [h27]
    exact sm_node_387_wf
  · rw [h28]
    exact sm_node_388_wf
  · rw [h29]
    exact sm_node_389_wf
  · rw [h30]
    exact sm_node_390_wf
  · rw [h31]
    exact sm_node_391_wf
  · rw [h32]
    exact sm_node_392_wf
  · rw [h33]
    exact sm_node_393_wf
  · rw [h34]
    exact sm_node_394_wf
  · rw [h35]
    exact sm_node_395_wf
  · rw [h36]
    exact sm_node_396_wf
  · rw [h37]
    exact sm_node_397_wf
  · rw [h38]
    exact sm_node_398_wf
  · rw [h39]
    exact sm_node_399_wf

def smChunk_10 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_reshape", ins := [5236], outs := [5237], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [5237], outs := [5238], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5238, 5239], outs := [5240] }, { rank := 0, op := "OpName.FW_view", ins := [5240], outs := [5241], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [5241], outs := [5242] }, { rank := 0, op := "OpName.FW_add", ins := [7907, 5242], outs := [5243] }, { rank := 0, op := "OpName.FW_multiref", ins := [5243], outs := [7924, 7928], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [7924, 5244], outs := [5245] }, { rank := 0, op := "OpName.FW_multiref", ins := [5245], outs := [7935, 7939, 7943, 7947, 7951], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [7935], outs := [5246] }, { rank := 0, op := "OpName.FW_reshape", ins := [7943], outs := [5255], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7947], outs := [5260], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7951], outs := [5264], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [5246, 5247], outs := [5248] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5255, 5256], outs := [5257] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5260, 5261], outs := [5262] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5264, 5265], outs := [5266] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [5248], outs := [5249, 5250, 5251], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5257], outs := [5258], params := [4096, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5262], outs := [5263], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [5266], outs := [5267], params := [4096, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7939, 5249, 5250, 5252, 5253], outs := [5254], params := [64, 0, 64, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [5258], outs := [5259] }, { rank := 0, op := "OpName.FW_swiglu", ins := [5263, 5267], outs := [5268] }, { rank := 0, op := "OpName.FW_reshape", ins := [5268], outs := [5269], params := [4096, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5269, 5270], outs := [5271] }, { rank := 0, op := "OpName.FW_view", ins := [5271], outs := [5272], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [5259, 5272], outs := [5273] }, { rank := 0, op := "OpName.FW_add", ins := [5254, 5273], outs := [5274] }, { rank := 0, op := "OpName.FW_float", ins := [5274], outs := [5275] }, { rank := 0, op := "OpName.FW_add", ins := [7928, 5275], outs := [5276] }, { rank := 0, op := "OpName.FW_multiref", ins := [5276], outs := [7955, 7959], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [7955, 5277], outs := [5278] }, { rank := 0, op := "OpName.FW_multiref", ins := [5278], outs := [7964, 7968, 7972], params := [3] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7964, 5279], outs := [5280] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7968, 5281], outs := [5282] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7972, 5283], outs := [5284] }, { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5285, 5280, 5282], outs := [5286, 5287], params := [16, 4] }, { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [5286, 5287, 5284, 5288, 5289], outs := [5290], params := [16, 4, 64, 64, 1, 512] }, { rank := 0, op := "OpName.FW_reshape", ins := [5290], outs := [5291], params := [4096, 1024] }]

theorem smChunk_10_wf : ∀ n ∈ smChunk_10, IsWellFormedNode sm n := by
  intro n hn
  simp only [smChunk_10, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact sm_node_400_wf
  · rw [h1]
    exact sm_node_401_wf
  · rw [h2]
    exact sm_node_402_wf
  · rw [h3]
    exact sm_node_403_wf
  · rw [h4]
    exact sm_node_404_wf
  · rw [h5]
    exact sm_node_405_wf
  · rw [h6]
    exact sm_node_406_wf
  · rw [h7]
    exact sm_node_407_wf
  · rw [h8]
    exact sm_node_408_wf
  · rw [h9]
    exact sm_node_409_wf
  · rw [h10]
    exact sm_node_410_wf
  · rw [h11]
    exact sm_node_411_wf
  · rw [h12]
    exact sm_node_412_wf
  · rw [h13]
    exact sm_node_413_wf
  · rw [h14]
    exact sm_node_414_wf
  · rw [h15]
    exact sm_node_415_wf
  · rw [h16]
    exact sm_node_416_wf
  · rw [h17]
    exact sm_node_417_wf
  · rw [h18]
    exact sm_node_418_wf
  · rw [h19]
    exact sm_node_419_wf
  · rw [h20]
    exact sm_node_420_wf
  · rw [h21]
    exact sm_node_421_wf
  · rw [h22]
    exact sm_node_422_wf
  · rw [h23]
    exact sm_node_423_wf
  · rw [h24]
    exact sm_node_424_wf
  · rw [h25]
    exact sm_node_425_wf
  · rw [h26]
    exact sm_node_426_wf
  · rw [h27]
    exact sm_node_427_wf
  · rw [h28]
    exact sm_node_428_wf
  · rw [h29]
    exact sm_node_429_wf
  · rw [h30]
    exact sm_node_430_wf
  · rw [h31]
    exact sm_node_431_wf
  · rw [h32]
    exact sm_node_432_wf
  · rw [h33]
    exact sm_node_433_wf
  · rw [h34]
    exact sm_node_434_wf
  · rw [h35]
    exact sm_node_435_wf
  · rw [h36]
    exact sm_node_436_wf
  · rw [h37]
    exact sm_node_437_wf
  · rw [h38]
    exact sm_node_438_wf
  · rw [h39]
    exact sm_node_439_wf

def smChunk_11 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_reshape", ins := [5291], outs := [5292], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5292, 5293], outs := [5294] }, { rank := 0, op := "OpName.FW_view", ins := [5294], outs := [5295], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [5295], outs := [5296] }, { rank := 0, op := "OpName.FW_add", ins := [7959, 5296], outs := [5297] }, { rank := 0, op := "OpName.FW_multiref", ins := [5297], outs := [7976, 7980], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [7976, 5298], outs := [5299] }, { rank := 0, op := "OpName.FW_multiref", ins := [5299], outs := [7987, 7991, 7995, 7999, 8003], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [7987], outs := [5300] }, { rank := 0, op := "OpName.FW_reshape", ins := [7995], outs := [5309], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7999], outs := [5314], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8003], outs := [5318], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [5300, 5301], outs := [5302] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5309, 5310], outs := [5311] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5314, 5315], outs := [5316] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5318, 5319], outs := [5320] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [5302], outs := [5303, 5304, 5305], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5311], outs := [5312], params := [4096, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5316], outs := [5317], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [5320], outs := [5321], params := [4096, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7991, 5303, 5304, 5306, 5307], outs := [5308], params := [64, 0, 64, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [5312], outs := [5313] }, { rank := 0, op := "OpName.FW_swiglu", ins := [5317, 5321], outs := [5322] }, { rank := 0, op := "OpName.FW_reshape", ins := [5322], outs := [5323], params := [4096, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5323, 5324], outs := [5325] }, { rank := 0, op := "OpName.FW_view", ins := [5325], outs := [5326], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [5313, 5326], outs := [5327] }, { rank := 0, op := "OpName.FW_add", ins := [5308, 5327], outs := [5328] }, { rank := 0, op := "OpName.FW_float", ins := [5328], outs := [5329] }, { rank := 0, op := "OpName.FW_add", ins := [7980, 5329], outs := [5330] }, { rank := 0, op := "OpName.FW_multiref", ins := [5330], outs := [8007, 8011], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8007, 5331], outs := [5332] }, { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [8011, 5337], outs := [5338], params := [1, 0] }, { rank := 0, op := "OpName.FW_multiref", ins := [5332], outs := [8015, 8019], params := [2] }, { rank := 0, op := "OpName.FW_multiref", ins := [5338], outs := [8139, 8143], params := [2] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [8015, 5333], outs := [5334] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [8019, 5335], outs := [5336] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8139, 5339], outs := [5340] }, { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] }, { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] }]

theorem smChunk_11_wf : ∀ n ∈ smChunk_11, IsWellFormedNode sm n := by
  intro n hn
  simp only [smChunk_11, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact sm_node_440_wf
  · rw [h1]
    exact sm_node_441_wf
  · rw [h2]
    exact sm_node_442_wf
  · rw [h3]
    exact sm_node_443_wf
  · rw [h4]
    exact sm_node_444_wf
  · rw [h5]
    exact sm_node_445_wf
  · rw [h6]
    exact sm_node_446_wf
  · rw [h7]
    exact sm_node_447_wf
  · rw [h8]
    exact sm_node_448_wf
  · rw [h9]
    exact sm_node_449_wf
  · rw [h10]
    exact sm_node_450_wf
  · rw [h11]
    exact sm_node_451_wf
  · rw [h12]
    exact sm_node_452_wf
  · rw [h13]
    exact sm_node_453_wf
  · rw [h14]
    exact sm_node_454_wf
  · rw [h15]
    exact sm_node_455_wf
  · rw [h16]
    exact sm_node_456_wf
  · rw [h17]
    exact sm_node_457_wf
  · rw [h18]
    exact sm_node_458_wf
  · rw [h19]
    exact sm_node_459_wf
  · rw [h20]
    exact sm_node_460_wf
  · rw [h21]
    exact sm_node_461_wf
  · rw [h22]
    exact sm_node_462_wf
  · rw [h23]
    exact sm_node_463_wf
  · rw [h24]
    exact sm_node_464_wf
  · rw [h25]
    exact sm_node_465_wf
  · rw [h26]
    exact sm_node_466_wf
  · rw [h27]
    exact sm_node_467_wf
  · rw [h28]
    exact sm_node_468_wf
  · rw [h29]
    exact sm_node_469_wf
  · rw [h30]
    exact sm_node_470_wf
  · rw [h31]
    exact sm_node_471_wf
  · rw [h32]
    exact sm_node_472_wf
  · rw [h33]
    exact sm_node_473_wf
  · rw [h34]
    exact sm_node_474_wf
  · rw [h35]
    exact sm_node_475_wf
  · rw [h36]
    exact sm_node_476_wf
  · rw [h37]
    exact sm_node_477_wf
  · rw [h38]
    exact sm_node_478_wf
  · rw [h39]
    exact sm_node_479_wf

def smChunk_12 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5340, 5341], outs := [5342] }, { rank := 0, op := "OpName.FW_to", ins := [8033], outs := [5343] }, { rank := 0, op := "OpName.FW_to", ins := [8037], outs := [5392] }, { rank := 0, op := "OpName.FW_to", ins := [8041], outs := [5441] }, { rank := 0, op := "OpName.FW_to", ins := [8045], outs := [5490] }, { rank := 0, op := "OpName.FW_to", ins := [8049], outs := [5539] }, { rank := 0, op := "OpName.FW_to", ins := [8053], outs := [5588] }, { rank := 0, op := "OpName.FW_to", ins := [8057], outs := [5637] }, { rank := 0, op := "OpName.FW_to", ins := [8061], outs := [5686] }, { rank := 0, op := "OpName.FW_to", ins := [8065], outs := [5735] }, { rank := 0, op := "OpName.FW_to", ins := [8069], outs := [5784] }, { rank := 0, op := "OpName.FW_to", ins := [8073], outs := [5833] }, { rank := 0, op := "OpName.FW_to", ins := [8077], outs := [5882] }, { rank := 0, op := "OpName.FW_to", ins := [8091], outs := [5344] }, { rank := 0, op := "OpName.FW_to", ins := [8095], outs := [5393] }, { rank := 0, op := "OpName.FW_to", ins := [8099], outs := [5442] }, { rank := 0, op := "OpName.FW_to", ins := [8103], outs := [5491] }, { rank := 0, op := "OpName.FW_to", ins := [8107], outs := [5540] }, { rank := 0, op := "OpName.FW_to", ins := [8111], outs := [5589] }, { rank := 0, op := "OpName.FW_to", ins := [8115], outs := [5638] }, { rank := 0, op := "OpName.FW_to", ins := [8119], outs := [5687] }, { rank := 0, op := "OpName.FW_to", ins := [8123], outs := [5736] }, { rank := 0, op := "OpName.FW_to", ins := [8127], outs := [5785] }, { rank := 0, op := "OpName.FW_to", ins := [8131], outs := [5834] }, { rank := 0, op := "OpName.FW_to", ins := [8135], outs := [5883] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := ((List.range 5).map (fun r => 5342 + r)), outs := [5347], params := [16, 4, 64, 64, 1, 0] }, { rank := 0, op := "OpName.FW_reshape", ins := [5347], outs := [5348], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [5348], outs := [5349], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5349, 5350], outs := [5351] }, { rank := 0, op := "OpName.FW_view", ins := [5351], outs := [5352], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [5352], outs := [5353] }, { rank := 0, op := "OpName.FW_add", ins := [8143, 5353], outs := [5354] }, { rank := 0, op := "OpName.FW_multiref", ins := [5354], outs := [8147, 8151], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8147, 5355], outs := [5356] }, { rank := 0, op := "OpName.FW_multiref", ins := [5356], outs := [8158, 8162, 8166, 8170, 8174], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [8158], outs := [5357] }, { rank := 0, op := "OpName.FW_reshape", ins := [8166], outs := [5366], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8170], outs := [5371], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8174], outs := [5375], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [5357, 5358], outs := [5359] }]

theorem smChunk_12_wf : ∀ n ∈ smChunk_12, IsWellFormedNode sm n := by
  intro n hn
  simp only [smChunk_12, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact sm_node_480_wf
  · rw [h1]
    exact sm_node_481_wf
  · rw [h2]
    exact sm_node_482_wf
  · rw [h3]
    exact sm_node_483_wf
  · rw [h4]
    exact sm_node_484_wf
  · rw [h5]
    exact sm_node_485_wf
  · rw [h6]
    exact sm_node_486_wf
  · rw [h7]
    exact sm_node_487_wf
  · rw [h8]
    exact sm_node_488_wf
  · rw [h9]
    exact sm_node_489_wf
  · rw [h10]
    exact sm_node_490_wf
  · rw [h11]
    exact sm_node_491_wf
  · rw [h12]
    exact sm_node_492_wf
  · rw [h13]
    exact sm_node_493_wf
  · rw [h14]
    exact sm_node_494_wf
  · rw [h15]
    exact sm_node_495_wf
  · rw [h16]
    exact sm_node_496_wf
  · rw [h17]
    exact sm_node_497_wf
  · rw [h18]
    exact sm_node_498_wf
  · rw [h19]
    exact sm_node_499_wf
  · rw [h20]
    exact sm_node_500_wf
  · rw [h21]
    exact sm_node_501_wf
  · rw [h22]
    exact sm_node_502_wf
  · rw [h23]
    exact sm_node_503_wf
  · rw [h24]
    exact sm_node_504_wf
  · rw [h25]
    exact sm_node_505_wf
  · rw [h26]
    exact sm_node_506_wf
  · rw [h27]
    exact sm_node_507_wf
  · rw [h28]
    exact sm_node_508_wf
  · rw [h29]
    exact sm_node_509_wf
  · rw [h30]
    exact sm_node_510_wf
  · rw [h31]
    exact sm_node_511_wf
  · rw [h32]
    exact sm_node_512_wf
  · rw [h33]
    exact sm_node_513_wf
  · rw [h34]
    exact sm_node_514_wf
  · rw [h35]
    exact sm_node_515_wf
  · rw [h36]
    exact sm_node_516_wf
  · rw [h37]
    exact sm_node_517_wf
  · rw [h38]
    exact sm_node_518_wf
  · rw [h39]
    exact sm_node_519_wf

def smChunk_13 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5366, 5367], outs := [5368] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5371, 5372], outs := [5373] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5375, 5376], outs := [5377] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [5359], outs := [5360, 5361, 5362], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5368], outs := [5369], params := [4096, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5373], outs := [5374], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [5377], outs := [5378], params := [4096, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8162, 5360, 5361, 5363, 5364], outs := [5365], params := [64, 0, 64, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [5369], outs := [5370] }, { rank := 0, op := "OpName.FW_swiglu", ins := [5374, 5378], outs := [5379] }, { rank := 0, op := "OpName.FW_reshape", ins := [5379], outs := [5380], params := [4096, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5380, 5381], outs := [5382] }, { rank := 0, op := "OpName.FW_view", ins := [5382], outs := [5383], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [5370, 5383], outs := [5384] }, { rank := 0, op := "OpName.FW_add", ins := [5365, 5384], outs := [5385] }, { rank := 0, op := "OpName.FW_float", ins := [5385], outs := [5386] }, { rank := 0, op := "OpName.FW_add", ins := [8151, 5386], outs := [5387] }, { rank := 0, op := "OpName.FW_multiref", ins := [5387], outs := [8178, 8182], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8178, 5388], outs := [5389] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5389, 5390], outs := [5391] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := ((List.range 5).map (fun r => 5391 + r)), outs := [5396], params := [16, 4, 64, 64, 1, 0] }, { rank := 0, op := "OpName.FW_reshape", ins := [5396], outs := [5397], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [5397], outs := [5398], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5398, 5399], outs := [5400] }, { rank := 0, op := "OpName.FW_view", ins := [5400], outs := [5401], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [5401], outs := [5402] }, { rank := 0, op := "OpName.FW_add", ins := [8182, 5402], outs := [5403] }, { rank := 0, op := "OpName.FW_multiref", ins := [5403], outs := [8186, 8190], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8186, 5404], outs := [5405] }, { rank := 0, op := "OpName.FW_multiref", ins := [5405], outs := [8197, 8201, 8205, 8209, 8213], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [8197], outs := [5406] }, { rank := 0, op := "OpName.FW_reshape", ins := [8205], outs := [5415], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8209], outs := [5420], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8213], outs := [5424], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [5406, 5407], outs := [5408] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5415, 5416], outs := [5417] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5420, 5421], outs := [5422] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5424, 5425], outs := [5426] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [5408], outs := [5409, 5410, 5411], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5417], outs := [5418], params := [4096, 1] }]

theorem smChunk_13_wf : ∀ n ∈ smChunk_13, IsWellFormedNode sm n := by
  intro n hn
  simp only [smChunk_13, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact sm_node_520_wf
  · rw [h1]
    exact sm_node_521_wf
  · rw [h2]
    exact sm_node_522_wf
  · rw [h3]
    exact sm_node_523_wf
  · rw [h4]
    exact sm_node_524_wf
  · rw [h5]
    exact sm_node_525_wf
  · rw [h6]
    exact sm_node_526_wf
  · rw [h7]
    exact sm_node_527_wf
  · rw [h8]
    exact sm_node_528_wf
  · rw [h9]
    exact sm_node_529_wf
  · rw [h10]
    exact sm_node_530_wf
  · rw [h11]
    exact sm_node_531_wf
  · rw [h12]
    exact sm_node_532_wf
  · rw [h13]
    exact sm_node_533_wf
  · rw [h14]
    exact sm_node_534_wf
  · rw [h15]
    exact sm_node_535_wf
  · rw [h16]
    exact sm_node_536_wf
  · rw [h17]
    exact sm_node_537_wf
  · rw [h18]
    exact sm_node_538_wf
  · rw [h19]
    exact sm_node_539_wf
  · rw [h20]
    exact sm_node_540_wf
  · rw [h21]
    exact sm_node_541_wf
  · rw [h22]
    exact sm_node_542_wf
  · rw [h23]
    exact sm_node_543_wf
  · rw [h24]
    exact sm_node_544_wf
  · rw [h25]
    exact sm_node_545_wf
  · rw [h26]
    exact sm_node_546_wf
  · rw [h27]
    exact sm_node_547_wf
  · rw [h28]
    exact sm_node_548_wf
  · rw [h29]
    exact sm_node_549_wf
  · rw [h30]
    exact sm_node_550_wf
  · rw [h31]
    exact sm_node_551_wf
  · rw [h32]
    exact sm_node_552_wf
  · rw [h33]
    exact sm_node_553_wf
  · rw [h34]
    exact sm_node_554_wf
  · rw [h35]
    exact sm_node_555_wf
  · rw [h36]
    exact sm_node_556_wf
  · rw [h37]
    exact sm_node_557_wf
  · rw [h38]
    exact sm_node_558_wf
  · rw [h39]
    exact sm_node_559_wf

def smChunk_14 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_view", ins := [5422], outs := [5423], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [5426], outs := [5427], params := [4096, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8201, 5409, 5410, 5412, 5413], outs := [5414], params := [64, 0, 64, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [5418], outs := [5419] }, { rank := 0, op := "OpName.FW_swiglu", ins := [5423, 5427], outs := [5428] }, { rank := 0, op := "OpName.FW_reshape", ins := [5428], outs := [5429], params := [4096, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5429, 5430], outs := [5431] }, { rank := 0, op := "OpName.FW_view", ins := [5431], outs := [5432], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [5419, 5432], outs := [5433] }, { rank := 0, op := "OpName.FW_add", ins := [5414, 5433], outs := [5434] }, { rank := 0, op := "OpName.FW_float", ins := [5434], outs := [5435] }, { rank := 0, op := "OpName.FW_add", ins := [8190, 5435], outs := [5436] }, { rank := 0, op := "OpName.FW_multiref", ins := [5436], outs := [8217, 8221], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8217, 5437], outs := [5438] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5438, 5439], outs := [5440] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := ((List.range 5).map (fun r => 5440 + r)), outs := [5445], params := [16, 4, 64, 64, 1, 0] }, { rank := 0, op := "OpName.FW_reshape", ins := [5445], outs := [5446], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [5446], outs := [5447], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5447, 5448], outs := [5449] }, { rank := 0, op := "OpName.FW_view", ins := [5449], outs := [5450], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [5450], outs := [5451] }, { rank := 0, op := "OpName.FW_add", ins := [8221, 5451], outs := [5452] }, { rank := 0, op := "OpName.FW_multiref", ins := [5452], outs := [8225, 8229], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8225, 5453], outs := [5454] }, { rank := 0, op := "OpName.FW_multiref", ins := [5454], outs := [8236, 8240, 8244, 8248, 8252], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [8236], outs := [5455] }, { rank := 0, op := "OpName.FW_reshape", ins := [8244], outs := [5464], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8248], outs := [5469], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8252], outs := [5473], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [5455, 5456], outs := [5457] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5464, 5465], outs := [5466] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5469, 5470], outs := [5471] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5473, 5474], outs := [5475] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [5457], outs := [5458, 5459, 5460], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5466], outs := [5467], params := [4096, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5471], outs := [5472], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [5475], outs := [5476], params := [4096, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8240, 5458, 5459, 5461, 5462], outs := [5463], params := [64, 0, 64, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [5467], outs := [5468] }, { rank := 0, op := "OpName.FW_swiglu", ins := [5472, 5476], outs := [5477] }]

theorem smChunk_14_wf : ∀ n ∈ smChunk_14, IsWellFormedNode sm n := by
  intro n hn
  simp only [smChunk_14, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact sm_node_560_wf
  · rw [h1]
    exact sm_node_561_wf
  · rw [h2]
    exact sm_node_562_wf
  · rw [h3]
    exact sm_node_563_wf
  · rw [h4]
    exact sm_node_564_wf
  · rw [h5]
    exact sm_node_565_wf
  · rw [h6]
    exact sm_node_566_wf
  · rw [h7]
    exact sm_node_567_wf
  · rw [h8]
    exact sm_node_568_wf
  · rw [h9]
    exact sm_node_569_wf
  · rw [h10]
    exact sm_node_570_wf
  · rw [h11]
    exact sm_node_571_wf
  · rw [h12]
    exact sm_node_572_wf
  · rw [h13]
    exact sm_node_573_wf
  · rw [h14]
    exact sm_node_574_wf
  · rw [h15]
    exact sm_node_575_wf
  · rw [h16]
    exact sm_node_576_wf
  · rw [h17]
    exact sm_node_577_wf
  · rw [h18]
    exact sm_node_578_wf
  · rw [h19]
    exact sm_node_579_wf
  · rw [h20]
    exact sm_node_580_wf
  · rw [h21]
    exact sm_node_581_wf
  · rw [h22]
    exact sm_node_582_wf
  · rw [h23]
    exact sm_node_583_wf
  · rw [h24]
    exact sm_node_584_wf
  · rw [h25]
    exact sm_node_585_wf
  · rw [h26]
    exact sm_node_586_wf
  · rw [h27]
    exact sm_node_587_wf
  · rw [h28]
    exact sm_node_588_wf
  · rw [h29]
    exact sm_node_589_wf
  · rw [h30]
    exact sm_node_590_wf
  · rw [h31]
    exact sm_node_591_wf
  · rw [h32]
    exact sm_node_592_wf
  · rw [h33]
    exact sm_node_593_wf
  · rw [h34]
    exact sm_node_594_wf
  · rw [h35]
    exact sm_node_595_wf
  · rw [h36]
    exact sm_node_596_wf
  · rw [h37]
    exact sm_node_597_wf
  · rw [h38]
    exact sm_node_598_wf
  · rw [h39]
    exact sm_node_599_wf

def smChunk_15 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_reshape", ins := [5477], outs := [5478], params := [4096, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5478, 5479], outs := [5480] }, { rank := 0, op := "OpName.FW_view", ins := [5480], outs := [5481], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [5468, 5481], outs := [5482] }, { rank := 0, op := "OpName.FW_add", ins := [5463, 5482], outs := [5483] }, { rank := 0, op := "OpName.FW_float", ins := [5483], outs := [5484] }, { rank := 0, op := "OpName.FW_add", ins := [8229, 5484], outs := [5485] }, { rank := 0, op := "OpName.FW_multiref", ins := [5485], outs := [8256, 8260], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8256, 5486], outs := [5487] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5487, 5488], outs := [5489] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := ((List.range 5).map (fun r => 5489 + r)), outs := [5494], params := [16, 4, 64, 64, 1, 0] }, { rank := 0, op := "OpName.FW_reshape", ins := [5494], outs := [5495], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [5495], outs := [5496], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5496, 5497], outs := [5498] }, { rank := 0, op := "OpName.FW_view", ins := [5498], outs := [5499], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [5499], outs := [5500] }, { rank := 0, op := "OpName.FW_add", ins := [8260, 5500], outs := [5501] }, { rank := 0, op := "OpName.FW_multiref", ins := [5501], outs := [8264, 8268], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8264, 5502], outs := [5503] }, { rank := 0, op := "OpName.FW_multiref", ins := [5503], outs := [8275, 8279, 8283, 8287, 8291], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [8275], outs := [5504] }, { rank := 0, op := "OpName.FW_reshape", ins := [8283], outs := [5513], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8287], outs := [5518], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8291], outs := [5522], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [5504, 5505], outs := [5506] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5513, 5514], outs := [5515] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5518, 5519], outs := [5520] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5522, 5523], outs := [5524] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [5506], outs := [5507, 5508, 5509], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5515], outs := [5516], params := [4096, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5520], outs := [5521], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [5524], outs := [5525], params := [4096, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8279, 5507, 5508, 5510, 5511], outs := [5512], params := [64, 0, 64, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [5516], outs := [5517] }, { rank := 0, op := "OpName.FW_swiglu", ins := [5521, 5525], outs := [5526] }, { rank := 0, op := "OpName.FW_reshape", ins := [5526], outs := [5527], params := [4096, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5527, 5528], outs := [5529] }, { rank := 0, op := "OpName.FW_view", ins := [5529], outs := [5530], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [5517, 5530], outs := [5531] }, { rank := 0, op := "OpName.FW_add", ins := [5512, 5531], outs := [5532] }]

theorem smChunk_15_wf : ∀ n ∈ smChunk_15, IsWellFormedNode sm n := by
  intro n hn
  simp only [smChunk_15, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact sm_node_600_wf
  · rw [h1]
    exact sm_node_601_wf
  · rw [h2]
    exact sm_node_602_wf
  · rw [h3]
    exact sm_node_603_wf
  · rw [h4]
    exact sm_node_604_wf
  · rw [h5]
    exact sm_node_605_wf
  · rw [h6]
    exact sm_node_606_wf
  · rw [h7]
    exact sm_node_607_wf
  · rw [h8]
    exact sm_node_608_wf
  · rw [h9]
    exact sm_node_609_wf
  · rw [h10]
    exact sm_node_610_wf
  · rw [h11]
    exact sm_node_611_wf
  · rw [h12]
    exact sm_node_612_wf
  · rw [h13]
    exact sm_node_613_wf
  · rw [h14]
    exact sm_node_614_wf
  · rw [h15]
    exact sm_node_615_wf
  · rw [h16]
    exact sm_node_616_wf
  · rw [h17]
    exact sm_node_617_wf
  · rw [h18]
    exact sm_node_618_wf
  · rw [h19]
    exact sm_node_619_wf
  · rw [h20]
    exact sm_node_620_wf
  · rw [h21]
    exact sm_node_621_wf
  · rw [h22]
    exact sm_node_622_wf
  · rw [h23]
    exact sm_node_623_wf
  · rw [h24]
    exact sm_node_624_wf
  · rw [h25]
    exact sm_node_625_wf
  · rw [h26]
    exact sm_node_626_wf
  · rw [h27]
    exact sm_node_627_wf
  · rw [h28]
    exact sm_node_628_wf
  · rw [h29]
    exact sm_node_629_wf
  · rw [h30]
    exact sm_node_630_wf
  · rw [h31]
    exact sm_node_631_wf
  · rw [h32]
    exact sm_node_632_wf
  · rw [h33]
    exact sm_node_633_wf
  · rw [h34]
    exact sm_node_634_wf
  · rw [h35]
    exact sm_node_635_wf
  · rw [h36]
    exact sm_node_636_wf
  · rw [h37]
    exact sm_node_637_wf
  · rw [h38]
    exact sm_node_638_wf
  · rw [h39]
    exact sm_node_639_wf

def smChunk_16 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_float", ins := [5532], outs := [5533] }, { rank := 0, op := "OpName.FW_add", ins := [8268, 5533], outs := [5534] }, { rank := 0, op := "OpName.FW_multiref", ins := [5534], outs := [8295, 8299], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8295, 5535], outs := [5536] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5536, 5537], outs := [5538] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := ((List.range 5).map (fun r => 5538 + r)), outs := [5543], params := [16, 4, 64, 64, 1, 0] }, { rank := 0, op := "OpName.FW_reshape", ins := [5543], outs := [5544], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [5544], outs := [5545], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5545, 5546], outs := [5547] }, { rank := 0, op := "OpName.FW_view", ins := [5547], outs := [5548], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [5548], outs := [5549] }, { rank := 0, op := "OpName.FW_add", ins := [8299, 5549], outs := [5550] }, { rank := 0, op := "OpName.FW_multiref", ins := [5550], outs := [8303, 8307], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8303, 5551], outs := [5552] }, { rank := 0, op := "OpName.FW_multiref", ins := [5552], outs := [8314, 8318, 8322, 8326, 8330], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [8314], outs := [5553] }, { rank := 0, op := "OpName.FW_reshape", ins := [8322], outs := [5562], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8326], outs := [5567], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8330], outs := [5571], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [5553, 5554], outs := [5555] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5562, 5563], outs := [5564] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5567, 5568], outs := [5569] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5571, 5572], outs := [5573] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [5555], outs := [5556, 5557, 5558], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5564], outs := [5565], params := [4096, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5569], outs := [5570], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [5573], outs := [5574], params := [4096, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8318, 5556, 5557, 5559, 5560], outs := [5561], params := [64, 0, 64, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [5565], outs := [5566] }, { rank := 0, op := "OpName.FW_swiglu", ins := [5570, 5574], outs := [5575] }, { rank := 0, op := "OpName.FW_reshape", ins := [5575], outs := [5576], params := [4096, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5576, 5577], outs := [5578] }, { rank := 0, op := "OpName.FW_view", ins := [5578], outs := [5579], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [5566, 5579], outs := [5580] }, { rank := 0, op := "OpName.FW_add", ins := [5561, 5580], outs := [5581] }, { rank := 0, op := "OpName.FW_float", ins := [5581], outs := [5582] }, { rank := 0, op := "OpName.FW_add", ins := [8307, 5582], outs := [5583] }, { rank := 0, op := "OpName.FW_multiref", ins := [5583], outs := [8334, 8338], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8334, 5584], outs := [5585] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5585, 5586], outs := [5587] }]

theorem smChunk_16_wf : ∀ n ∈ smChunk_16, IsWellFormedNode sm n := by
  intro n hn
  simp only [smChunk_16, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact sm_node_640_wf
  · rw [h1]
    exact sm_node_641_wf
  · rw [h2]
    exact sm_node_642_wf
  · rw [h3]
    exact sm_node_643_wf
  · rw [h4]
    exact sm_node_644_wf
  · rw [h5]
    exact sm_node_645_wf
  · rw [h6]
    exact sm_node_646_wf
  · rw [h7]
    exact sm_node_647_wf
  · rw [h8]
    exact sm_node_648_wf
  · rw [h9]
    exact sm_node_649_wf
  · rw [h10]
    exact sm_node_650_wf
  · rw [h11]
    exact sm_node_651_wf
  · rw [h12]
    exact sm_node_652_wf
  · rw [h13]
    exact sm_node_653_wf
  · rw [h14]
    exact sm_node_654_wf
  · rw [h15]
    exact sm_node_655_wf
  · rw [h16]
    exact sm_node_656_wf
  · rw [h17]
    exact sm_node_657_wf
  · rw [h18]
    exact sm_node_658_wf
  · rw [h19]
    exact sm_node_659_wf
  · rw [h20]
    exact sm_node_660_wf
  · rw [h21]
    exact sm_node_661_wf
  · rw [h22]
    exact sm_node_662_wf
  · rw [h23]
    exact sm_node_663_wf
  · rw [h24]
    exact sm_node_664_wf
  · rw [h25]
    exact sm_node_665_wf
  · rw [h26]
    exact sm_node_666_wf
  · rw [h27]
    exact sm_node_667_wf
  · rw [h28]
    exact sm_node_668_wf
  · rw [h29]
    exact sm_node_669_wf
  · rw [h30]
    exact sm_node_670_wf
  · rw [h31]
    exact sm_node_671_wf
  · rw [h32]
    exact sm_node_672_wf
  · rw [h33]
    exact sm_node_673_wf
  · rw [h34]
    exact sm_node_674_wf
  · rw [h35]
    exact sm_node_675_wf
  · rw [h36]
    exact sm_node_676_wf
  · rw [h37]
    exact sm_node_677_wf
  · rw [h38]
    exact sm_node_678_wf
  · rw [h39]
    exact sm_node_679_wf

def smChunk_17 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_attn_zigzag", ins := ((List.range 5).map (fun r => 5587 + r)), outs := [5592], params := [16, 4, 64, 64, 1, 0] }, { rank := 0, op := "OpName.FW_reshape", ins := [5592], outs := [5593], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [5593], outs := [5594], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5594, 5595], outs := [5596] }, { rank := 0, op := "OpName.FW_view", ins := [5596], outs := [5597], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [5597], outs := [5598] }, { rank := 0, op := "OpName.FW_add", ins := [8338, 5598], outs := [5599] }, { rank := 0, op := "OpName.FW_multiref", ins := [5599], outs := [8342, 8346], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8342, 5600], outs := [5601] }, { rank := 0, op := "OpName.FW_multiref", ins := [5601], outs := [8353, 8357, 8361, 8365, 8369], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [8353], outs := [5602] }, { rank := 0, op := "OpName.FW_reshape", ins := [8361], outs := [5611], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8365], outs := [5616], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8369], outs := [5620], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [5602, 5603], outs := [5604] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5611, 5612], outs := [5613] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5616, 5617], outs := [5618] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5620, 5621], outs := [5622] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [5604], outs := [5605, 5606, 5607], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5613], outs := [5614], params := [4096, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5618], outs := [5619], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [5622], outs := [5623], params := [4096, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8357, 5605, 5606, 5608, 5609], outs := [5610], params := [64, 0, 64, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [5614], outs := [5615] }, { rank := 0, op := "OpName.FW_swiglu", ins := [5619, 5623], outs := [5624] }, { rank := 0, op := "OpName.FW_reshape", ins := [5624], outs := [5625], params := [4096, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5625, 5626], outs := [5627] }, { rank := 0, op := "OpName.FW_view", ins := [5627], outs := [5628], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [5615, 5628], outs := [5629] }, { rank := 0, op := "OpName.FW_add", ins := [5610, 5629], outs := [5630] }, { rank := 0, op := "OpName.FW_float", ins := [5630], outs := [5631] }, { rank := 0, op := "OpName.FW_add", ins := [8346, 5631], outs := [5632] }, { rank := 0, op := "OpName.FW_multiref", ins := [5632], outs := [8373, 8377], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8373, 5633], outs := [5634] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5634, 5635], outs := [5636] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := ((List.range 5).map (fun r => 5636 + r)), outs := [5641], params := [16, 4, 64, 64, 1, 0] }, { rank := 0, op := "OpName.FW_reshape", ins := [5641], outs := [5642], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [5642], outs := [5643], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5643, 5644], outs := [5645] }, { rank := 0, op := "OpName.FW_view", ins := [5645], outs := [5646], params := [4096, 1024] }]

theorem smChunk_17_wf : ∀ n ∈ smChunk_17, IsWellFormedNode sm n := by
  intro n hn
  simp only [smChunk_17, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact sm_node_680_wf
  · rw [h1]
    exact sm_node_681_wf
  · rw [h2]
    exact sm_node_682_wf
  · rw [h3]
    exact sm_node_683_wf
  · rw [h4]
    exact sm_node_684_wf
  · rw [h5]
    exact sm_node_685_wf
  · rw [h6]
    exact sm_node_686_wf
  · rw [h7]
    exact sm_node_687_wf
  · rw [h8]
    exact sm_node_688_wf
  · rw [h9]
    exact sm_node_689_wf
  · rw [h10]
    exact sm_node_690_wf
  · rw [h11]
    exact sm_node_691_wf
  · rw [h12]
    exact sm_node_692_wf
  · rw [h13]
    exact sm_node_693_wf
  · rw [h14]
    exact sm_node_694_wf
  · rw [h15]
    exact sm_node_695_wf
  · rw [h16]
    exact sm_node_696_wf
  · rw [h17]
    exact sm_node_697_wf
  · rw [h18]
    exact sm_node_698_wf
  · rw [h19]
    exact sm_node_699_wf
  · rw [h20]
    exact sm_node_700_wf
  · rw [h21]
    exact sm_node_701_wf
  · rw [h22]
    exact sm_node_702_wf
  · rw [h23]
    exact sm_node_703_wf
  · rw [h24]
    exact sm_node_704_wf
  · rw [h25]
    exact sm_node_705_wf
  · rw [h26]
    exact sm_node_706_wf
  · rw [h27]
    exact sm_node_707_wf
  · rw [h28]
    exact sm_node_708_wf
  · rw [h29]
    exact sm_node_709_wf
  · rw [h30]
    exact sm_node_710_wf
  · rw [h31]
    exact sm_node_711_wf
  · rw [h32]
    exact sm_node_712_wf
  · rw [h33]
    exact sm_node_713_wf
  · rw [h34]
    exact sm_node_714_wf
  · rw [h35]
    exact sm_node_715_wf
  · rw [h36]
    exact sm_node_716_wf
  · rw [h37]
    exact sm_node_717_wf
  · rw [h38]
    exact sm_node_718_wf
  · rw [h39]
    exact sm_node_719_wf

def smChunk_18 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_float", ins := [5646], outs := [5647] }, { rank := 0, op := "OpName.FW_add", ins := [8377, 5647], outs := [5648] }, { rank := 0, op := "OpName.FW_multiref", ins := [5648], outs := [8381, 8385], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8381, 5649], outs := [5650] }, { rank := 0, op := "OpName.FW_multiref", ins := [5650], outs := [8392, 8396, 8400, 8404, 8408], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [8392], outs := [5651] }, { rank := 0, op := "OpName.FW_reshape", ins := [8400], outs := [5660], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8404], outs := [5665], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8408], outs := [5669], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [5651, 5652], outs := [5653] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5660, 5661], outs := [5662] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5665, 5666], outs := [5667] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5669, 5670], outs := [5671] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [5653], outs := [5654, 5655, 5656], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5662], outs := [5663], params := [4096, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5667], outs := [5668], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [5671], outs := [5672], params := [4096, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8396, 5654, 5655, 5657, 5658], outs := [5659], params := [64, 0, 64, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [5663], outs := [5664] }, { rank := 0, op := "OpName.FW_swiglu", ins := [5668, 5672], outs := [5673] }, { rank := 0, op := "OpName.FW_reshape", ins := [5673], outs := [5674], params := [4096, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5674, 5675], outs := [5676] }, { rank := 0, op := "OpName.FW_view", ins := [5676], outs := [5677], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [5664, 5677], outs := [5678] }, { rank := 0, op := "OpName.FW_add", ins := [5659, 5678], outs := [5679] }, { rank := 0, op := "OpName.FW_float", ins := [5679], outs := [5680] }, { rank := 0, op := "OpName.FW_add", ins := [8385, 5680], outs := [5681] }, { rank := 0, op := "OpName.FW_multiref", ins := [5681], outs := [8412, 8416], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8412, 5682], outs := [5683] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5683, 5684], outs := [5685] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := ((List.range 5).map (fun r => 5685 + r)), outs := [5690], params := [16, 4, 64, 64, 1, 0] }, { rank := 0, op := "OpName.FW_reshape", ins := [5690], outs := [5691], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [5691], outs := [5692], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5692, 5693], outs := [5694] }, { rank := 0, op := "OpName.FW_view", ins := [5694], outs := [5695], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [5695], outs := [5696] }, { rank := 0, op := "OpName.FW_add", ins := [8416, 5696], outs := [5697] }, { rank := 0, op := "OpName.FW_multiref", ins := [5697], outs := [8420, 8424], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8420, 5698], outs := [5699] }, { rank := 0, op := "OpName.FW_multiref", ins := [5699], outs := [8431, 8435, 8439, 8443, 8447], params := [5] }]

theorem smChunk_18_wf : ∀ n ∈ smChunk_18, IsWellFormedNode sm n := by
  intro n hn
  simp only [smChunk_18, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact sm_node_720_wf
  · rw [h1]
    exact sm_node_721_wf
  · rw [h2]
    exact sm_node_722_wf
  · rw [h3]
    exact sm_node_723_wf
  · rw [h4]
    exact sm_node_724_wf
  · rw [h5]
    exact sm_node_725_wf
  · rw [h6]
    exact sm_node_726_wf
  · rw [h7]
    exact sm_node_727_wf
  · rw [h8]
    exact sm_node_728_wf
  · rw [h9]
    exact sm_node_729_wf
  · rw [h10]
    exact sm_node_730_wf
  · rw [h11]
    exact sm_node_731_wf
  · rw [h12]
    exact sm_node_732_wf
  · rw [h13]
    exact sm_node_733_wf
  · rw [h14]
    exact sm_node_734_wf
  · rw [h15]
    exact sm_node_735_wf
  · rw [h16]
    exact sm_node_736_wf
  · rw [h17]
    exact sm_node_737_wf
  · rw [h18]
    exact sm_node_738_wf
  · rw [h19]
    exact sm_node_739_wf
  · rw [h20]
    exact sm_node_740_wf
  · rw [h21]
    exact sm_node_741_wf
  · rw [h22]
    exact sm_node_742_wf
  · rw [h23]
    exact sm_node_743_wf
  · rw [h24]
    exact sm_node_744_wf
  · rw [h25]
    exact sm_node_745_wf
  · rw [h26]
    exact sm_node_746_wf
  · rw [h27]
    exact sm_node_747_wf
  · rw [h28]
    exact sm_node_748_wf
  · rw [h29]
    exact sm_node_749_wf
  · rw [h30]
    exact sm_node_750_wf
  · rw [h31]
    exact sm_node_751_wf
  · rw [h32]
    exact sm_node_752_wf
  · rw [h33]
    exact sm_node_753_wf
  · rw [h34]
    exact sm_node_754_wf
  · rw [h35]
    exact sm_node_755_wf
  · rw [h36]
    exact sm_node_756_wf
  · rw [h37]
    exact sm_node_757_wf
  · rw [h38]
    exact sm_node_758_wf
  · rw [h39]
    exact sm_node_759_wf

def smChunk_19 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_float", ins := [8431], outs := [5700] }, { rank := 0, op := "OpName.FW_reshape", ins := [8439], outs := [5709], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8443], outs := [5714], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8447], outs := [5718], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [5700, 5701], outs := [5702] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5709, 5710], outs := [5711] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5714, 5715], outs := [5716] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5718, 5719], outs := [5720] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [5702], outs := [5703, 5704, 5705], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5711], outs := [5712], params := [4096, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5716], outs := [5717], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [5720], outs := [5721], params := [4096, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8435, 5703, 5704, 5706, 5707], outs := [5708], params := [64, 0, 64, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [5712], outs := [5713] }, { rank := 0, op := "OpName.FW_swiglu", ins := [5717, 5721], outs := [5722] }, { rank := 0, op := "OpName.FW_reshape", ins := [5722], outs := [5723], params := [4096, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5723, 5724], outs := [5725] }, { rank := 0, op := "OpName.FW_view", ins := [5725], outs := [5726], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [5713, 5726], outs := [5727] }, { rank := 0, op := "OpName.FW_add", ins := [5708, 5727], outs := [5728] }, { rank := 0, op := "OpName.FW_float", ins := [5728], outs := [5729] }, { rank := 0, op := "OpName.FW_add", ins := [8424, 5729], outs := [5730] }, { rank := 0, op := "OpName.FW_multiref", ins := [5730], outs := [8451, 8455], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8451, 5731], outs := [5732] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5732, 5733], outs := [5734] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := ((List.range 5).map (fun r => 5734 + r)), outs := [5739], params := [16, 4, 64, 64, 1, 0] }, { rank := 0, op := "OpName.FW_reshape", ins := [5739], outs := [5740], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [5740], outs := [5741], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5741, 5742], outs := [5743] }, { rank := 0, op := "OpName.FW_view", ins := [5743], outs := [5744], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [5744], outs := [5745] }, { rank := 0, op := "OpName.FW_add", ins := [8455, 5745], outs := [5746] }, { rank := 0, op := "OpName.FW_multiref", ins := [5746], outs := [8459, 8463], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8459, 5747], outs := [5748] }, { rank := 0, op := "OpName.FW_multiref", ins := [5748], outs := [8470, 8474, 8478, 8482, 8486], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [8470], outs := [5749] }, { rank := 0, op := "OpName.FW_reshape", ins := [8478], outs := [5758], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8482], outs := [5763], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8486], outs := [5767], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [5749, 5750], outs := [5751] }]

theorem smChunk_19_wf : ∀ n ∈ smChunk_19, IsWellFormedNode sm n := by
  intro n hn
  simp only [smChunk_19, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact sm_node_760_wf
  · rw [h1]
    exact sm_node_761_wf
  · rw [h2]
    exact sm_node_762_wf
  · rw [h3]
    exact sm_node_763_wf
  · rw [h4]
    exact sm_node_764_wf
  · rw [h5]
    exact sm_node_765_wf
  · rw [h6]
    exact sm_node_766_wf
  · rw [h7]
    exact sm_node_767_wf
  · rw [h8]
    exact sm_node_768_wf
  · rw [h9]
    exact sm_node_769_wf
  · rw [h10]
    exact sm_node_770_wf
  · rw [h11]
    exact sm_node_771_wf
  · rw [h12]
    exact sm_node_772_wf
  · rw [h13]
    exact sm_node_773_wf
  · rw [h14]
    exact sm_node_774_wf
  · rw [h15]
    exact sm_node_775_wf
  · rw [h16]
    exact sm_node_776_wf
  · rw [h17]
    exact sm_node_777_wf
  · rw [h18]
    exact sm_node_778_wf
  · rw [h19]
    exact sm_node_779_wf
  · rw [h20]
    exact sm_node_780_wf
  · rw [h21]
    exact sm_node_781_wf
  · rw [h22]
    exact sm_node_782_wf
  · rw [h23]
    exact sm_node_783_wf
  · rw [h24]
    exact sm_node_784_wf
  · rw [h25]
    exact sm_node_785_wf
  · rw [h26]
    exact sm_node_786_wf
  · rw [h27]
    exact sm_node_787_wf
  · rw [h28]
    exact sm_node_788_wf
  · rw [h29]
    exact sm_node_789_wf
  · rw [h30]
    exact sm_node_790_wf
  · rw [h31]
    exact sm_node_791_wf
  · rw [h32]
    exact sm_node_792_wf
  · rw [h33]
    exact sm_node_793_wf
  · rw [h34]
    exact sm_node_794_wf
  · rw [h35]
    exact sm_node_795_wf
  · rw [h36]
    exact sm_node_796_wf
  · rw [h37]
    exact sm_node_797_wf
  · rw [h38]
    exact sm_node_798_wf
  · rw [h39]
    exact sm_node_799_wf

def smChunk_20 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5758, 5759], outs := [5760] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5763, 5764], outs := [5765] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5767, 5768], outs := [5769] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [5751], outs := [5752, 5753, 5754], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5760], outs := [5761], params := [4096, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5765], outs := [5766], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [5769], outs := [5770], params := [4096, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8474, 5752, 5753, 5755, 5756], outs := [5757], params := [64, 0, 64, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [5761], outs := [5762] }, { rank := 0, op := "OpName.FW_swiglu", ins := [5766, 5770], outs := [5771] }, { rank := 0, op := "OpName.FW_reshape", ins := [5771], outs := [5772], params := [4096, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5772, 5773], outs := [5774] }, { rank := 0, op := "OpName.FW_view", ins := [5774], outs := [5775], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [5762, 5775], outs := [5776] }, { rank := 0, op := "OpName.FW_add", ins := [5757, 5776], outs := [5777] }, { rank := 0, op := "OpName.FW_float", ins := [5777], outs := [5778] }, { rank := 0, op := "OpName.FW_add", ins := [8463, 5778], outs := [5779] }, { rank := 0, op := "OpName.FW_multiref", ins := [5779], outs := [8490, 8494], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8490, 5780], outs := [5781] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5781, 5782], outs := [5783] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := ((List.range 5).map (fun r => 5783 + r)), outs := [5788], params := [16, 4, 64, 64, 1, 0] }, { rank := 0, op := "OpName.FW_reshape", ins := [5788], outs := [5789], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [5789], outs := [5790], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5790, 5791], outs := [5792] }, { rank := 0, op := "OpName.FW_view", ins := [5792], outs := [5793], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [5793], outs := [5794] }, { rank := 0, op := "OpName.FW_add", ins := [8494, 5794], outs := [5795] }, { rank := 0, op := "OpName.FW_multiref", ins := [5795], outs := [8498, 8502], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8498, 5796], outs := [5797] }, { rank := 0, op := "OpName.FW_multiref", ins := [5797], outs := [8509, 8513, 8517, 8521, 8525], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [8509], outs := [5798] }, { rank := 0, op := "OpName.FW_reshape", ins := [8517], outs := [5807], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8521], outs := [5812], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8525], outs := [5816], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [5798, 5799], outs := [5800] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5807, 5808], outs := [5809] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5812, 5813], outs := [5814] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5816, 5817], outs := [5818] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [5800], outs := [5801, 5802, 5803], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5809], outs := [5810], params := [4096, 1] }]

theorem smChunk_20_wf : ∀ n ∈ smChunk_20, IsWellFormedNode sm n := by
  intro n hn
  simp only [smChunk_20, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact sm_node_800_wf
  · rw [h1]
    exact sm_node_801_wf
  · rw [h2]
    exact sm_node_802_wf
  · rw [h3]
    exact sm_node_803_wf
  · rw [h4]
    exact sm_node_804_wf
  · rw [h5]
    exact sm_node_805_wf
  · rw [h6]
    exact sm_node_806_wf
  · rw [h7]
    exact sm_node_807_wf
  · rw [h8]
    exact sm_node_808_wf
  · rw [h9]
    exact sm_node_809_wf
  · rw [h10]
    exact sm_node_810_wf
  · rw [h11]
    exact sm_node_811_wf
  · rw [h12]
    exact sm_node_812_wf
  · rw [h13]
    exact sm_node_813_wf
  · rw [h14]
    exact sm_node_814_wf
  · rw [h15]
    exact sm_node_815_wf
  · rw [h16]
    exact sm_node_816_wf
  · rw [h17]
    exact sm_node_817_wf
  · rw [h18]
    exact sm_node_818_wf
  · rw [h19]
    exact sm_node_819_wf
  · rw [h20]
    exact sm_node_820_wf
  · rw [h21]
    exact sm_node_821_wf
  · rw [h22]
    exact sm_node_822_wf
  · rw [h23]
    exact sm_node_823_wf
  · rw [h24]
    exact sm_node_824_wf
  · rw [h25]
    exact sm_node_825_wf
  · rw [h26]
    exact sm_node_826_wf
  · rw [h27]
    exact sm_node_827_wf
  · rw [h28]
    exact sm_node_828_wf
  · rw [h29]
    exact sm_node_829_wf
  · rw [h30]
    exact sm_node_830_wf
  · rw [h31]
    exact sm_node_831_wf
  · rw [h32]
    exact sm_node_832_wf
  · rw [h33]
    exact sm_node_833_wf
  · rw [h34]
    exact sm_node_834_wf
  · rw [h35]
    exact sm_node_835_wf
  · rw [h36]
    exact sm_node_836_wf
  · rw [h37]
    exact sm_node_837_wf
  · rw [h38]
    exact sm_node_838_wf
  · rw [h39]
    exact sm_node_839_wf

def smChunk_21 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_view", ins := [5814], outs := [5815], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [5818], outs := [5819], params := [4096, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8513, 5801, 5802, 5804, 5805], outs := [5806], params := [64, 0, 64, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [5810], outs := [5811] }, { rank := 0, op := "OpName.FW_swiglu", ins := [5815, 5819], outs := [5820] }, { rank := 0, op := "OpName.FW_reshape", ins := [5820], outs := [5821], params := [4096, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5821, 5822], outs := [5823] }, { rank := 0, op := "OpName.FW_view", ins := [5823], outs := [5824], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [5811, 5824], outs := [5825] }, { rank := 0, op := "OpName.FW_add", ins := [5806, 5825], outs := [5826] }, { rank := 0, op := "OpName.FW_float", ins := [5826], outs := [5827] }, { rank := 0, op := "OpName.FW_add", ins := [8502, 5827], outs := [5828] }, { rank := 0, op := "OpName.FW_multiref", ins := [5828], outs := [8529, 8533], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8529, 5829], outs := [5830] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5830, 5831], outs := [5832] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := ((List.range 5).map (fun r => 5832 + r)), outs := [5837], params := [16, 4, 64, 64, 1, 0] }, { rank := 0, op := "OpName.FW_reshape", ins := [5837], outs := [5838], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [5838], outs := [5839], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5839, 5840], outs := [5841] }, { rank := 0, op := "OpName.FW_view", ins := [5841], outs := [5842], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [5842], outs := [5843] }, { rank := 0, op := "OpName.FW_add", ins := [8533, 5843], outs := [5844] }, { rank := 0, op := "OpName.FW_multiref", ins := [5844], outs := [8537, 8541], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8537, 5845], outs := [5846] }, { rank := 0, op := "OpName.FW_multiref", ins := [5846], outs := [8548, 8552, 8556, 8560, 8564], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [8548], outs := [5847] }, { rank := 0, op := "OpName.FW_reshape", ins := [8556], outs := [5856], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8560], outs := [5861], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8564], outs := [5865], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [5847, 5848], outs := [5849] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5856, 5857], outs := [5858] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5861, 5862], outs := [5863] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5865, 5866], outs := [5867] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [5849], outs := [5850, 5851, 5852], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5858], outs := [5859], params := [4096, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5863], outs := [5864], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [5867], outs := [5868], params := [4096, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8552, 5850, 5851, 5853, 5854], outs := [5855], params := [64, 0, 64, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [5859], outs := [5860] }, { rank := 0, op := "OpName.FW_swiglu", ins := [5864, 5868], outs := [5869] }]

theorem smChunk_21_wf : ∀ n ∈ smChunk_21, IsWellFormedNode sm n := by
  intro n hn
  simp only [smChunk_21, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact sm_node_840_wf
  · rw [h1]
    exact sm_node_841_wf
  · rw [h2]
    exact sm_node_842_wf
  · rw [h3]
    exact sm_node_843_wf
  · rw [h4]
    exact sm_node_844_wf
  · rw [h5]
    exact sm_node_845_wf
  · rw [h6]
    exact sm_node_846_wf
  · rw [h7]
    exact sm_node_847_wf
  · rw [h8]
    exact sm_node_848_wf
  · rw [h9]
    exact sm_node_849_wf
  · rw [h10]
    exact sm_node_850_wf
  · rw [h11]
    exact sm_node_851_wf
  · rw [h12]
    exact sm_node_852_wf
  · rw [h13]
    exact sm_node_853_wf
  · rw [h14]
    exact sm_node_854_wf
  · rw [h15]
    exact sm_node_855_wf
  · rw [h16]
    exact sm_node_856_wf
  · rw [h17]
    exact sm_node_857_wf
  · rw [h18]
    exact sm_node_858_wf
  · rw [h19]
    exact sm_node_859_wf
  · rw [h20]
    exact sm_node_860_wf
  · rw [h21]
    exact sm_node_861_wf
  · rw [h22]
    exact sm_node_862_wf
  · rw [h23]
    exact sm_node_863_wf
  · rw [h24]
    exact sm_node_864_wf
  · rw [h25]
    exact sm_node_865_wf
  · rw [h26]
    exact sm_node_866_wf
  · rw [h27]
    exact sm_node_867_wf
  · rw [h28]
    exact sm_node_868_wf
  · rw [h29]
    exact sm_node_869_wf
  · rw [h30]
    exact sm_node_870_wf
  · rw [h31]
    exact sm_node_871_wf
  · rw [h32]
    exact sm_node_872_wf
  · rw [h33]
    exact sm_node_873_wf
  · rw [h34]
    exact sm_node_874_wf
  · rw [h35]
    exact sm_node_875_wf
  · rw [h36]
    exact sm_node_876_wf
  · rw [h37]
    exact sm_node_877_wf
  · rw [h38]
    exact sm_node_878_wf
  · rw [h39]
    exact sm_node_879_wf

def smChunk_22 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_reshape", ins := [5869], outs := [5870], params := [4096, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5870, 5871], outs := [5872] }, { rank := 0, op := "OpName.FW_view", ins := [5872], outs := [5873], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [5860, 5873], outs := [5874] }, { rank := 0, op := "OpName.FW_add", ins := [5855, 5874], outs := [5875] }, { rank := 0, op := "OpName.FW_float", ins := [5875], outs := [5876] }, { rank := 0, op := "OpName.FW_add", ins := [8541, 5876], outs := [5877] }, { rank := 0, op := "OpName.FW_multiref", ins := [5877], outs := [8568, 8572], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8568, 5878], outs := [5879] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5879, 5880], outs := [5881] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := ((List.range 5).map (fun r => 5881 + r)), outs := [5886], params := [16, 4, 64, 64, 1, 0] }, { rank := 0, op := "OpName.FW_reshape", ins := [5886], outs := [5887], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [5887], outs := [5888], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5888, 5889], outs := [5890] }, { rank := 0, op := "OpName.FW_view", ins := [5890], outs := [5891], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [5891], outs := [5892] }, { rank := 0, op := "OpName.FW_add", ins := [8572, 5892], outs := [5893] }, { rank := 0, op := "OpName.FW_multiref", ins := [5893], outs := [8576, 8580], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [8576, 5894], outs := [5895] }, { rank := 0, op := "OpName.FW_multiref", ins := [5895], outs := [8587, 8591, 8595, 8599, 8603], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [8587], outs := [5896] }, { rank := 0, op := "OpName.FW_reshape", ins := [8595], outs := [5905], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8599], outs := [5910], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8603], outs := [5914], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [5896, 5897], outs := [5898] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5905, 5906], outs := [5907] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5910, 5911], outs := [5912] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5914, 5915], outs := [5916] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [5898], outs := [5899, 5900, 5901], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5907], outs := [5908], params := [4096, 1] }, { rank := 0, op := "OpName.FW_view", ins := [5912], outs := [5913], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [5916], outs := [5917], params := [4096, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8591, 5899, 5900, 5902, 5903], outs := [5904], params := [64, 0, 64, 8] }, { rank := 0, op := "OpName.FW_stack", ins := [4710, 4764, 4818, 4872, 4926, 4980, 5034, 5088, 5142, 5196, 5250, 5304, 5361, 5410, 5459, 5508, 5557, 5606, 5655, 5704, 5753, 5802, 5851, 5900], outs := [4675] }, { rank := 0, op := "OpName.FW_stack", ins := [4711, 4765, 4819, 4873, 4927, 4981, 5035, 5089, 5143, 5197, 5251, 5305, 5362, 5411, 5460, 5509, 5558, 5607, 5656, 5705, 5754, 5803, 5852, 5901], outs := [4676] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [5908], outs := [5909] }, { rank := 0, op := "OpName.FW_swiglu", ins := [5913, 5917], outs := [5918] }, { rank := 0, op := "OpName.FW_reshape", ins := [5918], outs := [5919], params := [4096, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5919, 5920], outs := [5921] }, { rank := 0, op := "OpName.FW_view", ins := [5921], outs := [5922], params := [4096, 1024] }]

theorem smChunk_22_wf : ∀ n ∈ smChunk_22, IsWellFormedNode sm n := by
  intro n hn
  simp only [smChunk_22, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact sm_node_880_wf
  · rw [h1]
    exact sm_node_881_wf
  · rw [h2]
    exact sm_node_882_wf
  · rw [h3]
    exact sm_node_883_wf
  · rw [h4]
    exact sm_node_884_wf
  · rw [h5]
    exact sm_node_885_wf
  · rw [h6]
    exact sm_node_886_wf
  · rw [h7]
    exact sm_node_887_wf
  · rw [h8]
    exact sm_node_888_wf
  · rw [h9]
    exact sm_node_889_wf
  · rw [h10]
    exact sm_node_890_wf
  · rw [h11]
    exact sm_node_891_wf
  · rw [h12]
    exact sm_node_892_wf
  · rw [h13]
    exact sm_node_893_wf
  · rw [h14]
    exact sm_node_894_wf
  · rw [h15]
    exact sm_node_895_wf
  · rw [h16]
    exact sm_node_896_wf
  · rw [h17]
    exact sm_node_897_wf
  · rw [h18]
    exact sm_node_898_wf
  · rw [h19]
    exact sm_node_899_wf
  · rw [h20]
    exact sm_node_900_wf
  · rw [h21]
    exact sm_node_901_wf
  · rw [h22]
    exact sm_node_902_wf
  · rw [h23]
    exact sm_node_903_wf
  · rw [h24]
    exact sm_node_904_wf
  · rw [h25]
    exact sm_node_905_wf
  · rw [h26]
    exact sm_node_906_wf
  · rw [h27]
    exact sm_node_907_wf
  · rw [h28]
    exact sm_node_908_wf
  · rw [h29]
    exact sm_node_909_wf
  · rw [h30]
    exact sm_node_910_wf
  · rw [h31]
    exact sm_node_911_wf
  · rw [h32]
    exact sm_node_912_wf
  · rw [h33]
    exact sm_node_913_wf
  · rw [h34]
    exact sm_node_914_wf
  · rw [h35]
    exact sm_node_915_wf
  · rw [h36]
    exact sm_node_916_wf
  · rw [h37]
    exact sm_node_917_wf
  · rw [h38]
    exact sm_node_918_wf
  · rw [h39]
    exact sm_node_919_wf

def smChunk_23 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_mul", ins := [5909, 5922], outs := [5923] }, { rank := 0, op := "OpName.FW_add", ins := [5904, 5923], outs := [5924] }, { rank := 0, op := "OpName.FW_float", ins := [5924], outs := [5925] }, { rank := 0, op := "OpName.FW_add", ins := [8580, 5925], outs := [5926] }, { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5926, 5927], outs := [5928], params := [1, 0] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [5928, 5929], outs := [5930] }, { rank := 0, op := "OpName.FW_inner_chunk_ce", ins := [5930, 5931, 4678], outs := [4673, 4674], params := [1024] }]

theorem smChunk_23_wf : ∀ n ∈ smChunk_23, IsWellFormedNode sm n := by
  intro n hn
  simp only [smChunk_23, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · rw [h0]
    exact sm_node_920_wf
  · rw [h1]
    exact sm_node_921_wf
  · rw [h2]
    exact sm_node_922_wf
  · rw [h3]
    exact sm_node_923_wf
  · rw [h4]
    exact sm_node_924_wf
  · rw [h5]
    exact sm_node_925_wf
  · rw [h6]
    exact sm_node_926_wf

def smNodeChunks : List NodeDecl :=
  smChunk_0 ++ (smChunk_1 ++ (smChunk_2 ++ (smChunk_3 ++ (smChunk_4 ++ (smChunk_5 ++ (smChunk_6 ++ (smChunk_7 ++ (smChunk_8 ++ (smChunk_9 ++ (smChunk_10 ++ (smChunk_11 ++ (smChunk_12 ++ (smChunk_13 ++ (smChunk_14 ++ (smChunk_15 ++ (smChunk_16 ++ (smChunk_17 ++ (smChunk_18 ++ (smChunk_19 ++ (smChunk_20 ++ (smChunk_21 ++ (smChunk_22 ++ (smChunk_23)))))))))))))))))))))))

theorem sm_nodes_eq_chunks : sm.nodes = smNodeChunks := by
  rfl

theorem sm_wellFormed : IsWellFormedGraph sm := by
  intro n hn
  rw [sm_nodes_eq_chunks] at hn
  simp only [smNodeChunks, List.mem_append] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23
  · exact smChunk_0_wf n h0
  · exact smChunk_1_wf n h1
  · exact smChunk_2_wf n h2
  · exact smChunk_3_wf n h3
  · exact smChunk_4_wf n h4
  · exact smChunk_5_wf n h5
  · exact smChunk_6_wf n h6
  · exact smChunk_7_wf n h7
  · exact smChunk_8_wf n h8
  · exact smChunk_9_wf n h9
  · exact smChunk_10_wf n h10
  · exact smChunk_11_wf n h11
  · exact smChunk_12_wf n h12
  · exact smChunk_13_wf n h13
  · exact smChunk_14_wf n h14
  · exact smChunk_15_wf n h15
  · exact smChunk_16_wf n h16
  · exact smChunk_17_wf n h17
  · exact smChunk_18_wf n h18
  · exact smChunk_19_wf n h19
  · exact smChunk_20_wf n h20
  · exact smChunk_21_wf n h21
  · exact smChunk_22_wf n h22
  · exact smChunk_23_wf n h23

theorem sm_topoSorted : IsTopoSorted sm.nodes := by
  apply isTopoSorted_of_bool
  native_decide

theorem sm_nodes_nodup : sm.nodes.Nodup := by native_decide

def pmChunk_0 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_embedding", ins := [4677, 7389], outs := [7391], params := [0] }, { rank := 0, op := "OpName.FW_multiref", ins := [4691], outs := ((List.range 12).map (fun r => 11853 + r)), params := [12] }, { rank := 0, op := "OpName.ChunkPrim", ins := [4799], outs := [7803], params := [0] }, { rank := 0, op := "OpName.ChunkPrim", ins := [4853], outs := [7989], params := [0] }, { rank := 0, op := "OpName.ChunkPrim", ins := [4907], outs := [8175], params := [0] }, { rank := 0, op := "OpName.ChunkPrim", ins := [4961], outs := [8361], params := [0] }, { rank := 0, op := "OpName.ChunkPrim", ins := [5015], outs := [8547], params := [0] }, { rank := 0, op := "OpName.ChunkPrim", ins := [5069], outs := [8733], params := [0] }, { rank := 0, op := "OpName.ChunkPrim", ins := [5123], outs := [8919], params := [0] }, { rank := 0, op := "OpName.ChunkPrim", ins := [5177], outs := [9105], params := [0] }, { rank := 0, op := "OpName.ChunkPrim", ins := [5231], outs := [9291], params := [0] }, { rank := 0, op := "OpName.ChunkPrim", ins := [5285], outs := [9477], params := [0] }, { rank := 0, op := "OpName.ChunkPrim", ins := [4678], outs := [11835], params := [0] }, { rank := 1, op := "OpName.FW_embedding", ins := [4677, 7390], outs := [7392], params := [77440] }, { rank := 1, op := "OpName.FW_multiref", ins := [4691], outs := ((List.range 12).map (fun r => 11853 + r)), params := [12] }, { rank := 1, op := "OpName.ChunkPrim", ins := [4799], outs := [7804], params := [0] }, { rank := 1, op := "OpName.ChunkPrim", ins := [4853], outs := [7990], params := [0] }, { rank := 1, op := "OpName.ChunkPrim", ins := [4907], outs := [8176], params := [0] }, { rank := 1, op := "OpName.ChunkPrim", ins := [4961], outs := [8362], params := [0] }, { rank := 1, op := "OpName.ChunkPrim", ins := [5015], outs := [8548], params := [0] }, { rank := 1, op := "OpName.ChunkPrim", ins := [5069], outs := [8734], params := [0] }, { rank := 1, op := "OpName.ChunkPrim", ins := [5123], outs := [8920], params := [0] }, { rank := 1, op := "OpName.ChunkPrim", ins := [5177], outs := [9106], params := [0] }, { rank := 1, op := "OpName.ChunkPrim", ins := [5231], outs := [9292], params := [0] }, { rank := 1, op := "OpName.ChunkPrim", ins := [5285], outs := [9478], params := [0] }, { rank := 1, op := "OpName.ChunkPrim", ins := [4678], outs := [11836], params := [0] }, { rank := 0, op := "OpName.AllReducePrim", ins := [7391, 7392], outs := [4680] }, { rank := 0, op := "OpName.FW_float", ins := [4680], outs := [4681] }, { rank := 1, op := "OpName.FW_float", ins := [4680], outs := [4681] }, { rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [14603, 14607], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [4681], outs := [14611, 14615], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [14603, 4682], outs := [4683] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [14611, 4682], outs := [4683] }, { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [14620, 14624, 14628], params := [3] }, { rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14620, 4684], outs := [4685] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14624, 4686], outs := [4687] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14628, 4688], outs := [4689] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14632, 4684], outs := [4685] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14636, 4686], outs := [4687] }]

theorem pmChunk_0_wf : ∀ n ∈ pmChunk_0, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_0, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_0_wf
  · rw [h1]
    exact pm_node_1_wf
  · rw [h2]
    exact pm_node_2_wf
  · rw [h3]
    exact pm_node_3_wf
  · rw [h4]
    exact pm_node_4_wf
  · rw [h5]
    exact pm_node_5_wf
  · rw [h6]
    exact pm_node_6_wf
  · rw [h7]
    exact pm_node_7_wf
  · rw [h8]
    exact pm_node_8_wf
  · rw [h9]
    exact pm_node_9_wf
  · rw [h10]
    exact pm_node_10_wf
  · rw [h11]
    exact pm_node_11_wf
  · rw [h12]
    exact pm_node_12_wf
  · rw [h13]
    exact pm_node_13_wf
  · rw [h14]
    exact pm_node_14_wf
  · rw [h15]
    exact pm_node_15_wf
  · rw [h16]
    exact pm_node_16_wf
  · rw [h17]
    exact pm_node_17_wf
  · rw [h18]
    exact pm_node_18_wf
  · rw [h19]
    exact pm_node_19_wf
  · rw [h20]
    exact pm_node_20_wf
  · rw [h21]
    exact pm_node_21_wf
  · rw [h22]
    exact pm_node_22_wf
  · rw [h23]
    exact pm_node_23_wf
  · rw [h24]
    exact pm_node_24_wf
  · rw [h25]
    exact pm_node_25_wf
  · rw [h26]
    exact pm_node_26_wf
  · rw [h27]
    exact pm_node_27_wf
  · rw [h28]
    exact pm_node_28_wf
  · rw [h29]
    exact pm_node_29_wf
  · rw [h30]
    exact pm_node_30_wf
  · rw [h31]
    exact pm_node_31_wf
  · rw [h32]
    exact pm_node_32_wf
  · rw [h33]
    exact pm_node_33_wf
  · rw [h34]
    exact pm_node_34_wf
  · rw [h35]
    exact pm_node_35_wf
  · rw [h36]
    exact pm_node_36_wf
  · rw [h37]
    exact pm_node_37_wf
  · rw [h38]
    exact pm_node_38_wf
  · rw [h39]
    exact pm_node_39_wf

def pmChunk_1 : List NodeDecl :=
  [{ rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14640, 4688], outs := [4689] }, { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11853, 4690, 4685, 4687], outs := [4692, 4693], params := [16, 4] }, { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11853, 4690, 4685, 4687], outs := [4692, 4693], params := [16, 4] }, { rank := 0, op := "OpName.ChunkPrim", ins := [4689], outs := [7421], params := [0] }, { rank := 1, op := "OpName.ChunkPrim", ins := [4689], outs := [7422], params := [0] }, { rank := 0, op := "OpName.ChunkPrim", ins := [4692], outs := [7433], params := [0] }, { rank := 0, op := "OpName.ChunkPrim", ins := [4693], outs := [7435], params := [0] }, { rank := 1, op := "OpName.ChunkPrim", ins := [4692], outs := [7434], params := [0] }, { rank := 1, op := "OpName.ChunkPrim", ins := [4693], outs := [7436], params := [0] }, { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [7433, 7435, 7421, 4694, 4695], outs := [7437], params := [16, 4, 64, 64, 1, 512] }, { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [7434, 7436, 7422, 4694, 4695], outs := [7438], params := [16, 4, 64, 64, 1, 512] }, { rank := 0, op := "OpName.FW_reshape", ins := [7437], outs := [7439], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [7438], outs := [7440], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7439], outs := [7445], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [7440], outs := [7446], params := [2048, 1024] }, { rank := 0, op := "OpName.AllGatherPrim", ins := [7445, 7446], outs := [4698], params := [0] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4698, 4699], outs := [4700] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4698, 4699], outs := [4700] }, { rank := 0, op := "OpName.FW_view", ins := [4700], outs := [4701], params := [4096, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [4700], outs := [4701], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [4701], outs := [4702] }, { rank := 1, op := "OpName.FW_float", ins := [4701], outs := [4702] }, { rank := 0, op := "OpName.FW_add", ins := [14607, 4702], outs := [4703] }, { rank := 1, op := "OpName.FW_add", ins := [14615, 4702], outs := [4703] }, { rank := 0, op := "OpName.FW_multiref", ins := [4703], outs := [14644, 14648], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [4703], outs := [14652, 14656], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [14644, 4704], outs := [4705] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [14652, 4704], outs := [4705] }, { rank := 0, op := "OpName.FW_multiref", ins := [4705], outs := ((List.range 5).map (fun r => 11875 + r)), params := [5] }, { rank := 1, op := "OpName.FW_multiref", ins := [4705], outs := ((List.range 5).map (fun r => 11875 + r)), params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [11875], outs := [4706] }, { rank := 0, op := "OpName.ChunkPrim", ins := [11876], outs := [11941], params := [0] }, { rank := 0, op := "OpName.FW_reshape", ins := [11877], outs := [4715], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [11878], outs := [4720], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [11879], outs := [4724], params := [4096, 1024] }, { rank := 1, op := "OpName.FW_float", ins := [11875], outs := [4706] }, { rank := 1, op := "OpName.ChunkPrim", ins := [11876], outs := [11942], params := [0] }, { rank := 1, op := "OpName.FW_reshape", ins := [11877], outs := [4715], params := [4096, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [11878], outs := [4720], params := [4096, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [11879], outs := [4724], params := [4096, 1024] }]

theorem pmChunk_1_wf : ∀ n ∈ pmChunk_1, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_1, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_40_wf
  · rw [h1]
    exact pm_node_41_wf
  · rw [h2]
    exact pm_node_42_wf
  · rw [h3]
    exact pm_node_43_wf
  · rw [h4]
    exact pm_node_44_wf
  · rw [h5]
    exact pm_node_45_wf
  · rw [h6]
    exact pm_node_46_wf
  · rw [h7]
    exact pm_node_47_wf
  · rw [h8]
    exact pm_node_48_wf
  · rw [h9]
    exact pm_node_49_wf
  · rw [h10]
    exact pm_node_50_wf
  · rw [h11]
    exact pm_node_51_wf
  · rw [h12]
    exact pm_node_52_wf
  · rw [h13]
    exact pm_node_53_wf
  · rw [h14]
    exact pm_node_54_wf
  · rw [h15]
    exact pm_node_55_wf
  · rw [h16]
    exact pm_node_56_wf
  · rw [h17]
    exact pm_node_57_wf
  · rw [h18]
    exact pm_node_58_wf
  · rw [h19]
    exact pm_node_59_wf
  · rw [h20]
    exact pm_node_60_wf
  · rw [h21]
    exact pm_node_61_wf
  · rw [h22]
    exact pm_node_62_wf
  · rw [h23]
    exact pm_node_63_wf
  · rw [h24]
    exact pm_node_64_wf
  · rw [h25]
    exact pm_node_65_wf
  · rw [h26]
    exact pm_node_66_wf
  · rw [h27]
    exact pm_node_67_wf
  · rw [h28]
    exact pm_node_68_wf
  · rw [h29]
    exact pm_node_69_wf
  · rw [h30]
    exact pm_node_70_wf
  · rw [h31]
    exact pm_node_71_wf
  · rw [h32]
    exact pm_node_72_wf
  · rw [h33]
    exact pm_node_73_wf
  · rw [h34]
    exact pm_node_74_wf
  · rw [h35]
    exact pm_node_75_wf
  · rw [h36]
    exact pm_node_76_wf
  · rw [h37]
    exact pm_node_77_wf
  · rw [h38]
    exact pm_node_78_wf
  · rw [h39]
    exact pm_node_79_wf

def pmChunk_2 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_norm_linear", ins := [4706, 4707], outs := [4708] }, { rank := 1, op := "OpName.FW_norm_linear", ins := [4706, 4707], outs := [4708] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4715, 4716], outs := [4717] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4715, 4716], outs := [4717] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4720, 4721], outs := [4722] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4720, 4721], outs := [4722] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4724, 4725], outs := [4726] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4724, 4725], outs := [4726] }, { rank := 0, op := "OpName.ChunkPrim", ins := [4708], outs := [7479], params := [0] }, { rank := 1, op := "OpName.ChunkPrim", ins := [4708], outs := [7480], params := [0] }, { rank := 0, op := "OpName.FW_view", ins := [4717], outs := [4718], params := [4096, 1] }, { rank := 1, op := "OpName.FW_view", ins := [4717], outs := [4718], params := [4096, 1] }, { rank := 0, op := "OpName.FW_view", ins := [4722], outs := [4723], params := [4096, 512] }, { rank := 1, op := "OpName.FW_view", ins := [4722], outs := [4723], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [4726], outs := [4727], params := [4096, 512] }, { rank := 1, op := "OpName.FW_view", ins := [4726], outs := [4727], params := [4096, 512] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [7479], outs := [7481, 7483, 7485], params := [8, 1] }, { rank := 1, op := "OpName.FW_topk_routing", ins := [7480], outs := [7482, 7484, 7486], params := [8, 1] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [4718], outs := [4719] }, { rank := 1, op := "OpName.FW_sigmoid", ins := [4718], outs := [4719] }, { rank := 0, op := "OpName.ChunkPrim", ins := [4723], outs := [7521], params := [0] }, { rank := 1, op := "OpName.ChunkPrim", ins := [4723], outs := [7522], params := [0] }, { rank := 0, op := "OpName.ChunkPrim", ins := [4727], outs := [7539], params := [0] }, { rank := 1, op := "OpName.ChunkPrim", ins := [4727], outs := [7540], params := [0] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [11941, 7481, 7483, 7487, 7489], outs := [7491], params := [64, 0, 32, 8] }, { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [11942, 7482, 7484, 7488, 7490], outs := [7492], params := [64, 32, 64, 8] }, { rank := 0, op := "OpName.FW_swiglu", ins := [7521, 7539], outs := [7543] }, { rank := 1, op := "OpName.FW_swiglu", ins := [7522, 7540], outs := [7544] }, { rank := 0, op := "OpName.AllGatherPrim", ins := [7491, 7492], outs := [4714], params := [0] }, { rank := 0, op := "OpName.FW_reshape", ins := [7543], outs := [7545], params := [2048, 512] }, { rank := 1, op := "OpName.FW_reshape", ins := [7544], outs := [7546], params := [2048, 512] }, { rank := 0, op := "OpName.AllGatherPrim", ins := [7545, 7546], outs := [4729], params := [0] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4729, 4730], outs := [4731] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4729, 4730], outs := [4731] }, { rank := 0, op := "OpName.FW_view", ins := [4731], outs := [4732], params := [4096, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [4731], outs := [4732], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [4719, 4732], outs := [4733] }, { rank := 1, op := "OpName.FW_mul", ins := [4719, 4732], outs := [4733] }, { rank := 0, op := "OpName.FW_add", ins := [4714, 4733], outs := [4734] }, { rank := 1, op := "OpName.FW_add", ins := [4714, 4733], outs := [4734] }]

theorem pmChunk_2_wf : ∀ n ∈ pmChunk_2, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_2, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_80_wf
  · rw [h1]
    exact pm_node_81_wf
  · rw [h2]
    exact pm_node_82_wf
  · rw [h3]
    exact pm_node_83_wf
  · rw [h4]
    exact pm_node_84_wf
  · rw [h5]
    exact pm_node_85_wf
  · rw [h6]
    exact pm_node_86_wf
  · rw [h7]
    exact pm_node_87_wf
  · rw [h8]
    exact pm_node_88_wf
  · rw [h9]
    exact pm_node_89_wf
  · rw [h10]
    exact pm_node_90_wf
  · rw [h11]
    exact pm_node_91_wf
  · rw [h12]
    exact pm_node_92_wf
  · rw [h13]
    exact pm_node_93_wf
  · rw [h14]
    exact pm_node_94_wf
  · rw [h15]
    exact pm_node_95_wf
  · rw [h16]
    exact pm_node_96_wf
  · rw [h17]
    exact pm_node_97_wf
  · rw [h18]
    exact pm_node_98_wf
  · rw [h19]
    exact pm_node_99_wf
  · rw [h20]
    exact pm_node_100_wf
  · rw [h21]
    exact pm_node_101_wf
  · rw [h22]
    exact pm_node_102_wf
  · rw [h23]
    exact pm_node_103_wf
  · rw [h24]
    exact pm_node_104_wf
  · rw [h25]
    exact pm_node_105_wf
  · rw [h26]
    exact pm_node_106_wf
  · rw [h27]
    exact pm_node_107_wf
  · rw [h28]
    exact pm_node_108_wf
  · rw [h29]
    exact pm_node_109_wf
  · rw [h30]
    exact pm_node_110_wf
  · rw [h31]
    exact pm_node_111_wf
  · rw [h32]
    exact pm_node_112_wf
  · rw [h33]
    exact pm_node_113_wf
  · rw [h34]
    exact pm_node_114_wf
  · rw [h35]
    exact pm_node_115_wf
  · rw [h36]
    exact pm_node_116_wf
  · rw [h37]
    exact pm_node_117_wf
  · rw [h38]
    exact pm_node_118_wf
  · rw [h39]
    exact pm_node_119_wf

def pmChunk_3 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_float", ins := [4734], outs := [4735] }, { rank := 1, op := "OpName.FW_float", ins := [4734], outs := [4735] }, { rank := 0, op := "OpName.FW_add", ins := [14648, 4735], outs := [4736] }, { rank := 1, op := "OpName.FW_add", ins := [14656, 4735], outs := [4736] }, { rank := 0, op := "OpName.FW_multiref", ins := [4736], outs := [14660, 14664], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [4736], outs := [14668, 14672], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [14660, 4737], outs := [4738] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [14668, 4737], outs := [4738] }, { rank := 0, op := "OpName.FW_multiref", ins := [4738], outs := [14677, 14681, 14685], params := [3] }, { rank := 1, op := "OpName.FW_multiref", ins := [4738], outs := [14689, 14693, 14697], params := [3] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14677, 4739], outs := [4740] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14681, 4741], outs := [4742] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14685, 4743], outs := [4744] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14689, 4739], outs := [4740] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14693, 4741], outs := [4742] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14697, 4743], outs := [4744] }, { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11854, 4745, 4740, 4742], outs := [4746, 4747], params := [16, 4] }, { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11854, 4745, 4740, 4742], outs := [4746, 4747], params := [16, 4] }, { rank := 0, op := "OpName.ChunkPrim", ins := [4744], outs := [7607], params := [0] }, { rank := 1, op := "OpName.ChunkPrim", ins := [4744], outs := [7608], params := [0] }, { rank := 0, op := "OpName.ChunkPrim", ins := [4746], outs := [7619], params := [0] }, { rank := 0, op := "OpName.ChunkPrim", ins := [4747], outs := [7621], params := [0] }, { rank := 1, op := "OpName.ChunkPrim", ins := [4746], outs := [7620], params := [0] }, { rank := 1, op := "OpName.ChunkPrim", ins := [4747], outs := [7622], params := [0] }, { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [7619, 7621, 7607, 4748, 4749], outs := [7623], params := [16, 4, 64, 64, 1, 512] }, { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [7620, 7622, 7608, 4748, 4749], outs := [7624], params := [16, 4, 64, 64, 1, 512] }, { rank := 0, op := "OpName.FW_reshape", ins := [7623], outs := [7625], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [7624], outs := [7626], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7625], outs := [7631], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [7626], outs := [7632], params := [2048, 1024] }, { rank := 0, op := "OpName.AllGatherPrim", ins := [7631, 7632], outs := [4752], params := [0] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4752, 4753], outs := [4754] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4752, 4753], outs := [4754] }, { rank := 0, op := "OpName.FW_view", ins := [4754], outs := [4755], params := [4096, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [4754], outs := [4755], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [4755], outs := [4756] }, { rank := 1, op := "OpName.FW_float", ins := [4755], outs := [4756] }, { rank := 0, op := "OpName.FW_add", ins := [14664, 4756], outs := [4757] }, { rank := 1, op := "OpName.FW_add", ins := [14672, 4756], outs := [4757] }, { rank := 0, op := "OpName.FW_multiref", ins := [4757], outs := [11889, 11890], params := [2] }]

theorem pmChunk_3_wf : ∀ n ∈ pmChunk_3, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_3, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_120_wf
  · rw [h1]
    exact pm_node_121_wf
  · rw [h2]
    exact pm_node_122_wf
  · rw [h3]
    exact pm_node_123_wf
  · rw [h4]
    exact pm_node_124_wf
  · rw [h5]
    exact pm_node_125_wf
  · rw [h6]
    exact pm_node_126_wf
  · rw [h7]
    exact pm_node_127_wf
  · rw [h8]
    exact pm_node_128_wf
  · rw [h9]
    exact pm_node_129_wf
  · rw [h10]
    exact pm_node_130_wf
  · rw [h11]
    exact pm_node_131_wf
  · rw [h12]
    exact pm_node_132_wf
  · rw [h13]
    exact pm_node_133_wf
  · rw [h14]
    exact pm_node_134_wf
  · rw [h15]
    exact pm_node_135_wf
  · rw [h16]
    exact pm_node_136_wf
  · rw [h17]
    exact pm_node_137_wf
  · rw [h18]
    exact pm_node_138_wf
  · rw [h19]
    exact pm_node_139_wf
  · rw [h20]
    exact pm_node_140_wf
  · rw [h21]
    exact pm_node_141_wf
  · rw [h22]
    exact pm_node_142_wf
  · rw [h23]
    exact pm_node_143_wf
  · rw [h24]
    exact pm_node_144_wf
  · rw [h25]
    exact pm_node_145_wf
  · rw [h26]
    exact pm_node_146_wf
  · rw [h27]
    exact pm_node_147_wf
  · rw [h28]
    exact pm_node_148_wf
  · rw [h29]
    exact pm_node_149_wf
  · rw [h30]
    exact pm_node_150_wf
  · rw [h31]
    exact pm_node_151_wf
  · rw [h32]
    exact pm_node_152_wf
  · rw [h33]
    exact pm_node_153_wf
  · rw [h34]
    exact pm_node_154_wf
  · rw [h35]
    exact pm_node_155_wf
  · rw [h36]
    exact pm_node_156_wf
  · rw [h37]
    exact pm_node_157_wf
  · rw [h38]
    exact pm_node_158_wf
  · rw [h39]
    exact pm_node_159_wf

def pmChunk_4 : List NodeDecl :=
  [{ rank := 1, op := "OpName.FW_multiref", ins := [4757], outs := [11889, 11890], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [11889, 4758], outs := [4759] }, { rank := 0, op := "OpName.ChunkPrim", ins := [11890], outs := [12011], params := [0] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [11889, 4758], outs := [4759] }, { rank := 1, op := "OpName.ChunkPrim", ins := [11890], outs := [12012], params := [0] }, { rank := 0, op := "OpName.FW_multiref", ins := [4759], outs := ((List.range 5).map (fun r => 11903 + r)), params := [5] }, { rank := 1, op := "OpName.FW_multiref", ins := [4759], outs := ((List.range 5).map (fun r => 11903 + r)), params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [11903], outs := [4760] }, { rank := 0, op := "OpName.ChunkPrim", ins := [11904], outs := [11977], params := [0] }, { rank := 0, op := "OpName.FW_reshape", ins := [11905], outs := [4769], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [11906], outs := [4774], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [11907], outs := [4778], params := [4096, 1024] }, { rank := 1, op := "OpName.FW_float", ins := [11903], outs := [4760] }, { rank := 1, op := "OpName.ChunkPrim", ins := [11904], outs := [11978], params := [0] }, { rank := 1, op := "OpName.FW_reshape", ins := [11905], outs := [4769], params := [4096, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [11906], outs := [4774], params := [4096, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [11907], outs := [4778], params := [4096, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [4760, 4761], outs := [4762] }, { rank := 1, op := "OpName.FW_norm_linear", ins := [4760, 4761], outs := [4762] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4769, 4770], outs := [4771] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4769, 4770], outs := [4771] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4774, 4775], outs := [4776] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4774, 4775], outs := [4776] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4778, 4779], outs := [4780] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4778, 4779], outs := [4780] }, { rank := 0, op := "OpName.ChunkPrim", ins := [4762], outs := [7665], params := [0] }, { rank := 1, op := "OpName.ChunkPrim", ins := [4762], outs := [7666], params := [0] }, { rank := 0, op := "OpName.FW_view", ins := [4771], outs := [4772], params := [4096, 1] }, { rank := 1, op := "OpName.FW_view", ins := [4771], outs := [4772], params := [4096, 1] }, { rank := 0, op := "OpName.FW_view", ins := [4776], outs := [4777], params := [4096, 512] }, { rank := 1, op := "OpName.FW_view", ins := [4776], outs := [4777], params := [4096, 512] }, { rank := 0, op := "OpName.FW_view", ins := [4780], outs := [4781], params := [4096, 512] }, { rank := 1, op := "OpName.FW_view", ins := [4780], outs := [4781], params := [4096, 512] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [7665], outs := [7667, 7669, 7671], params := [8, 1] }, { rank := 1, op := "OpName.FW_topk_routing", ins := [7666], outs := [7668, 7670, 7672], params := [8, 1] }, { rank := 0, op := "OpName.ChunkPrim", ins := [4772], outs := [7689], params := [0] }, { rank := 1, op := "OpName.ChunkPrim", ins := [4772], outs := [7690], params := [0] }, { rank := 0, op := "OpName.ChunkPrim", ins := [4777], outs := [7707], params := [0] }, { rank := 1, op := "OpName.ChunkPrim", ins := [4777], outs := [7708], params := [0] }, { rank := 0, op := "OpName.ChunkPrim", ins := [4781], outs := [7725], params := [0] }]

theorem pmChunk_4_wf : ∀ n ∈ pmChunk_4, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_4, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_160_wf
  · rw [h1]
    exact pm_node_161_wf
  · rw [h2]
    exact pm_node_162_wf
  · rw [h3]
    exact pm_node_163_wf
  · rw [h4]
    exact pm_node_164_wf
  · rw [h5]
    exact pm_node_165_wf
  · rw [h6]
    exact pm_node_166_wf
  · rw [h7]
    exact pm_node_167_wf
  · rw [h8]
    exact pm_node_168_wf
  · rw [h9]
    exact pm_node_169_wf
  · rw [h10]
    exact pm_node_170_wf
  · rw [h11]
    exact pm_node_171_wf
  · rw [h12]
    exact pm_node_172_wf
  · rw [h13]
    exact pm_node_173_wf
  · rw [h14]
    exact pm_node_174_wf
  · rw [h15]
    exact pm_node_175_wf
  · rw [h16]
    exact pm_node_176_wf
  · rw [h17]
    exact pm_node_177_wf
  · rw [h18]
    exact pm_node_178_wf
  · rw [h19]
    exact pm_node_179_wf
  · rw [h20]
    exact pm_node_180_wf
  · rw [h21]
    exact pm_node_181_wf
  · rw [h22]
    exact pm_node_182_wf
  · rw [h23]
    exact pm_node_183_wf
  · rw [h24]
    exact pm_node_184_wf
  · rw [h25]
    exact pm_node_185_wf
  · rw [h26]
    exact pm_node_186_wf
  · rw [h27]
    exact pm_node_187_wf
  · rw [h28]
    exact pm_node_188_wf
  · rw [h29]
    exact pm_node_189_wf
  · rw [h30]
    exact pm_node_190_wf
  · rw [h31]
    exact pm_node_191_wf
  · rw [h32]
    exact pm_node_192_wf
  · rw [h33]
    exact pm_node_193_wf
  · rw [h34]
    exact pm_node_194_wf
  · rw [h35]
    exact pm_node_195_wf
  · rw [h36]
    exact pm_node_196_wf
  · rw [h37]
    exact pm_node_197_wf
  · rw [h38]
    exact pm_node_198_wf
  · rw [h39]
    exact pm_node_199_wf

def pmChunk_5 : List NodeDecl :=
  [{ rank := 1, op := "OpName.ChunkPrim", ins := [4781], outs := [7726], params := [0] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [11977, 7667, 7669, 7673, 7675], outs := [7677], params := [64, 0, 32, 8] }, { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [11978, 7668, 7670, 7674, 7676], outs := [7678], params := [64, 32, 64, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [7689], outs := [7691] }, { rank := 1, op := "OpName.FW_sigmoid", ins := [7690], outs := [7692] }, { rank := 0, op := "OpName.FW_swiglu", ins := [7707, 7725], outs := [7729] }, { rank := 1, op := "OpName.FW_swiglu", ins := [7708, 7726], outs := [7730] }, { rank := 0, op := "OpName.FW_reshape", ins := [7729], outs := [7731], params := [2048, 512] }, { rank := 1, op := "OpName.FW_reshape", ins := [7730], outs := [7732], params := [2048, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [7731, 4784], outs := [7737] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [7732, 4784], outs := [7738] }, { rank := 0, op := "OpName.FW_view", ins := [7737], outs := [7747], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [7738], outs := [7748], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [7691, 7747], outs := [7751] }, { rank := 1, op := "OpName.FW_mul", ins := [7692, 7748], outs := [7752] }, { rank := 0, op := "OpName.FW_add", ins := [7677, 7751], outs := [7755] }, { rank := 1, op := "OpName.FW_add", ins := [7678, 7752], outs := [7756] }, { rank := 0, op := "OpName.FW_float", ins := [7755], outs := [7761] }, { rank := 1, op := "OpName.FW_float", ins := [7756], outs := [7762] }, { rank := 0, op := "OpName.FW_add", ins := [12011, 7761], outs := [7765] }, { rank := 1, op := "OpName.FW_add", ins := [12012, 7762], outs := [7766] }, { rank := 0, op := "OpName.FW_multiref", ins := [7765], outs := [14701, 14705], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [7766], outs := [14709, 14713], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [14701, 4791], outs := [7769] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [14709, 4791], outs := [7770] }, { rank := 0, op := "OpName.FW_multiref", ins := [7769], outs := [14718, 14722, 14726], params := [3] }, { rank := 1, op := "OpName.FW_multiref", ins := [7770], outs := [14731, 14735, 14739], params := [3] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14718, 4793], outs := [7771] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14722, 4795], outs := [7783] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14726, 4797], outs := [7793] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14731, 4793], outs := [7772] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14735, 4795], outs := [7784] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14739, 4797], outs := [7794] }, { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11855, 7803, 7771, 7783], outs := [7805, 7807], params := [16, 4] }, { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11855, 7804, 7772, 7784], outs := [7806, 7808], params := [16, 4] }, { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [7805, 7807, 7793, 4802, 4803], outs := [7809], params := [16, 4, 64, 64, 1, 512] }, { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [7806, 7808, 7794, 4802, 4803], outs := [7810], params := [16, 4, 64, 64, 1, 512] }, { rank := 0, op := "OpName.FW_reshape", ins := [7809], outs := [7811], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [7810], outs := [7812], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7811], outs := [7817], params := [2048, 1024] }]

theorem pmChunk_5_wf : ∀ n ∈ pmChunk_5, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_5, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_200_wf
  · rw [h1]
    exact pm_node_201_wf
  · rw [h2]
    exact pm_node_202_wf
  · rw [h3]
    exact pm_node_203_wf
  · rw [h4]
    exact pm_node_204_wf
  · rw [h5]
    exact pm_node_205_wf
  · rw [h6]
    exact pm_node_206_wf
  · rw [h7]
    exact pm_node_207_wf
  · rw [h8]
    exact pm_node_208_wf
  · rw [h9]
    exact pm_node_209_wf
  · rw [h10]
    exact pm_node_210_wf
  · rw [h11]
    exact pm_node_211_wf
  · rw [h12]
    exact pm_node_212_wf
  · rw [h13]
    exact pm_node_213_wf
  · rw [h14]
    exact pm_node_214_wf
  · rw [h15]
    exact pm_node_215_wf
  · rw [h16]
    exact pm_node_216_wf
  · rw [h17]
    exact pm_node_217_wf
  · rw [h18]
    exact pm_node_218_wf
  · rw [h19]
    exact pm_node_219_wf
  · rw [h20]
    exact pm_node_220_wf
  · rw [h21]
    exact pm_node_221_wf
  · rw [h22]
    exact pm_node_222_wf
  · rw [h23]
    exact pm_node_223_wf
  · rw [h24]
    exact pm_node_224_wf
  · rw [h25]
    exact pm_node_225_wf
  · rw [h26]
    exact pm_node_226_wf
  · rw [h27]
    exact pm_node_227_wf
  · rw [h28]
    exact pm_node_228_wf
  · rw [h29]
    exact pm_node_229_wf
  · rw [h30]
    exact pm_node_230_wf
  · rw [h31]
    exact pm_node_231_wf
  · rw [h32]
    exact pm_node_232_wf
  · rw [h33]
    exact pm_node_233_wf
  · rw [h34]
    exact pm_node_234_wf
  · rw [h35]
    exact pm_node_235_wf
  · rw [h36]
    exact pm_node_236_wf
  · rw [h37]
    exact pm_node_237_wf
  · rw [h38]
    exact pm_node_238_wf
  · rw [h39]
    exact pm_node_239_wf

def pmChunk_6 : List NodeDecl :=
  [{ rank := 1, op := "OpName.FW_reshape", ins := [7812], outs := [7818], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [7817, 4807], outs := [7821] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [7818, 4807], outs := [7822] }, { rank := 0, op := "OpName.FW_view", ins := [7821], outs := [7831], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [7822], outs := [7832], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [7831], outs := [7835] }, { rank := 1, op := "OpName.FW_float", ins := [7832], outs := [7836] }, { rank := 0, op := "OpName.FW_add", ins := [14705, 7835], outs := [7839] }, { rank := 1, op := "OpName.FW_add", ins := [14713, 7836], outs := [7840] }, { rank := 0, op := "OpName.FW_multiref", ins := [7839], outs := [14743, 14747], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [7840], outs := [14751, 14755], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [14743, 4812], outs := [7843] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [14751, 4812], outs := [7844] }, { rank := 0, op := "OpName.FW_multiref", ins := [7843], outs := [14762, 14766, 14770, 14774, 14778], params := [5] }, { rank := 1, op := "OpName.FW_multiref", ins := [7844], outs := [14785, 14789, 14793, 14797, 14801], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [14762], outs := [7845] }, { rank := 0, op := "OpName.FW_reshape", ins := [14770], outs := [7865], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [14774], outs := [7879], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [14778], outs := [7897], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_float", ins := [14785], outs := [7846] }, { rank := 1, op := "OpName.FW_reshape", ins := [14793], outs := [7866], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [14797], outs := [7880], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [14801], outs := [7898], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [7845, 4815], outs := [7851] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [7865, 4824], outs := [7869] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [7879, 4829], outs := [7883] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [7897, 4833], outs := [7901] }, { rank := 1, op := "OpName.FW_norm_linear", ins := [7846, 4815], outs := [7852] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [7866, 4824], outs := [7870] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [7880, 4829], outs := [7884] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [7898, 4833], outs := [7902] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [7851], outs := [7853, 7855, 7857], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [7869], outs := [7875], params := [2048, 1] }, { rank := 0, op := "OpName.FW_view", ins := [7883], outs := [7893], params := [2048, 512] }, { rank := 0, op := "OpName.FW_view", ins := [7901], outs := [7911], params := [2048, 512] }, { rank := 1, op := "OpName.FW_topk_routing", ins := [7852], outs := [7854, 7856, 7858], params := [8, 1] }, { rank := 1, op := "OpName.FW_view", ins := [7870], outs := [7876], params := [2048, 1] }, { rank := 1, op := "OpName.FW_view", ins := [7884], outs := [7894], params := [2048, 512] }, { rank := 1, op := "OpName.FW_view", ins := [7902], outs := [7912], params := [2048, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [14766, 7853, 7855, 7859, 7861], outs := [7863], params := [64, 0, 32, 8] }]

theorem pmChunk_6_wf : ∀ n ∈ pmChunk_6, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_6, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_240_wf
  · rw [h1]
    exact pm_node_241_wf
  · rw [h2]
    exact pm_node_242_wf
  · rw [h3]
    exact pm_node_243_wf
  · rw [h4]
    exact pm_node_244_wf
  · rw [h5]
    exact pm_node_245_wf
  · rw [h6]
    exact pm_node_246_wf
  · rw [h7]
    exact pm_node_247_wf
  · rw [h8]
    exact pm_node_248_wf
  · rw [h9]
    exact pm_node_249_wf
  · rw [h10]
    exact pm_node_250_wf
  · rw [h11]
    exact pm_node_251_wf
  · rw [h12]
    exact pm_node_252_wf
  · rw [h13]
    exact pm_node_253_wf
  · rw [h14]
    exact pm_node_254_wf
  · rw [h15]
    exact pm_node_255_wf
  · rw [h16]
    exact pm_node_256_wf
  · rw [h17]
    exact pm_node_257_wf
  · rw [h18]
    exact pm_node_258_wf
  · rw [h19]
    exact pm_node_259_wf
  · rw [h20]
    exact pm_node_260_wf
  · rw [h21]
    exact pm_node_261_wf
  · rw [h22]
    exact pm_node_262_wf
  · rw [h23]
    exact pm_node_263_wf
  · rw [h24]
    exact pm_node_264_wf
  · rw [h25]
    exact pm_node_265_wf
  · rw [h26]
    exact pm_node_266_wf
  · rw [h27]
    exact pm_node_267_wf
  · rw [h28]
    exact pm_node_268_wf
  · rw [h29]
    exact pm_node_269_wf
  · rw [h30]
    exact pm_node_270_wf
  · rw [h31]
    exact pm_node_271_wf
  · rw [h32]
    exact pm_node_272_wf
  · rw [h33]
    exact pm_node_273_wf
  · rw [h34]
    exact pm_node_274_wf
  · rw [h35]
    exact pm_node_275_wf
  · rw [h36]
    exact pm_node_276_wf
  · rw [h37]
    exact pm_node_277_wf
  · rw [h38]
    exact pm_node_278_wf
  · rw [h39]
    exact pm_node_279_wf

def pmChunk_7 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_sigmoid", ins := [7875], outs := [7877] }, { rank := 0, op := "OpName.FW_swiglu", ins := [7893, 7911], outs := [7915] }, { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [14789, 7854, 7856, 7860, 7862], outs := [7864], params := [64, 32, 64, 8] }, { rank := 1, op := "OpName.FW_sigmoid", ins := [7876], outs := [7878] }, { rank := 1, op := "OpName.FW_swiglu", ins := [7894, 7912], outs := [7916] }, { rank := 0, op := "OpName.FW_reshape", ins := [7915], outs := [7917], params := [2048, 512] }, { rank := 1, op := "OpName.FW_reshape", ins := [7916], outs := [7918], params := [2048, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [7917, 4838], outs := [7923] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [7918, 4838], outs := [7924] }, { rank := 0, op := "OpName.FW_view", ins := [7923], outs := [7933], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [7924], outs := [7934], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [7877, 7933], outs := [7937] }, { rank := 1, op := "OpName.FW_mul", ins := [7878, 7934], outs := [7938] }, { rank := 0, op := "OpName.FW_add", ins := [7863, 7937], outs := [7941] }, { rank := 1, op := "OpName.FW_add", ins := [7864, 7938], outs := [7942] }, { rank := 0, op := "OpName.FW_float", ins := [7941], outs := [7947] }, { rank := 1, op := "OpName.FW_float", ins := [7942], outs := [7948] }, { rank := 0, op := "OpName.FW_add", ins := [14747, 7947], outs := [7951] }, { rank := 1, op := "OpName.FW_add", ins := [14755, 7948], outs := [7952] }, { rank := 0, op := "OpName.FW_multiref", ins := [7951], outs := [14805, 14809], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [7952], outs := [14813, 14817], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [14805, 4845], outs := [7955] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [14813, 4845], outs := [7956] }, { rank := 0, op := "OpName.FW_multiref", ins := [7955], outs := [14822, 14826, 14830], params := [3] }, { rank := 1, op := "OpName.FW_multiref", ins := [7956], outs := [14835, 14839, 14843], params := [3] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14822, 4847], outs := [7957] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14826, 4849], outs := [7969] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14830, 4851], outs := [7979] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14835, 4847], outs := [7958] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14839, 4849], outs := [7970] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14843, 4851], outs := [7980] }, { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11856, 7989, 7957, 7969], outs := [7991, 7993], params := [16, 4] }, { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11856, 7990, 7958, 7970], outs := [7992, 7994], params := [16, 4] }, { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [7991, 7993, 7979, 4856, 4857], outs := [7995], params := [16, 4, 64, 64, 1, 512] }, { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [7992, 7994, 7980, 4856, 4857], outs := [7996], params := [16, 4, 64, 64, 1, 512] }, { rank := 0, op := "OpName.FW_reshape", ins := [7995], outs := [7997], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [7996], outs := [7998], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [7997], outs := [8003], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [7998], outs := [8004], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8003, 4861], outs := [8007] }]

theorem pmChunk_7_wf : ∀ n ∈ pmChunk_7, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_7, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_280_wf
  · rw [h1]
    exact pm_node_281_wf
  · rw [h2]
    exact pm_node_282_wf
  · rw [h3]
    exact pm_node_283_wf
  · rw [h4]
    exact pm_node_284_wf
  · rw [h5]
    exact pm_node_285_wf
  · rw [h6]
    exact pm_node_286_wf
  · rw [h7]
    exact pm_node_287_wf
  · rw [h8]
    exact pm_node_288_wf
  · rw [h9]
    exact pm_node_289_wf
  · rw [h10]
    exact pm_node_290_wf
  · rw [h11]
    exact pm_node_291_wf
  · rw [h12]
    exact pm_node_292_wf
  · rw [h13]
    exact pm_node_293_wf
  · rw [h14]
    exact pm_node_294_wf
  · rw [h15]
    exact pm_node_295_wf
  · rw [h16]
    exact pm_node_296_wf
  · rw [h17]
    exact pm_node_297_wf
  · rw [h18]
    exact pm_node_298_wf
  · rw [h19]
    exact pm_node_299_wf
  · rw [h20]
    exact pm_node_300_wf
  · rw [h21]
    exact pm_node_301_wf
  · rw [h22]
    exact pm_node_302_wf
  · rw [h23]
    exact pm_node_303_wf
  · rw [h24]
    exact pm_node_304_wf
  · rw [h25]
    exact pm_node_305_wf
  · rw [h26]
    exact pm_node_306_wf
  · rw [h27]
    exact pm_node_307_wf
  · rw [h28]
    exact pm_node_308_wf
  · rw [h29]
    exact pm_node_309_wf
  · rw [h30]
    exact pm_node_310_wf
  · rw [h31]
    exact pm_node_311_wf
  · rw [h32]
    exact pm_node_312_wf
  · rw [h33]
    exact pm_node_313_wf
  · rw [h34]
    exact pm_node_314_wf
  · rw [h35]
    exact pm_node_315_wf
  · rw [h36]
    exact pm_node_316_wf
  · rw [h37]
    exact pm_node_317_wf
  · rw [h38]
    exact pm_node_318_wf
  · rw [h39]
    exact pm_node_319_wf

def pmChunk_8 : List NodeDecl :=
  [{ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8004, 4861], outs := [8008] }, { rank := 0, op := "OpName.FW_view", ins := [8007], outs := [8017], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [8008], outs := [8018], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [8017], outs := [8021] }, { rank := 1, op := "OpName.FW_float", ins := [8018], outs := [8022] }, { rank := 0, op := "OpName.FW_add", ins := [14809, 8021], outs := [8025] }, { rank := 1, op := "OpName.FW_add", ins := [14817, 8022], outs := [8026] }, { rank := 0, op := "OpName.FW_multiref", ins := [8025], outs := [14847, 14851], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [8026], outs := [14855, 14859], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [14847, 4866], outs := [8029] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [14855, 4866], outs := [8030] }, { rank := 0, op := "OpName.FW_multiref", ins := [8029], outs := [14866, 14870, 14874, 14878, 14882], params := [5] }, { rank := 1, op := "OpName.FW_multiref", ins := [8030], outs := [14889, 14893, 14897, 14901, 14905], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [14866], outs := [8031] }, { rank := 0, op := "OpName.FW_reshape", ins := [14874], outs := [8051], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [14878], outs := [8065], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [14882], outs := [8083], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_float", ins := [14889], outs := [8032] }, { rank := 1, op := "OpName.FW_reshape", ins := [14897], outs := [8052], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [14901], outs := [8066], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [14905], outs := [8084], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [8031, 4869], outs := [8037] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8051, 4878], outs := [8055] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8065, 4883], outs := [8069] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8083, 4887], outs := [8087] }, { rank := 1, op := "OpName.FW_norm_linear", ins := [8032, 4869], outs := [8038] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8052, 4878], outs := [8056] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8066, 4883], outs := [8070] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8084, 4887], outs := [8088] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [8037], outs := [8039, 8041, 8043], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [8055], outs := [8061], params := [2048, 1] }, { rank := 0, op := "OpName.FW_view", ins := [8069], outs := [8079], params := [2048, 512] }, { rank := 0, op := "OpName.FW_view", ins := [8087], outs := [8097], params := [2048, 512] }, { rank := 1, op := "OpName.FW_topk_routing", ins := [8038], outs := [8040, 8042, 8044], params := [8, 1] }, { rank := 1, op := "OpName.FW_view", ins := [8056], outs := [8062], params := [2048, 1] }, { rank := 1, op := "OpName.FW_view", ins := [8070], outs := [8080], params := [2048, 512] }, { rank := 1, op := "OpName.FW_view", ins := [8088], outs := [8098], params := [2048, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [14870, 8039, 8041, 8045, 8047], outs := [8049], params := [64, 0, 32, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [8061], outs := [8063] }, { rank := 0, op := "OpName.FW_swiglu", ins := [8079, 8097], outs := [8101] }]

theorem pmChunk_8_wf : ∀ n ∈ pmChunk_8, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_8, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_320_wf
  · rw [h1]
    exact pm_node_321_wf
  · rw [h2]
    exact pm_node_322_wf
  · rw [h3]
    exact pm_node_323_wf
  · rw [h4]
    exact pm_node_324_wf
  · rw [h5]
    exact pm_node_325_wf
  · rw [h6]
    exact pm_node_326_wf
  · rw [h7]
    exact pm_node_327_wf
  · rw [h8]
    exact pm_node_328_wf
  · rw [h9]
    exact pm_node_329_wf
  · rw [h10]
    exact pm_node_330_wf
  · rw [h11]
    exact pm_node_331_wf
  · rw [h12]
    exact pm_node_332_wf
  · rw [h13]
    exact pm_node_333_wf
  · rw [h14]
    exact pm_node_334_wf
  · rw [h15]
    exact pm_node_335_wf
  · rw [h16]
    exact pm_node_336_wf
  · rw [h17]
    exact pm_node_337_wf
  · rw [h18]
    exact pm_node_338_wf
  · rw [h19]
    exact pm_node_339_wf
  · rw [h20]
    exact pm_node_340_wf
  · rw [h21]
    exact pm_node_341_wf
  · rw [h22]
    exact pm_node_342_wf
  · rw [h23]
    exact pm_node_343_wf
  · rw [h24]
    exact pm_node_344_wf
  · rw [h25]
    exact pm_node_345_wf
  · rw [h26]
    exact pm_node_346_wf
  · rw [h27]
    exact pm_node_347_wf
  · rw [h28]
    exact pm_node_348_wf
  · rw [h29]
    exact pm_node_349_wf
  · rw [h30]
    exact pm_node_350_wf
  · rw [h31]
    exact pm_node_351_wf
  · rw [h32]
    exact pm_node_352_wf
  · rw [h33]
    exact pm_node_353_wf
  · rw [h34]
    exact pm_node_354_wf
  · rw [h35]
    exact pm_node_355_wf
  · rw [h36]
    exact pm_node_356_wf
  · rw [h37]
    exact pm_node_357_wf
  · rw [h38]
    exact pm_node_358_wf
  · rw [h39]
    exact pm_node_359_wf

def pmChunk_9 : List NodeDecl :=
  [{ rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [14893, 8040, 8042, 8046, 8048], outs := [8050], params := [64, 32, 64, 8] }, { rank := 1, op := "OpName.FW_sigmoid", ins := [8062], outs := [8064] }, { rank := 1, op := "OpName.FW_swiglu", ins := [8080, 8098], outs := [8102] }, { rank := 0, op := "OpName.FW_reshape", ins := [8101], outs := [8103], params := [2048, 512] }, { rank := 1, op := "OpName.FW_reshape", ins := [8102], outs := [8104], params := [2048, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8103, 4892], outs := [8109] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8104, 4892], outs := [8110] }, { rank := 0, op := "OpName.FW_view", ins := [8109], outs := [8119], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [8110], outs := [8120], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [8063, 8119], outs := [8123] }, { rank := 1, op := "OpName.FW_mul", ins := [8064, 8120], outs := [8124] }, { rank := 0, op := "OpName.FW_add", ins := [8049, 8123], outs := [8127] }, { rank := 1, op := "OpName.FW_add", ins := [8050, 8124], outs := [8128] }, { rank := 0, op := "OpName.FW_float", ins := [8127], outs := [8133] }, { rank := 1, op := "OpName.FW_float", ins := [8128], outs := [8134] }, { rank := 0, op := "OpName.FW_add", ins := [14851, 8133], outs := [8137] }, { rank := 1, op := "OpName.FW_add", ins := [14859, 8134], outs := [8138] }, { rank := 0, op := "OpName.FW_multiref", ins := [8137], outs := [14909, 14913], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [8138], outs := [14917, 14921], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [14909, 4899], outs := [8141] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [14917, 4899], outs := [8142] }, { rank := 0, op := "OpName.FW_multiref", ins := [8141], outs := [14926, 14930, 14934], params := [3] }, { rank := 1, op := "OpName.FW_multiref", ins := [8142], outs := [14939, 14943, 14947], params := [3] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14926, 4901], outs := [8143] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14930, 4903], outs := [8155] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14934, 4905], outs := [8165] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14939, 4901], outs := [8144] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14943, 4903], outs := [8156] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14947, 4905], outs := [8166] }, { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11857, 8175, 8143, 8155], outs := [8177, 8179], params := [16, 4] }, { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11857, 8176, 8144, 8156], outs := [8178, 8180], params := [16, 4] }, { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [8177, 8179, 8165, 4910, 4911], outs := [8181], params := [16, 4, 64, 64, 1, 512] }, { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [8178, 8180, 8166, 4910, 4911], outs := [8182], params := [16, 4, 64, 64, 1, 512] }, { rank := 0, op := "OpName.FW_reshape", ins := [8181], outs := [8183], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [8182], outs := [8184], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8183], outs := [8189], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [8184], outs := [8190], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8189, 4915], outs := [8193] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8190, 4915], outs := [8194] }, { rank := 0, op := "OpName.FW_view", ins := [8193], outs := [8203], params := [2048, 1024] }]

theorem pmChunk_9_wf : ∀ n ∈ pmChunk_9, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_9, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_360_wf
  · rw [h1]
    exact pm_node_361_wf
  · rw [h2]
    exact pm_node_362_wf
  · rw [h3]
    exact pm_node_363_wf
  · rw [h4]
    exact pm_node_364_wf
  · rw [h5]
    exact pm_node_365_wf
  · rw [h6]
    exact pm_node_366_wf
  · rw [h7]
    exact pm_node_367_wf
  · rw [h8]
    exact pm_node_368_wf
  · rw [h9]
    exact pm_node_369_wf
  · rw [h10]
    exact pm_node_370_wf
  · rw [h11]
    exact pm_node_371_wf
  · rw [h12]
    exact pm_node_372_wf
  · rw [h13]
    exact pm_node_373_wf
  · rw [h14]
    exact pm_node_374_wf
  · rw [h15]
    exact pm_node_375_wf
  · rw [h16]
    exact pm_node_376_wf
  · rw [h17]
    exact pm_node_377_wf
  · rw [h18]
    exact pm_node_378_wf
  · rw [h19]
    exact pm_node_379_wf
  · rw [h20]
    exact pm_node_380_wf
  · rw [h21]
    exact pm_node_381_wf
  · rw [h22]
    exact pm_node_382_wf
  · rw [h23]
    exact pm_node_383_wf
  · rw [h24]
    exact pm_node_384_wf
  · rw [h25]
    exact pm_node_385_wf
  · rw [h26]
    exact pm_node_386_wf
  · rw [h27]
    exact pm_node_387_wf
  · rw [h28]
    exact pm_node_388_wf
  · rw [h29]
    exact pm_node_389_wf
  · rw [h30]
    exact pm_node_390_wf
  · rw [h31]
    exact pm_node_391_wf
  · rw [h32]
    exact pm_node_392_wf
  · rw [h33]
    exact pm_node_393_wf
  · rw [h34]
    exact pm_node_394_wf
  · rw [h35]
    exact pm_node_395_wf
  · rw [h36]
    exact pm_node_396_wf
  · rw [h37]
    exact pm_node_397_wf
  · rw [h38]
    exact pm_node_398_wf
  · rw [h39]
    exact pm_node_399_wf

def pmChunk_10 : List NodeDecl :=
  [{ rank := 1, op := "OpName.FW_view", ins := [8194], outs := [8204], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [8203], outs := [8207] }, { rank := 1, op := "OpName.FW_float", ins := [8204], outs := [8208] }, { rank := 0, op := "OpName.FW_add", ins := [14913, 8207], outs := [8211] }, { rank := 1, op := "OpName.FW_add", ins := [14921, 8208], outs := [8212] }, { rank := 0, op := "OpName.FW_multiref", ins := [8211], outs := [14951, 14955], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [8212], outs := [14959, 14963], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [14951, 4920], outs := [8215] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [14959, 4920], outs := [8216] }, { rank := 0, op := "OpName.FW_multiref", ins := [8215], outs := [14970, 14974, 14978, 14982, 14986], params := [5] }, { rank := 1, op := "OpName.FW_multiref", ins := [8216], outs := [14993, 14997, 15001, 15005, 15009], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [14970], outs := [8217] }, { rank := 0, op := "OpName.FW_reshape", ins := [14978], outs := [8237], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [14982], outs := [8251], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [14986], outs := [8269], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_float", ins := [14993], outs := [8218] }, { rank := 1, op := "OpName.FW_reshape", ins := [15001], outs := [8238], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [15005], outs := [8252], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [15009], outs := [8270], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [8217, 4923], outs := [8223] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8237, 4932], outs := [8241] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8251, 4937], outs := [8255] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8269, 4941], outs := [8273] }, { rank := 1, op := "OpName.FW_norm_linear", ins := [8218, 4923], outs := [8224] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8238, 4932], outs := [8242] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8252, 4937], outs := [8256] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8270, 4941], outs := [8274] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [8223], outs := [8225, 8227, 8229], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [8241], outs := [8247], params := [2048, 1] }, { rank := 0, op := "OpName.FW_view", ins := [8255], outs := [8265], params := [2048, 512] }, { rank := 0, op := "OpName.FW_view", ins := [8273], outs := [8283], params := [2048, 512] }, { rank := 1, op := "OpName.FW_topk_routing", ins := [8224], outs := [8226, 8228, 8230], params := [8, 1] }, { rank := 1, op := "OpName.FW_view", ins := [8242], outs := [8248], params := [2048, 1] }, { rank := 1, op := "OpName.FW_view", ins := [8256], outs := [8266], params := [2048, 512] }, { rank := 1, op := "OpName.FW_view", ins := [8274], outs := [8284], params := [2048, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [14974, 8225, 8227, 8231, 8233], outs := [8235], params := [64, 0, 32, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [8247], outs := [8249] }, { rank := 0, op := "OpName.FW_swiglu", ins := [8265, 8283], outs := [8287] }, { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [14997, 8226, 8228, 8232, 8234], outs := [8236], params := [64, 32, 64, 8] }, { rank := 1, op := "OpName.FW_sigmoid", ins := [8248], outs := [8250] }]

theorem pmChunk_10_wf : ∀ n ∈ pmChunk_10, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_10, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_400_wf
  · rw [h1]
    exact pm_node_401_wf
  · rw [h2]
    exact pm_node_402_wf
  · rw [h3]
    exact pm_node_403_wf
  · rw [h4]
    exact pm_node_404_wf
  · rw [h5]
    exact pm_node_405_wf
  · rw [h6]
    exact pm_node_406_wf
  · rw [h7]
    exact pm_node_407_wf
  · rw [h8]
    exact pm_node_408_wf
  · rw [h9]
    exact pm_node_409_wf
  · rw [h10]
    exact pm_node_410_wf
  · rw [h11]
    exact pm_node_411_wf
  · rw [h12]
    exact pm_node_412_wf
  · rw [h13]
    exact pm_node_413_wf
  · rw [h14]
    exact pm_node_414_wf
  · rw [h15]
    exact pm_node_415_wf
  · rw [h16]
    exact pm_node_416_wf
  · rw [h17]
    exact pm_node_417_wf
  · rw [h18]
    exact pm_node_418_wf
  · rw [h19]
    exact pm_node_419_wf
  · rw [h20]
    exact pm_node_420_wf
  · rw [h21]
    exact pm_node_421_wf
  · rw [h22]
    exact pm_node_422_wf
  · rw [h23]
    exact pm_node_423_wf
  · rw [h24]
    exact pm_node_424_wf
  · rw [h25]
    exact pm_node_425_wf
  · rw [h26]
    exact pm_node_426_wf
  · rw [h27]
    exact pm_node_427_wf
  · rw [h28]
    exact pm_node_428_wf
  · rw [h29]
    exact pm_node_429_wf
  · rw [h30]
    exact pm_node_430_wf
  · rw [h31]
    exact pm_node_431_wf
  · rw [h32]
    exact pm_node_432_wf
  · rw [h33]
    exact pm_node_433_wf
  · rw [h34]
    exact pm_node_434_wf
  · rw [h35]
    exact pm_node_435_wf
  · rw [h36]
    exact pm_node_436_wf
  · rw [h37]
    exact pm_node_437_wf
  · rw [h38]
    exact pm_node_438_wf
  · rw [h39]
    exact pm_node_439_wf

def pmChunk_11 : List NodeDecl :=
  [{ rank := 1, op := "OpName.FW_swiglu", ins := [8266, 8284], outs := [8288] }, { rank := 0, op := "OpName.FW_reshape", ins := [8287], outs := [8289], params := [2048, 512] }, { rank := 1, op := "OpName.FW_reshape", ins := [8288], outs := [8290], params := [2048, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8289, 4946], outs := [8295] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8290, 4946], outs := [8296] }, { rank := 0, op := "OpName.FW_view", ins := [8295], outs := [8305], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [8296], outs := [8306], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [8249, 8305], outs := [8309] }, { rank := 1, op := "OpName.FW_mul", ins := [8250, 8306], outs := [8310] }, { rank := 0, op := "OpName.FW_add", ins := [8235, 8309], outs := [8313] }, { rank := 1, op := "OpName.FW_add", ins := [8236, 8310], outs := [8314] }, { rank := 0, op := "OpName.FW_float", ins := [8313], outs := [8319] }, { rank := 1, op := "OpName.FW_float", ins := [8314], outs := [8320] }, { rank := 0, op := "OpName.FW_add", ins := [14955, 8319], outs := [8323] }, { rank := 1, op := "OpName.FW_add", ins := [14963, 8320], outs := [8324] }, { rank := 0, op := "OpName.FW_multiref", ins := [8323], outs := [15013, 15017], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [8324], outs := [15021, 15025], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [15013, 4953], outs := [8327] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [15021, 4953], outs := [8328] }, { rank := 0, op := "OpName.FW_multiref", ins := [8327], outs := [15030, 15034, 15038], params := [3] }, { rank := 1, op := "OpName.FW_multiref", ins := [8328], outs := [15043, 15047, 15051], params := [3] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15030, 4955], outs := [8329] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15034, 4957], outs := [8341] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15038, 4959], outs := [8351] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15043, 4955], outs := [8330] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15047, 4957], outs := [8342] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15051, 4959], outs := [8352] }, { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11858, 8361, 8329, 8341], outs := [8363, 8365], params := [16, 4] }, { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11858, 8362, 8330, 8342], outs := [8364, 8366], params := [16, 4] }, { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [8363, 8365, 8351, 4964, 4965], outs := [8367], params := [16, 4, 64, 64, 1, 512] }, { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [8364, 8366, 8352, 4964, 4965], outs := [8368], params := [16, 4, 64, 64, 1, 512] }, { rank := 0, op := "OpName.FW_reshape", ins := [8367], outs := [8369], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [8368], outs := [8370], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8369], outs := [8375], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [8370], outs := [8376], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8375, 4969], outs := [8379] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8376, 4969], outs := [8380] }, { rank := 0, op := "OpName.FW_view", ins := [8379], outs := [8389], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [8380], outs := [8390], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [8389], outs := [8393] }]

theorem pmChunk_11_wf : ∀ n ∈ pmChunk_11, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_11, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_440_wf
  · rw [h1]
    exact pm_node_441_wf
  · rw [h2]
    exact pm_node_442_wf
  · rw [h3]
    exact pm_node_443_wf
  · rw [h4]
    exact pm_node_444_wf
  · rw [h5]
    exact pm_node_445_wf
  · rw [h6]
    exact pm_node_446_wf
  · rw [h7]
    exact pm_node_447_wf
  · rw [h8]
    exact pm_node_448_wf
  · rw [h9]
    exact pm_node_449_wf
  · rw [h10]
    exact pm_node_450_wf
  · rw [h11]
    exact pm_node_451_wf
  · rw [h12]
    exact pm_node_452_wf
  · rw [h13]
    exact pm_node_453_wf
  · rw [h14]
    exact pm_node_454_wf
  · rw [h15]
    exact pm_node_455_wf
  · rw [h16]
    exact pm_node_456_wf
  · rw [h17]
    exact pm_node_457_wf
  · rw [h18]
    exact pm_node_458_wf
  · rw [h19]
    exact pm_node_459_wf
  · rw [h20]
    exact pm_node_460_wf
  · rw [h21]
    exact pm_node_461_wf
  · rw [h22]
    exact pm_node_462_wf
  · rw [h23]
    exact pm_node_463_wf
  · rw [h24]
    exact pm_node_464_wf
  · rw [h25]
    exact pm_node_465_wf
  · rw [h26]
    exact pm_node_466_wf
  · rw [h27]
    exact pm_node_467_wf
  · rw [h28]
    exact pm_node_468_wf
  · rw [h29]
    exact pm_node_469_wf
  · rw [h30]
    exact pm_node_470_wf
  · rw [h31]
    exact pm_node_471_wf
  · rw [h32]
    exact pm_node_472_wf
  · rw [h33]
    exact pm_node_473_wf
  · rw [h34]
    exact pm_node_474_wf
  · rw [h35]
    exact pm_node_475_wf
  · rw [h36]
    exact pm_node_476_wf
  · rw [h37]
    exact pm_node_477_wf
  · rw [h38]
    exact pm_node_478_wf
  · rw [h39]
    exact pm_node_479_wf

def pmChunk_12 : List NodeDecl :=
  [{ rank := 1, op := "OpName.FW_float", ins := [8390], outs := [8394] }, { rank := 0, op := "OpName.FW_add", ins := [15017, 8393], outs := [8397] }, { rank := 1, op := "OpName.FW_add", ins := [15025, 8394], outs := [8398] }, { rank := 0, op := "OpName.FW_multiref", ins := [8397], outs := [15055, 15059], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [8398], outs := [15063, 15067], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [15055, 4974], outs := [8401] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [15063, 4974], outs := [8402] }, { rank := 0, op := "OpName.FW_multiref", ins := [8401], outs := [15074, 15078, 15082, 15086, 15090], params := [5] }, { rank := 1, op := "OpName.FW_multiref", ins := [8402], outs := [15097, 15101, 15105, 15109, 15113], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [15074], outs := [8403] }, { rank := 0, op := "OpName.FW_reshape", ins := [15082], outs := [8423], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [15086], outs := [8437], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [15090], outs := [8455], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_float", ins := [15097], outs := [8404] }, { rank := 1, op := "OpName.FW_reshape", ins := [15105], outs := [8424], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [15109], outs := [8438], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [15113], outs := [8456], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [8403, 4977], outs := [8409] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8423, 4986], outs := [8427] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8437, 4991], outs := [8441] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8455, 4995], outs := [8459] }, { rank := 1, op := "OpName.FW_norm_linear", ins := [8404, 4977], outs := [8410] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8424, 4986], outs := [8428] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8438, 4991], outs := [8442] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8456, 4995], outs := [8460] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [8409], outs := [8411, 8413, 8415], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [8427], outs := [8433], params := [2048, 1] }, { rank := 0, op := "OpName.FW_view", ins := [8441], outs := [8451], params := [2048, 512] }, { rank := 0, op := "OpName.FW_view", ins := [8459], outs := [8469], params := [2048, 512] }, { rank := 1, op := "OpName.FW_topk_routing", ins := [8410], outs := [8412, 8414, 8416], params := [8, 1] }, { rank := 1, op := "OpName.FW_view", ins := [8428], outs := [8434], params := [2048, 1] }, { rank := 1, op := "OpName.FW_view", ins := [8442], outs := [8452], params := [2048, 512] }, { rank := 1, op := "OpName.FW_view", ins := [8460], outs := [8470], params := [2048, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [15078, 8411, 8413, 8417, 8419], outs := [8421], params := [64, 0, 32, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [8433], outs := [8435] }, { rank := 0, op := "OpName.FW_swiglu", ins := [8451, 8469], outs := [8473] }, { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [15101, 8412, 8414, 8418, 8420], outs := [8422], params := [64, 32, 64, 8] }, { rank := 1, op := "OpName.FW_sigmoid", ins := [8434], outs := [8436] }, { rank := 1, op := "OpName.FW_swiglu", ins := [8452, 8470], outs := [8474] }, { rank := 0, op := "OpName.FW_reshape", ins := [8473], outs := [8475], params := [2048, 512] }]

theorem pmChunk_12_wf : ∀ n ∈ pmChunk_12, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_12, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_480_wf
  · rw [h1]
    exact pm_node_481_wf
  · rw [h2]
    exact pm_node_482_wf
  · rw [h3]
    exact pm_node_483_wf
  · rw [h4]
    exact pm_node_484_wf
  · rw [h5]
    exact pm_node_485_wf
  · rw [h6]
    exact pm_node_486_wf
  · rw [h7]
    exact pm_node_487_wf
  · rw [h8]
    exact pm_node_488_wf
  · rw [h9]
    exact pm_node_489_wf
  · rw [h10]
    exact pm_node_490_wf
  · rw [h11]
    exact pm_node_491_wf
  · rw [h12]
    exact pm_node_492_wf
  · rw [h13]
    exact pm_node_493_wf
  · rw [h14]
    exact pm_node_494_wf
  · rw [h15]
    exact pm_node_495_wf
  · rw [h16]
    exact pm_node_496_wf
  · rw [h17]
    exact pm_node_497_wf
  · rw [h18]
    exact pm_node_498_wf
  · rw [h19]
    exact pm_node_499_wf
  · rw [h20]
    exact pm_node_500_wf
  · rw [h21]
    exact pm_node_501_wf
  · rw [h22]
    exact pm_node_502_wf
  · rw [h23]
    exact pm_node_503_wf
  · rw [h24]
    exact pm_node_504_wf
  · rw [h25]
    exact pm_node_505_wf
  · rw [h26]
    exact pm_node_506_wf
  · rw [h27]
    exact pm_node_507_wf
  · rw [h28]
    exact pm_node_508_wf
  · rw [h29]
    exact pm_node_509_wf
  · rw [h30]
    exact pm_node_510_wf
  · rw [h31]
    exact pm_node_511_wf
  · rw [h32]
    exact pm_node_512_wf
  · rw [h33]
    exact pm_node_513_wf
  · rw [h34]
    exact pm_node_514_wf
  · rw [h35]
    exact pm_node_515_wf
  · rw [h36]
    exact pm_node_516_wf
  · rw [h37]
    exact pm_node_517_wf
  · rw [h38]
    exact pm_node_518_wf
  · rw [h39]
    exact pm_node_519_wf

def pmChunk_13 : List NodeDecl :=
  [{ rank := 1, op := "OpName.FW_reshape", ins := [8474], outs := [8476], params := [2048, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8475, 5000], outs := [8481] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8476, 5000], outs := [8482] }, { rank := 0, op := "OpName.FW_view", ins := [8481], outs := [8491], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [8482], outs := [8492], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [8435, 8491], outs := [8495] }, { rank := 1, op := "OpName.FW_mul", ins := [8436, 8492], outs := [8496] }, { rank := 0, op := "OpName.FW_add", ins := [8421, 8495], outs := [8499] }, { rank := 1, op := "OpName.FW_add", ins := [8422, 8496], outs := [8500] }, { rank := 0, op := "OpName.FW_float", ins := [8499], outs := [8505] }, { rank := 1, op := "OpName.FW_float", ins := [8500], outs := [8506] }, { rank := 0, op := "OpName.FW_add", ins := [15059, 8505], outs := [8509] }, { rank := 1, op := "OpName.FW_add", ins := [15067, 8506], outs := [8510] }, { rank := 0, op := "OpName.FW_multiref", ins := [8509], outs := [15117, 15121], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [8510], outs := [15125, 15129], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [15117, 5007], outs := [8513] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [15125, 5007], outs := [8514] }, { rank := 0, op := "OpName.FW_multiref", ins := [8513], outs := [15134, 15138, 15142], params := [3] }, { rank := 1, op := "OpName.FW_multiref", ins := [8514], outs := [15147, 15151, 15155], params := [3] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15134, 5009], outs := [8515] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15138, 5011], outs := [8527] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15142, 5013], outs := [8537] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15147, 5009], outs := [8516] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15151, 5011], outs := [8528] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15155, 5013], outs := [8538] }, { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11859, 8547, 8515, 8527], outs := [8549, 8551], params := [16, 4] }, { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11859, 8548, 8516, 8528], outs := [8550, 8552], params := [16, 4] }, { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [8549, 8551, 8537, 5018, 5019], outs := [8553], params := [16, 4, 64, 64, 1, 512] }, { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [8550, 8552, 8538, 5018, 5019], outs := [8554], params := [16, 4, 64, 64, 1, 512] }, { rank := 0, op := "OpName.FW_reshape", ins := [8553], outs := [8555], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [8554], outs := [8556], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8555], outs := [8561], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [8556], outs := [8562], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8561, 5023], outs := [8565] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8562, 5023], outs := [8566] }, { rank := 0, op := "OpName.FW_view", ins := [8565], outs := [8575], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [8566], outs := [8576], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [8575], outs := [8579] }, { rank := 1, op := "OpName.FW_float", ins := [8576], outs := [8580] }, { rank := 0, op := "OpName.FW_add", ins := [15121, 8579], outs := [8583] }]

theorem pmChunk_13_wf : ∀ n ∈ pmChunk_13, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_13, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_520_wf
  · rw [h1]
    exact pm_node_521_wf
  · rw [h2]
    exact pm_node_522_wf
  · rw [h3]
    exact pm_node_523_wf
  · rw [h4]
    exact pm_node_524_wf
  · rw [h5]
    exact pm_node_525_wf
  · rw [h6]
    exact pm_node_526_wf
  · rw [h7]
    exact pm_node_527_wf
  · rw [h8]
    exact pm_node_528_wf
  · rw [h9]
    exact pm_node_529_wf
  · rw [h10]
    exact pm_node_530_wf
  · rw [h11]
    exact pm_node_531_wf
  · rw [h12]
    exact pm_node_532_wf
  · rw [h13]
    exact pm_node_533_wf
  · rw [h14]
    exact pm_node_534_wf
  · rw [h15]
    exact pm_node_535_wf
  · rw [h16]
    exact pm_node_536_wf
  · rw [h17]
    exact pm_node_537_wf
  · rw [h18]
    exact pm_node_538_wf
  · rw [h19]
    exact pm_node_539_wf
  · rw [h20]
    exact pm_node_540_wf
  · rw [h21]
    exact pm_node_541_wf
  · rw [h22]
    exact pm_node_542_wf
  · rw [h23]
    exact pm_node_543_wf
  · rw [h24]
    exact pm_node_544_wf
  · rw [h25]
    exact pm_node_545_wf
  · rw [h26]
    exact pm_node_546_wf
  · rw [h27]
    exact pm_node_547_wf
  · rw [h28]
    exact pm_node_548_wf
  · rw [h29]
    exact pm_node_549_wf
  · rw [h30]
    exact pm_node_550_wf
  · rw [h31]
    exact pm_node_551_wf
  · rw [h32]
    exact pm_node_552_wf
  · rw [h33]
    exact pm_node_553_wf
  · rw [h34]
    exact pm_node_554_wf
  · rw [h35]
    exact pm_node_555_wf
  · rw [h36]
    exact pm_node_556_wf
  · rw [h37]
    exact pm_node_557_wf
  · rw [h38]
    exact pm_node_558_wf
  · rw [h39]
    exact pm_node_559_wf

def pmChunk_14 : List NodeDecl :=
  [{ rank := 1, op := "OpName.FW_add", ins := [15129, 8580], outs := [8584] }, { rank := 0, op := "OpName.FW_multiref", ins := [8583], outs := [15159, 15163], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [8584], outs := [15167, 15171], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [15159, 5028], outs := [8587] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [15167, 5028], outs := [8588] }, { rank := 0, op := "OpName.FW_multiref", ins := [8587], outs := [15178, 15182, 15186, 15190, 15194], params := [5] }, { rank := 1, op := "OpName.FW_multiref", ins := [8588], outs := [15201, 15205, 15209, 15213, 15217], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [15178], outs := [8589] }, { rank := 0, op := "OpName.FW_reshape", ins := [15186], outs := [8609], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [15190], outs := [8623], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [15194], outs := [8641], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_float", ins := [15201], outs := [8590] }, { rank := 1, op := "OpName.FW_reshape", ins := [15209], outs := [8610], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [15213], outs := [8624], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [15217], outs := [8642], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [8589, 5031], outs := [8595] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8609, 5040], outs := [8613] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8623, 5045], outs := [8627] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8641, 5049], outs := [8645] }, { rank := 1, op := "OpName.FW_norm_linear", ins := [8590, 5031], outs := [8596] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8610, 5040], outs := [8614] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8624, 5045], outs := [8628] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8642, 5049], outs := [8646] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [8595], outs := [8597, 8599, 8601], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [8613], outs := [8619], params := [2048, 1] }, { rank := 0, op := "OpName.FW_view", ins := [8627], outs := [8637], params := [2048, 512] }, { rank := 0, op := "OpName.FW_view", ins := [8645], outs := [8655], params := [2048, 512] }, { rank := 1, op := "OpName.FW_topk_routing", ins := [8596], outs := [8598, 8600, 8602], params := [8, 1] }, { rank := 1, op := "OpName.FW_view", ins := [8614], outs := [8620], params := [2048, 1] }, { rank := 1, op := "OpName.FW_view", ins := [8628], outs := [8638], params := [2048, 512] }, { rank := 1, op := "OpName.FW_view", ins := [8646], outs := [8656], params := [2048, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [15182, 8597, 8599, 8603, 8605], outs := [8607], params := [64, 0, 32, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [8619], outs := [8621] }, { rank := 0, op := "OpName.FW_swiglu", ins := [8637, 8655], outs := [8659] }, { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [15205, 8598, 8600, 8604, 8606], outs := [8608], params := [64, 32, 64, 8] }, { rank := 1, op := "OpName.FW_sigmoid", ins := [8620], outs := [8622] }, { rank := 1, op := "OpName.FW_swiglu", ins := [8638, 8656], outs := [8660] }, { rank := 0, op := "OpName.FW_reshape", ins := [8659], outs := [8661], params := [2048, 512] }, { rank := 1, op := "OpName.FW_reshape", ins := [8660], outs := [8662], params := [2048, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8661, 5054], outs := [8667] }]

theorem pmChunk_14_wf : ∀ n ∈ pmChunk_14, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_14, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_560_wf
  · rw [h1]
    exact pm_node_561_wf
  · rw [h2]
    exact pm_node_562_wf
  · rw [h3]
    exact pm_node_563_wf
  · rw [h4]
    exact pm_node_564_wf
  · rw [h5]
    exact pm_node_565_wf
  · rw [h6]
    exact pm_node_566_wf
  · rw [h7]
    exact pm_node_567_wf
  · rw [h8]
    exact pm_node_568_wf
  · rw [h9]
    exact pm_node_569_wf
  · rw [h10]
    exact pm_node_570_wf
  · rw [h11]
    exact pm_node_571_wf
  · rw [h12]
    exact pm_node_572_wf
  · rw [h13]
    exact pm_node_573_wf
  · rw [h14]
    exact pm_node_574_wf
  · rw [h15]
    exact pm_node_575_wf
  · rw [h16]
    exact pm_node_576_wf
  · rw [h17]
    exact pm_node_577_wf
  · rw [h18]
    exact pm_node_578_wf
  · rw [h19]
    exact pm_node_579_wf
  · rw [h20]
    exact pm_node_580_wf
  · rw [h21]
    exact pm_node_581_wf
  · rw [h22]
    exact pm_node_582_wf
  · rw [h23]
    exact pm_node_583_wf
  · rw [h24]
    exact pm_node_584_wf
  · rw [h25]
    exact pm_node_585_wf
  · rw [h26]
    exact pm_node_586_wf
  · rw [h27]
    exact pm_node_587_wf
  · rw [h28]
    exact pm_node_588_wf
  · rw [h29]
    exact pm_node_589_wf
  · rw [h30]
    exact pm_node_590_wf
  · rw [h31]
    exact pm_node_591_wf
  · rw [h32]
    exact pm_node_592_wf
  · rw [h33]
    exact pm_node_593_wf
  · rw [h34]
    exact pm_node_594_wf
  · rw [h35]
    exact pm_node_595_wf
  · rw [h36]
    exact pm_node_596_wf
  · rw [h37]
    exact pm_node_597_wf
  · rw [h38]
    exact pm_node_598_wf
  · rw [h39]
    exact pm_node_599_wf

def pmChunk_15 : List NodeDecl :=
  [{ rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8662, 5054], outs := [8668] }, { rank := 0, op := "OpName.FW_view", ins := [8667], outs := [8677], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [8668], outs := [8678], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [8621, 8677], outs := [8681] }, { rank := 1, op := "OpName.FW_mul", ins := [8622, 8678], outs := [8682] }, { rank := 0, op := "OpName.FW_add", ins := [8607, 8681], outs := [8685] }, { rank := 1, op := "OpName.FW_add", ins := [8608, 8682], outs := [8686] }, { rank := 0, op := "OpName.FW_float", ins := [8685], outs := [8691] }, { rank := 1, op := "OpName.FW_float", ins := [8686], outs := [8692] }, { rank := 0, op := "OpName.FW_add", ins := [15163, 8691], outs := [8695] }, { rank := 1, op := "OpName.FW_add", ins := [15171, 8692], outs := [8696] }, { rank := 0, op := "OpName.FW_multiref", ins := [8695], outs := [15221, 15225], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [8696], outs := [15229, 15233], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [15221, 5061], outs := [8699] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [15229, 5061], outs := [8700] }, { rank := 0, op := "OpName.FW_multiref", ins := [8699], outs := [15238, 15242, 15246], params := [3] }, { rank := 1, op := "OpName.FW_multiref", ins := [8700], outs := [15251, 15255, 15259], params := [3] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15238, 5063], outs := [8701] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15242, 5065], outs := [8713] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15246, 5067], outs := [8723] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15251, 5063], outs := [8702] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15255, 5065], outs := [8714] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15259, 5067], outs := [8724] }, { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11860, 8733, 8701, 8713], outs := [8735, 8737], params := [16, 4] }, { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11860, 8734, 8702, 8714], outs := [8736, 8738], params := [16, 4] }, { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [8735, 8737, 8723, 5072, 5073], outs := [8739], params := [16, 4, 64, 64, 1, 512] }, { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [8736, 8738, 8724, 5072, 5073], outs := [8740], params := [16, 4, 64, 64, 1, 512] }, { rank := 0, op := "OpName.FW_reshape", ins := [8739], outs := [8741], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [8740], outs := [8742], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8741], outs := [8747], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [8742], outs := [8748], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8747, 5077], outs := [8751] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8748, 5077], outs := [8752] }, { rank := 0, op := "OpName.FW_view", ins := [8751], outs := [8761], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [8752], outs := [8762], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [8761], outs := [8765] }, { rank := 1, op := "OpName.FW_float", ins := [8762], outs := [8766] }, { rank := 0, op := "OpName.FW_add", ins := [15225, 8765], outs := [8769] }, { rank := 1, op := "OpName.FW_add", ins := [15233, 8766], outs := [8770] }, { rank := 0, op := "OpName.FW_multiref", ins := [8769], outs := [15263, 15267], params := [2] }]

theorem pmChunk_15_wf : ∀ n ∈ pmChunk_15, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_15, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_600_wf
  · rw [h1]
    exact pm_node_601_wf
  · rw [h2]
    exact pm_node_602_wf
  · rw [h3]
    exact pm_node_603_wf
  · rw [h4]
    exact pm_node_604_wf
  · rw [h5]
    exact pm_node_605_wf
  · rw [h6]
    exact pm_node_606_wf
  · rw [h7]
    exact pm_node_607_wf
  · rw [h8]
    exact pm_node_608_wf
  · rw [h9]
    exact pm_node_609_wf
  · rw [h10]
    exact pm_node_610_wf
  · rw [h11]
    exact pm_node_611_wf
  · rw [h12]
    exact pm_node_612_wf
  · rw [h13]
    exact pm_node_613_wf
  · rw [h14]
    exact pm_node_614_wf
  · rw [h15]
    exact pm_node_615_wf
  · rw [h16]
    exact pm_node_616_wf
  · rw [h17]
    exact pm_node_617_wf
  · rw [h18]
    exact pm_node_618_wf
  · rw [h19]
    exact pm_node_619_wf
  · rw [h20]
    exact pm_node_620_wf
  · rw [h21]
    exact pm_node_621_wf
  · rw [h22]
    exact pm_node_622_wf
  · rw [h23]
    exact pm_node_623_wf
  · rw [h24]
    exact pm_node_624_wf
  · rw [h25]
    exact pm_node_625_wf
  · rw [h26]
    exact pm_node_626_wf
  · rw [h27]
    exact pm_node_627_wf
  · rw [h28]
    exact pm_node_628_wf
  · rw [h29]
    exact pm_node_629_wf
  · rw [h30]
    exact pm_node_630_wf
  · rw [h31]
    exact pm_node_631_wf
  · rw [h32]
    exact pm_node_632_wf
  · rw [h33]
    exact pm_node_633_wf
  · rw [h34]
    exact pm_node_634_wf
  · rw [h35]
    exact pm_node_635_wf
  · rw [h36]
    exact pm_node_636_wf
  · rw [h37]
    exact pm_node_637_wf
  · rw [h38]
    exact pm_node_638_wf
  · rw [h39]
    exact pm_node_639_wf

def pmChunk_16 : List NodeDecl :=
  [{ rank := 1, op := "OpName.FW_multiref", ins := [8770], outs := [15271, 15275], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [15263, 5082], outs := [8773] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [15271, 5082], outs := [8774] }, { rank := 0, op := "OpName.FW_multiref", ins := [8773], outs := [15282, 15286, 15290, 15294, 15298], params := [5] }, { rank := 1, op := "OpName.FW_multiref", ins := [8774], outs := [15305, 15309, 15313, 15317, 15321], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [15282], outs := [8775] }, { rank := 0, op := "OpName.FW_reshape", ins := [15290], outs := [8795], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [15294], outs := [8809], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [15298], outs := [8827], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_float", ins := [15305], outs := [8776] }, { rank := 1, op := "OpName.FW_reshape", ins := [15313], outs := [8796], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [15317], outs := [8810], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [15321], outs := [8828], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [8775, 5085], outs := [8781] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8795, 5094], outs := [8799] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8809, 5099], outs := [8813] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8827, 5103], outs := [8831] }, { rank := 1, op := "OpName.FW_norm_linear", ins := [8776, 5085], outs := [8782] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8796, 5094], outs := [8800] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8810, 5099], outs := [8814] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8828, 5103], outs := [8832] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [8781], outs := [8783, 8785, 8787], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [8799], outs := [8805], params := [2048, 1] }, { rank := 0, op := "OpName.FW_view", ins := [8813], outs := [8823], params := [2048, 512] }, { rank := 0, op := "OpName.FW_view", ins := [8831], outs := [8841], params := [2048, 512] }, { rank := 1, op := "OpName.FW_topk_routing", ins := [8782], outs := [8784, 8786, 8788], params := [8, 1] }, { rank := 1, op := "OpName.FW_view", ins := [8800], outs := [8806], params := [2048, 1] }, { rank := 1, op := "OpName.FW_view", ins := [8814], outs := [8824], params := [2048, 512] }, { rank := 1, op := "OpName.FW_view", ins := [8832], outs := [8842], params := [2048, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [15286, 8783, 8785, 8789, 8791], outs := [8793], params := [64, 0, 32, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [8805], outs := [8807] }, { rank := 0, op := "OpName.FW_swiglu", ins := [8823, 8841], outs := [8845] }, { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [15309, 8784, 8786, 8790, 8792], outs := [8794], params := [64, 32, 64, 8] }, { rank := 1, op := "OpName.FW_sigmoid", ins := [8806], outs := [8808] }, { rank := 1, op := "OpName.FW_swiglu", ins := [8824, 8842], outs := [8846] }, { rank := 0, op := "OpName.FW_reshape", ins := [8845], outs := [8847], params := [2048, 512] }, { rank := 1, op := "OpName.FW_reshape", ins := [8846], outs := [8848], params := [2048, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8847, 5108], outs := [8853] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8848, 5108], outs := [8854] }, { rank := 0, op := "OpName.FW_view", ins := [8853], outs := [8863], params := [2048, 1024] }]

theorem pmChunk_16_wf : ∀ n ∈ pmChunk_16, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_16, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_640_wf
  · rw [h1]
    exact pm_node_641_wf
  · rw [h2]
    exact pm_node_642_wf
  · rw [h3]
    exact pm_node_643_wf
  · rw [h4]
    exact pm_node_644_wf
  · rw [h5]
    exact pm_node_645_wf
  · rw [h6]
    exact pm_node_646_wf
  · rw [h7]
    exact pm_node_647_wf
  · rw [h8]
    exact pm_node_648_wf
  · rw [h9]
    exact pm_node_649_wf
  · rw [h10]
    exact pm_node_650_wf
  · rw [h11]
    exact pm_node_651_wf
  · rw [h12]
    exact pm_node_652_wf
  · rw [h13]
    exact pm_node_653_wf
  · rw [h14]
    exact pm_node_654_wf
  · rw [h15]
    exact pm_node_655_wf
  · rw [h16]
    exact pm_node_656_wf
  · rw [h17]
    exact pm_node_657_wf
  · rw [h18]
    exact pm_node_658_wf
  · rw [h19]
    exact pm_node_659_wf
  · rw [h20]
    exact pm_node_660_wf
  · rw [h21]
    exact pm_node_661_wf
  · rw [h22]
    exact pm_node_662_wf
  · rw [h23]
    exact pm_node_663_wf
  · rw [h24]
    exact pm_node_664_wf
  · rw [h25]
    exact pm_node_665_wf
  · rw [h26]
    exact pm_node_666_wf
  · rw [h27]
    exact pm_node_667_wf
  · rw [h28]
    exact pm_node_668_wf
  · rw [h29]
    exact pm_node_669_wf
  · rw [h30]
    exact pm_node_670_wf
  · rw [h31]
    exact pm_node_671_wf
  · rw [h32]
    exact pm_node_672_wf
  · rw [h33]
    exact pm_node_673_wf
  · rw [h34]
    exact pm_node_674_wf
  · rw [h35]
    exact pm_node_675_wf
  · rw [h36]
    exact pm_node_676_wf
  · rw [h37]
    exact pm_node_677_wf
  · rw [h38]
    exact pm_node_678_wf
  · rw [h39]
    exact pm_node_679_wf

def pmChunk_17 : List NodeDecl :=
  [{ rank := 1, op := "OpName.FW_view", ins := [8854], outs := [8864], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [8807, 8863], outs := [8867] }, { rank := 1, op := "OpName.FW_mul", ins := [8808, 8864], outs := [8868] }, { rank := 0, op := "OpName.FW_add", ins := [8793, 8867], outs := [8871] }, { rank := 1, op := "OpName.FW_add", ins := [8794, 8868], outs := [8872] }, { rank := 0, op := "OpName.FW_float", ins := [8871], outs := [8877] }, { rank := 1, op := "OpName.FW_float", ins := [8872], outs := [8878] }, { rank := 0, op := "OpName.FW_add", ins := [15267, 8877], outs := [8881] }, { rank := 1, op := "OpName.FW_add", ins := [15275, 8878], outs := [8882] }, { rank := 0, op := "OpName.FW_multiref", ins := [8881], outs := [15325, 15329], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [8882], outs := [15333, 15337], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [15325, 5115], outs := [8885] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [15333, 5115], outs := [8886] }, { rank := 0, op := "OpName.FW_multiref", ins := [8885], outs := [15342, 15346, 15350], params := [3] }, { rank := 1, op := "OpName.FW_multiref", ins := [8886], outs := [15355, 15359, 15363], params := [3] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15342, 5117], outs := [8887] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15346, 5119], outs := [8899] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15350, 5121], outs := [8909] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15355, 5117], outs := [8888] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15359, 5119], outs := [8900] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15363, 5121], outs := [8910] }, { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11861, 8919, 8887, 8899], outs := [8921, 8923], params := [16, 4] }, { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11861, 8920, 8888, 8900], outs := [8922, 8924], params := [16, 4] }, { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [8921, 8923, 8909, 5126, 5127], outs := [8925], params := [16, 4, 64, 64, 1, 512] }, { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [8922, 8924, 8910, 5126, 5127], outs := [8926], params := [16, 4, 64, 64, 1, 512] }, { rank := 0, op := "OpName.FW_reshape", ins := [8925], outs := [8927], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [8926], outs := [8928], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [8927], outs := [8933], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [8928], outs := [8934], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8933, 5131], outs := [8937] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8934, 5131], outs := [8938] }, { rank := 0, op := "OpName.FW_view", ins := [8937], outs := [8947], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [8938], outs := [8948], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [8947], outs := [8951] }, { rank := 1, op := "OpName.FW_float", ins := [8948], outs := [8952] }, { rank := 0, op := "OpName.FW_add", ins := [15329, 8951], outs := [8955] }, { rank := 1, op := "OpName.FW_add", ins := [15337, 8952], outs := [8956] }, { rank := 0, op := "OpName.FW_multiref", ins := [8955], outs := [15367, 15371], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [8956], outs := [15375, 15379], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [15367, 5136], outs := [8959] }]

theorem pmChunk_17_wf : ∀ n ∈ pmChunk_17, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_17, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_680_wf
  · rw [h1]
    exact pm_node_681_wf
  · rw [h2]
    exact pm_node_682_wf
  · rw [h3]
    exact pm_node_683_wf
  · rw [h4]
    exact pm_node_684_wf
  · rw [h5]
    exact pm_node_685_wf
  · rw [h6]
    exact pm_node_686_wf
  · rw [h7]
    exact pm_node_687_wf
  · rw [h8]
    exact pm_node_688_wf
  · rw [h9]
    exact pm_node_689_wf
  · rw [h10]
    exact pm_node_690_wf
  · rw [h11]
    exact pm_node_691_wf
  · rw [h12]
    exact pm_node_692_wf
  · rw [h13]
    exact pm_node_693_wf
  · rw [h14]
    exact pm_node_694_wf
  · rw [h15]
    exact pm_node_695_wf
  · rw [h16]
    exact pm_node_696_wf
  · rw [h17]
    exact pm_node_697_wf
  · rw [h18]
    exact pm_node_698_wf
  · rw [h19]
    exact pm_node_699_wf
  · rw [h20]
    exact pm_node_700_wf
  · rw [h21]
    exact pm_node_701_wf
  · rw [h22]
    exact pm_node_702_wf
  · rw [h23]
    exact pm_node_703_wf
  · rw [h24]
    exact pm_node_704_wf
  · rw [h25]
    exact pm_node_705_wf
  · rw [h26]
    exact pm_node_706_wf
  · rw [h27]
    exact pm_node_707_wf
  · rw [h28]
    exact pm_node_708_wf
  · rw [h29]
    exact pm_node_709_wf
  · rw [h30]
    exact pm_node_710_wf
  · rw [h31]
    exact pm_node_711_wf
  · rw [h32]
    exact pm_node_712_wf
  · rw [h33]
    exact pm_node_713_wf
  · rw [h34]
    exact pm_node_714_wf
  · rw [h35]
    exact pm_node_715_wf
  · rw [h36]
    exact pm_node_716_wf
  · rw [h37]
    exact pm_node_717_wf
  · rw [h38]
    exact pm_node_718_wf
  · rw [h39]
    exact pm_node_719_wf

def pmChunk_18 : List NodeDecl :=
  [{ rank := 1, op := "OpName.FW_rms_norm", ins := [15375, 5136], outs := [8960] }, { rank := 0, op := "OpName.FW_multiref", ins := [8959], outs := [15386, 15390, 15394, 15398, 15402], params := [5] }, { rank := 1, op := "OpName.FW_multiref", ins := [8960], outs := [15409, 15413, 15417, 15421, 15425], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [15386], outs := [8961] }, { rank := 0, op := "OpName.FW_reshape", ins := [15394], outs := [8981], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [15398], outs := [8995], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [15402], outs := [9013], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_float", ins := [15409], outs := [8962] }, { rank := 1, op := "OpName.FW_reshape", ins := [15417], outs := [8982], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [15421], outs := [8996], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [15425], outs := [9014], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [8961, 5139], outs := [8967] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8981, 5148], outs := [8985] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8995, 5153], outs := [8999] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9013, 5157], outs := [9017] }, { rank := 1, op := "OpName.FW_norm_linear", ins := [8962, 5139], outs := [8968] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8982, 5148], outs := [8986] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8996, 5153], outs := [9000] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9014, 5157], outs := [9018] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [8967], outs := [8969, 8971, 8973], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [8985], outs := [8991], params := [2048, 1] }, { rank := 0, op := "OpName.FW_view", ins := [8999], outs := [9009], params := [2048, 512] }, { rank := 0, op := "OpName.FW_view", ins := [9017], outs := [9027], params := [2048, 512] }, { rank := 1, op := "OpName.FW_topk_routing", ins := [8968], outs := [8970, 8972, 8974], params := [8, 1] }, { rank := 1, op := "OpName.FW_view", ins := [8986], outs := [8992], params := [2048, 1] }, { rank := 1, op := "OpName.FW_view", ins := [9000], outs := [9010], params := [2048, 512] }, { rank := 1, op := "OpName.FW_view", ins := [9018], outs := [9028], params := [2048, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [15390, 8969, 8971, 8975, 8977], outs := [8979], params := [64, 0, 32, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [8991], outs := [8993] }, { rank := 0, op := "OpName.FW_swiglu", ins := [9009, 9027], outs := [9031] }, { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [15413, 8970, 8972, 8976, 8978], outs := [8980], params := [64, 32, 64, 8] }, { rank := 1, op := "OpName.FW_sigmoid", ins := [8992], outs := [8994] }, { rank := 1, op := "OpName.FW_swiglu", ins := [9010, 9028], outs := [9032] }, { rank := 0, op := "OpName.FW_reshape", ins := [9031], outs := [9033], params := [2048, 512] }, { rank := 1, op := "OpName.FW_reshape", ins := [9032], outs := [9034], params := [2048, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9033, 5162], outs := [9039] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9034, 5162], outs := [9040] }, { rank := 0, op := "OpName.FW_view", ins := [9039], outs := [9049], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [9040], outs := [9050], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [8993, 9049], outs := [9053] }]

theorem pmChunk_18_wf : ∀ n ∈ pmChunk_18, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_18, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_720_wf
  · rw [h1]
    exact pm_node_721_wf
  · rw [h2]
    exact pm_node_722_wf
  · rw [h3]
    exact pm_node_723_wf
  · rw [h4]
    exact pm_node_724_wf
  · rw [h5]
    exact pm_node_725_wf
  · rw [h6]
    exact pm_node_726_wf
  · rw [h7]
    exact pm_node_727_wf
  · rw [h8]
    exact pm_node_728_wf
  · rw [h9]
    exact pm_node_729_wf
  · rw [h10]
    exact pm_node_730_wf
  · rw [h11]
    exact pm_node_731_wf
  · rw [h12]
    exact pm_node_732_wf
  · rw [h13]
    exact pm_node_733_wf
  · rw [h14]
    exact pm_node_734_wf
  · rw [h15]
    exact pm_node_735_wf
  · rw [h16]
    exact pm_node_736_wf
  · rw [h17]
    exact pm_node_737_wf
  · rw [h18]
    exact pm_node_738_wf
  · rw [h19]
    exact pm_node_739_wf
  · rw [h20]
    exact pm_node_740_wf
  · rw [h21]
    exact pm_node_741_wf
  · rw [h22]
    exact pm_node_742_wf
  · rw [h23]
    exact pm_node_743_wf
  · rw [h24]
    exact pm_node_744_wf
  · rw [h25]
    exact pm_node_745_wf
  · rw [h26]
    exact pm_node_746_wf
  · rw [h27]
    exact pm_node_747_wf
  · rw [h28]
    exact pm_node_748_wf
  · rw [h29]
    exact pm_node_749_wf
  · rw [h30]
    exact pm_node_750_wf
  · rw [h31]
    exact pm_node_751_wf
  · rw [h32]
    exact pm_node_752_wf
  · rw [h33]
    exact pm_node_753_wf
  · rw [h34]
    exact pm_node_754_wf
  · rw [h35]
    exact pm_node_755_wf
  · rw [h36]
    exact pm_node_756_wf
  · rw [h37]
    exact pm_node_757_wf
  · rw [h38]
    exact pm_node_758_wf
  · rw [h39]
    exact pm_node_759_wf

def pmChunk_19 : List NodeDecl :=
  [{ rank := 1, op := "OpName.FW_mul", ins := [8994, 9050], outs := [9054] }, { rank := 0, op := "OpName.FW_add", ins := [8979, 9053], outs := [9057] }, { rank := 1, op := "OpName.FW_add", ins := [8980, 9054], outs := [9058] }, { rank := 0, op := "OpName.FW_float", ins := [9057], outs := [9063] }, { rank := 1, op := "OpName.FW_float", ins := [9058], outs := [9064] }, { rank := 0, op := "OpName.FW_add", ins := [15371, 9063], outs := [9067] }, { rank := 1, op := "OpName.FW_add", ins := [15379, 9064], outs := [9068] }, { rank := 0, op := "OpName.FW_multiref", ins := [9067], outs := [15429, 15433], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [9068], outs := [15437, 15441], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [15429, 5169], outs := [9071] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [15437, 5169], outs := [9072] }, { rank := 0, op := "OpName.FW_multiref", ins := [9071], outs := [15446, 15450, 15454], params := [3] }, { rank := 1, op := "OpName.FW_multiref", ins := [9072], outs := [15459, 15463, 15467], params := [3] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15446, 5171], outs := [9073] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15450, 5173], outs := [9085] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15454, 5175], outs := [9095] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15459, 5171], outs := [9074] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15463, 5173], outs := [9086] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15467, 5175], outs := [9096] }, { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11862, 9105, 9073, 9085], outs := [9107, 9109], params := [16, 4] }, { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11862, 9106, 9074, 9086], outs := [9108, 9110], params := [16, 4] }, { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [9107, 9109, 9095, 5180, 5181], outs := [9111], params := [16, 4, 64, 64, 1, 512] }, { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [9108, 9110, 9096, 5180, 5181], outs := [9112], params := [16, 4, 64, 64, 1, 512] }, { rank := 0, op := "OpName.FW_reshape", ins := [9111], outs := [9113], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [9112], outs := [9114], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [9113], outs := [9119], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [9114], outs := [9120], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9119, 5185], outs := [9123] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9120, 5185], outs := [9124] }, { rank := 0, op := "OpName.FW_view", ins := [9123], outs := [9133], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [9124], outs := [9134], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [9133], outs := [9137] }, { rank := 1, op := "OpName.FW_float", ins := [9134], outs := [9138] }, { rank := 0, op := "OpName.FW_add", ins := [15433, 9137], outs := [9141] }, { rank := 1, op := "OpName.FW_add", ins := [15441, 9138], outs := [9142] }, { rank := 0, op := "OpName.FW_multiref", ins := [9141], outs := [15471, 15475], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [9142], outs := [15479, 15483], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [15471, 5190], outs := [9145] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [15479, 5190], outs := [9146] }, { rank := 0, op := "OpName.FW_multiref", ins := [9145], outs := [15490, 15494, 15498, 15502, 15506], params := [5] }]

theorem pmChunk_19_wf : ∀ n ∈ pmChunk_19, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_19, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_760_wf
  · rw [h1]
    exact pm_node_761_wf
  · rw [h2]
    exact pm_node_762_wf
  · rw [h3]
    exact pm_node_763_wf
  · rw [h4]
    exact pm_node_764_wf
  · rw [h5]
    exact pm_node_765_wf
  · rw [h6]
    exact pm_node_766_wf
  · rw [h7]
    exact pm_node_767_wf
  · rw [h8]
    exact pm_node_768_wf
  · rw [h9]
    exact pm_node_769_wf
  · rw [h10]
    exact pm_node_770_wf
  · rw [h11]
    exact pm_node_771_wf
  · rw [h12]
    exact pm_node_772_wf
  · rw [h13]
    exact pm_node_773_wf
  · rw [h14]
    exact pm_node_774_wf
  · rw [h15]
    exact pm_node_775_wf
  · rw [h16]
    exact pm_node_776_wf
  · rw [h17]
    exact pm_node_777_wf
  · rw [h18]
    exact pm_node_778_wf
  · rw [h19]
    exact pm_node_779_wf
  · rw [h20]
    exact pm_node_780_wf
  · rw [h21]
    exact pm_node_781_wf
  · rw [h22]
    exact pm_node_782_wf
  · rw [h23]
    exact pm_node_783_wf
  · rw [h24]
    exact pm_node_784_wf
  · rw [h25]
    exact pm_node_785_wf
  · rw [h26]
    exact pm_node_786_wf
  · rw [h27]
    exact pm_node_787_wf
  · rw [h28]
    exact pm_node_788_wf
  · rw [h29]
    exact pm_node_789_wf
  · rw [h30]
    exact pm_node_790_wf
  · rw [h31]
    exact pm_node_791_wf
  · rw [h32]
    exact pm_node_792_wf
  · rw [h33]
    exact pm_node_793_wf
  · rw [h34]
    exact pm_node_794_wf
  · rw [h35]
    exact pm_node_795_wf
  · rw [h36]
    exact pm_node_796_wf
  · rw [h37]
    exact pm_node_797_wf
  · rw [h38]
    exact pm_node_798_wf
  · rw [h39]
    exact pm_node_799_wf

def pmChunk_20 : List NodeDecl :=
  [{ rank := 1, op := "OpName.FW_multiref", ins := [9146], outs := [15513, 15517, 15521, 15525, 15529], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [15490], outs := [9147] }, { rank := 0, op := "OpName.FW_reshape", ins := [15498], outs := [9167], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [15502], outs := [9181], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [15506], outs := [9199], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_float", ins := [15513], outs := [9148] }, { rank := 1, op := "OpName.FW_reshape", ins := [15521], outs := [9168], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [15525], outs := [9182], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [15529], outs := [9200], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [9147, 5193], outs := [9153] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9167, 5202], outs := [9171] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9181, 5207], outs := [9185] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9199, 5211], outs := [9203] }, { rank := 1, op := "OpName.FW_norm_linear", ins := [9148, 5193], outs := [9154] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9168, 5202], outs := [9172] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9182, 5207], outs := [9186] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9200, 5211], outs := [9204] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [9153], outs := [9155, 9157, 9159], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [9171], outs := [9177], params := [2048, 1] }, { rank := 0, op := "OpName.FW_view", ins := [9185], outs := [9195], params := [2048, 512] }, { rank := 0, op := "OpName.FW_view", ins := [9203], outs := [9213], params := [2048, 512] }, { rank := 1, op := "OpName.FW_topk_routing", ins := [9154], outs := [9156, 9158, 9160], params := [8, 1] }, { rank := 1, op := "OpName.FW_view", ins := [9172], outs := [9178], params := [2048, 1] }, { rank := 1, op := "OpName.FW_view", ins := [9186], outs := [9196], params := [2048, 512] }, { rank := 1, op := "OpName.FW_view", ins := [9204], outs := [9214], params := [2048, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [15494, 9155, 9157, 9161, 9163], outs := [9165], params := [64, 0, 32, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [9177], outs := [9179] }, { rank := 0, op := "OpName.FW_swiglu", ins := [9195, 9213], outs := [9217] }, { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [15517, 9156, 9158, 9162, 9164], outs := [9166], params := [64, 32, 64, 8] }, { rank := 1, op := "OpName.FW_sigmoid", ins := [9178], outs := [9180] }, { rank := 1, op := "OpName.FW_swiglu", ins := [9196, 9214], outs := [9218] }, { rank := 0, op := "OpName.FW_reshape", ins := [9217], outs := [9219], params := [2048, 512] }, { rank := 1, op := "OpName.FW_reshape", ins := [9218], outs := [9220], params := [2048, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9219, 5216], outs := [9225] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9220, 5216], outs := [9226] }, { rank := 0, op := "OpName.FW_view", ins := [9225], outs := [9235], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [9226], outs := [9236], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [9179, 9235], outs := [9239] }, { rank := 1, op := "OpName.FW_mul", ins := [9180, 9236], outs := [9240] }, { rank := 0, op := "OpName.FW_add", ins := [9165, 9239], outs := [9243] }]

theorem pmChunk_20_wf : ∀ n ∈ pmChunk_20, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_20, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_800_wf
  · rw [h1]
    exact pm_node_801_wf
  · rw [h2]
    exact pm_node_802_wf
  · rw [h3]
    exact pm_node_803_wf
  · rw [h4]
    exact pm_node_804_wf
  · rw [h5]
    exact pm_node_805_wf
  · rw [h6]
    exact pm_node_806_wf
  · rw [h7]
    exact pm_node_807_wf
  · rw [h8]
    exact pm_node_808_wf
  · rw [h9]
    exact pm_node_809_wf
  · rw [h10]
    exact pm_node_810_wf
  · rw [h11]
    exact pm_node_811_wf
  · rw [h12]
    exact pm_node_812_wf
  · rw [h13]
    exact pm_node_813_wf
  · rw [h14]
    exact pm_node_814_wf
  · rw [h15]
    exact pm_node_815_wf
  · rw [h16]
    exact pm_node_816_wf
  · rw [h17]
    exact pm_node_817_wf
  · rw [h18]
    exact pm_node_818_wf
  · rw [h19]
    exact pm_node_819_wf
  · rw [h20]
    exact pm_node_820_wf
  · rw [h21]
    exact pm_node_821_wf
  · rw [h22]
    exact pm_node_822_wf
  · rw [h23]
    exact pm_node_823_wf
  · rw [h24]
    exact pm_node_824_wf
  · rw [h25]
    exact pm_node_825_wf
  · rw [h26]
    exact pm_node_826_wf
  · rw [h27]
    exact pm_node_827_wf
  · rw [h28]
    exact pm_node_828_wf
  · rw [h29]
    exact pm_node_829_wf
  · rw [h30]
    exact pm_node_830_wf
  · rw [h31]
    exact pm_node_831_wf
  · rw [h32]
    exact pm_node_832_wf
  · rw [h33]
    exact pm_node_833_wf
  · rw [h34]
    exact pm_node_834_wf
  · rw [h35]
    exact pm_node_835_wf
  · rw [h36]
    exact pm_node_836_wf
  · rw [h37]
    exact pm_node_837_wf
  · rw [h38]
    exact pm_node_838_wf
  · rw [h39]
    exact pm_node_839_wf

def pmChunk_21 : List NodeDecl :=
  [{ rank := 1, op := "OpName.FW_add", ins := [9166, 9240], outs := [9244] }, { rank := 0, op := "OpName.FW_float", ins := [9243], outs := [9249] }, { rank := 1, op := "OpName.FW_float", ins := [9244], outs := [9250] }, { rank := 0, op := "OpName.FW_add", ins := [15475, 9249], outs := [9253] }, { rank := 1, op := "OpName.FW_add", ins := [15483, 9250], outs := [9254] }, { rank := 0, op := "OpName.FW_multiref", ins := [9253], outs := [15533, 15537], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [9254], outs := [15541, 15545], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [15533, 5223], outs := [9257] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [15541, 5223], outs := [9258] }, { rank := 0, op := "OpName.FW_multiref", ins := [9257], outs := [15550, 15554, 15558], params := [3] }, { rank := 1, op := "OpName.FW_multiref", ins := [9258], outs := [15563, 15567, 15571], params := [3] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15550, 5225], outs := [9259] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15554, 5227], outs := [9271] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15558, 5229], outs := [9281] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15563, 5225], outs := [9260] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15567, 5227], outs := [9272] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15571, 5229], outs := [9282] }, { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11863, 9291, 9259, 9271], outs := [9293, 9295], params := [16, 4] }, { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11863, 9292, 9260, 9272], outs := [9294, 9296], params := [16, 4] }, { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [9293, 9295, 9281, 5234, 5235], outs := [9297], params := [16, 4, 64, 64, 1, 512] }, { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [9294, 9296, 9282, 5234, 5235], outs := [9298], params := [16, 4, 64, 64, 1, 512] }, { rank := 0, op := "OpName.FW_reshape", ins := [9297], outs := [9299], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [9298], outs := [9300], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [9299], outs := [9305], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [9300], outs := [9306], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9305, 5239], outs := [9309] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9306, 5239], outs := [9310] }, { rank := 0, op := "OpName.FW_view", ins := [9309], outs := [9319], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [9310], outs := [9320], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [9319], outs := [9323] }, { rank := 1, op := "OpName.FW_float", ins := [9320], outs := [9324] }, { rank := 0, op := "OpName.FW_add", ins := [15537, 9323], outs := [9327] }, { rank := 1, op := "OpName.FW_add", ins := [15545, 9324], outs := [9328] }, { rank := 0, op := "OpName.FW_multiref", ins := [9327], outs := [15575, 15579], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [9328], outs := [15583, 15587], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [15575, 5244], outs := [9331] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [15583, 5244], outs := [9332] }, { rank := 0, op := "OpName.FW_multiref", ins := [9331], outs := [15594, 15598, 15602, 15606, 15610], params := [5] }, { rank := 1, op := "OpName.FW_multiref", ins := [9332], outs := [15617, 15621, 15625, 15629, 15633], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [15594], outs := [9333] }]

theorem pmChunk_21_wf : ∀ n ∈ pmChunk_21, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_21, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_840_wf
  · rw [h1]
    exact pm_node_841_wf
  · rw [h2]
    exact pm_node_842_wf
  · rw [h3]
    exact pm_node_843_wf
  · rw [h4]
    exact pm_node_844_wf
  · rw [h5]
    exact pm_node_845_wf
  · rw [h6]
    exact pm_node_846_wf
  · rw [h7]
    exact pm_node_847_wf
  · rw [h8]
    exact pm_node_848_wf
  · rw [h9]
    exact pm_node_849_wf
  · rw [h10]
    exact pm_node_850_wf
  · rw [h11]
    exact pm_node_851_wf
  · rw [h12]
    exact pm_node_852_wf
  · rw [h13]
    exact pm_node_853_wf
  · rw [h14]
    exact pm_node_854_wf
  · rw [h15]
    exact pm_node_855_wf
  · rw [h16]
    exact pm_node_856_wf
  · rw [h17]
    exact pm_node_857_wf
  · rw [h18]
    exact pm_node_858_wf
  · rw [h19]
    exact pm_node_859_wf
  · rw [h20]
    exact pm_node_860_wf
  · rw [h21]
    exact pm_node_861_wf
  · rw [h22]
    exact pm_node_862_wf
  · rw [h23]
    exact pm_node_863_wf
  · rw [h24]
    exact pm_node_864_wf
  · rw [h25]
    exact pm_node_865_wf
  · rw [h26]
    exact pm_node_866_wf
  · rw [h27]
    exact pm_node_867_wf
  · rw [h28]
    exact pm_node_868_wf
  · rw [h29]
    exact pm_node_869_wf
  · rw [h30]
    exact pm_node_870_wf
  · rw [h31]
    exact pm_node_871_wf
  · rw [h32]
    exact pm_node_872_wf
  · rw [h33]
    exact pm_node_873_wf
  · rw [h34]
    exact pm_node_874_wf
  · rw [h35]
    exact pm_node_875_wf
  · rw [h36]
    exact pm_node_876_wf
  · rw [h37]
    exact pm_node_877_wf
  · rw [h38]
    exact pm_node_878_wf
  · rw [h39]
    exact pm_node_879_wf

def pmChunk_22 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_reshape", ins := [15602], outs := [9353], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [15606], outs := [9367], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [15610], outs := [9385], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_float", ins := [15617], outs := [9334] }, { rank := 1, op := "OpName.FW_reshape", ins := [15625], outs := [9354], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [15629], outs := [9368], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [15633], outs := [9386], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [9333, 5247], outs := [9339] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9353, 5256], outs := [9357] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9367, 5261], outs := [9371] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9385, 5265], outs := [9389] }, { rank := 1, op := "OpName.FW_norm_linear", ins := [9334, 5247], outs := [9340] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9354, 5256], outs := [9358] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9368, 5261], outs := [9372] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9386, 5265], outs := [9390] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [9339], outs := [9341, 9343, 9345], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [9357], outs := [9363], params := [2048, 1] }, { rank := 0, op := "OpName.FW_view", ins := [9371], outs := [9381], params := [2048, 512] }, { rank := 0, op := "OpName.FW_view", ins := [9389], outs := [9399], params := [2048, 512] }, { rank := 1, op := "OpName.FW_topk_routing", ins := [9340], outs := [9342, 9344, 9346], params := [8, 1] }, { rank := 1, op := "OpName.FW_view", ins := [9358], outs := [9364], params := [2048, 1] }, { rank := 1, op := "OpName.FW_view", ins := [9372], outs := [9382], params := [2048, 512] }, { rank := 1, op := "OpName.FW_view", ins := [9390], outs := [9400], params := [2048, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [15598, 9341, 9343, 9347, 9349], outs := [9351], params := [64, 0, 32, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [9363], outs := [9365] }, { rank := 0, op := "OpName.FW_swiglu", ins := [9381, 9399], outs := [9403] }, { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [15621, 9342, 9344, 9348, 9350], outs := [9352], params := [64, 32, 64, 8] }, { rank := 1, op := "OpName.FW_sigmoid", ins := [9364], outs := [9366] }, { rank := 1, op := "OpName.FW_swiglu", ins := [9382, 9400], outs := [9404] }, { rank := 0, op := "OpName.FW_reshape", ins := [9403], outs := [9405], params := [2048, 512] }, { rank := 1, op := "OpName.FW_reshape", ins := [9404], outs := [9406], params := [2048, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9405, 5270], outs := [9411] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9406, 5270], outs := [9412] }, { rank := 0, op := "OpName.FW_view", ins := [9411], outs := [9421], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [9412], outs := [9422], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [9365, 9421], outs := [9425] }, { rank := 1, op := "OpName.FW_mul", ins := [9366, 9422], outs := [9426] }, { rank := 0, op := "OpName.FW_add", ins := [9351, 9425], outs := [9429] }, { rank := 1, op := "OpName.FW_add", ins := [9352, 9426], outs := [9430] }, { rank := 0, op := "OpName.FW_float", ins := [9429], outs := [9435] }]

theorem pmChunk_22_wf : ∀ n ∈ pmChunk_22, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_22, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_880_wf
  · rw [h1]
    exact pm_node_881_wf
  · rw [h2]
    exact pm_node_882_wf
  · rw [h3]
    exact pm_node_883_wf
  · rw [h4]
    exact pm_node_884_wf
  · rw [h5]
    exact pm_node_885_wf
  · rw [h6]
    exact pm_node_886_wf
  · rw [h7]
    exact pm_node_887_wf
  · rw [h8]
    exact pm_node_888_wf
  · rw [h9]
    exact pm_node_889_wf
  · rw [h10]
    exact pm_node_890_wf
  · rw [h11]
    exact pm_node_891_wf
  · rw [h12]
    exact pm_node_892_wf
  · rw [h13]
    exact pm_node_893_wf
  · rw [h14]
    exact pm_node_894_wf
  · rw [h15]
    exact pm_node_895_wf
  · rw [h16]
    exact pm_node_896_wf
  · rw [h17]
    exact pm_node_897_wf
  · rw [h18]
    exact pm_node_898_wf
  · rw [h19]
    exact pm_node_899_wf
  · rw [h20]
    exact pm_node_900_wf
  · rw [h21]
    exact pm_node_901_wf
  · rw [h22]
    exact pm_node_902_wf
  · rw [h23]
    exact pm_node_903_wf
  · rw [h24]
    exact pm_node_904_wf
  · rw [h25]
    exact pm_node_905_wf
  · rw [h26]
    exact pm_node_906_wf
  · rw [h27]
    exact pm_node_907_wf
  · rw [h28]
    exact pm_node_908_wf
  · rw [h29]
    exact pm_node_909_wf
  · rw [h30]
    exact pm_node_910_wf
  · rw [h31]
    exact pm_node_911_wf
  · rw [h32]
    exact pm_node_912_wf
  · rw [h33]
    exact pm_node_913_wf
  · rw [h34]
    exact pm_node_914_wf
  · rw [h35]
    exact pm_node_915_wf
  · rw [h36]
    exact pm_node_916_wf
  · rw [h37]
    exact pm_node_917_wf
  · rw [h38]
    exact pm_node_918_wf
  · rw [h39]
    exact pm_node_919_wf

def pmChunk_23 : List NodeDecl :=
  [{ rank := 1, op := "OpName.FW_float", ins := [9430], outs := [9436] }, { rank := 0, op := "OpName.FW_add", ins := [15579, 9435], outs := [9439] }, { rank := 1, op := "OpName.FW_add", ins := [15587, 9436], outs := [9440] }, { rank := 0, op := "OpName.FW_multiref", ins := [9439], outs := [15637, 15641], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [9440], outs := [15645, 15649], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [15637, 5277], outs := [9443] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [15645, 5277], outs := [9444] }, { rank := 0, op := "OpName.FW_multiref", ins := [9443], outs := [15654, 15658, 15662], params := [3] }, { rank := 1, op := "OpName.FW_multiref", ins := [9444], outs := [15667, 15671, 15675], params := [3] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15654, 5279], outs := [9445] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15658, 5281], outs := [9457] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15662, 5283], outs := [9467] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15667, 5279], outs := [9446] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15671, 5281], outs := [9458] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15675, 5283], outs := [9468] }, { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11864, 9477, 9445, 9457], outs := [9479, 9481], params := [16, 4] }, { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11864, 9478, 9446, 9458], outs := [9480, 9482], params := [16, 4] }, { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [9479, 9481, 9467, 5288, 5289], outs := [9483], params := [16, 4, 64, 64, 1, 512] }, { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [9480, 9482, 9468, 5288, 5289], outs := [9484], params := [16, 4, 64, 64, 1, 512] }, { rank := 0, op := "OpName.FW_reshape", ins := [9483], outs := [9485], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [9484], outs := [9486], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [9485], outs := [9491], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [9486], outs := [9492], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9491, 5293], outs := [9495] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9492, 5293], outs := [9496] }, { rank := 0, op := "OpName.FW_view", ins := [9495], outs := [9505], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [9496], outs := [9506], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [9505], outs := [9509] }, { rank := 1, op := "OpName.FW_float", ins := [9506], outs := [9510] }, { rank := 0, op := "OpName.FW_add", ins := [15641, 9509], outs := [9513] }, { rank := 1, op := "OpName.FW_add", ins := [15649, 9510], outs := [9514] }, { rank := 0, op := "OpName.FW_multiref", ins := [9513], outs := [15679, 15683], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [9514], outs := [15687, 15691], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [15679, 5298], outs := [9517] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [15687, 5298], outs := [9518] }, { rank := 0, op := "OpName.FW_multiref", ins := [9517], outs := [15698, 15702, 15706, 15710, 15714], params := [5] }, { rank := 1, op := "OpName.FW_multiref", ins := [9518], outs := [15721, 15725, 15729, 15733, 15737], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [15698], outs := [9519] }, { rank := 0, op := "OpName.FW_reshape", ins := [15706], outs := [9539], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [15710], outs := [9553], params := [2048, 1024] }]

theorem pmChunk_23_wf : ∀ n ∈ pmChunk_23, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_23, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_920_wf
  · rw [h1]
    exact pm_node_921_wf
  · rw [h2]
    exact pm_node_922_wf
  · rw [h3]
    exact pm_node_923_wf
  · rw [h4]
    exact pm_node_924_wf
  · rw [h5]
    exact pm_node_925_wf
  · rw [h6]
    exact pm_node_926_wf
  · rw [h7]
    exact pm_node_927_wf
  · rw [h8]
    exact pm_node_928_wf
  · rw [h9]
    exact pm_node_929_wf
  · rw [h10]
    exact pm_node_930_wf
  · rw [h11]
    exact pm_node_931_wf
  · rw [h12]
    exact pm_node_932_wf
  · rw [h13]
    exact pm_node_933_wf
  · rw [h14]
    exact pm_node_934_wf
  · rw [h15]
    exact pm_node_935_wf
  · rw [h16]
    exact pm_node_936_wf
  · rw [h17]
    exact pm_node_937_wf
  · rw [h18]
    exact pm_node_938_wf
  · rw [h19]
    exact pm_node_939_wf
  · rw [h20]
    exact pm_node_940_wf
  · rw [h21]
    exact pm_node_941_wf
  · rw [h22]
    exact pm_node_942_wf
  · rw [h23]
    exact pm_node_943_wf
  · rw [h24]
    exact pm_node_944_wf
  · rw [h25]
    exact pm_node_945_wf
  · rw [h26]
    exact pm_node_946_wf
  · rw [h27]
    exact pm_node_947_wf
  · rw [h28]
    exact pm_node_948_wf
  · rw [h29]
    exact pm_node_949_wf
  · rw [h30]
    exact pm_node_950_wf
  · rw [h31]
    exact pm_node_951_wf
  · rw [h32]
    exact pm_node_952_wf
  · rw [h33]
    exact pm_node_953_wf
  · rw [h34]
    exact pm_node_954_wf
  · rw [h35]
    exact pm_node_955_wf
  · rw [h36]
    exact pm_node_956_wf
  · rw [h37]
    exact pm_node_957_wf
  · rw [h38]
    exact pm_node_958_wf
  · rw [h39]
    exact pm_node_959_wf

def pmChunk_24 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_reshape", ins := [15714], outs := [9571], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_float", ins := [15721], outs := [9520] }, { rank := 1, op := "OpName.FW_reshape", ins := [15729], outs := [9540], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [15733], outs := [9554], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [15737], outs := [9572], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [9519, 5301], outs := [9525] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9539, 5310], outs := [9543] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9553, 5315], outs := [9557] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9571, 5319], outs := [9575] }, { rank := 1, op := "OpName.FW_norm_linear", ins := [9520, 5301], outs := [9526] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9540, 5310], outs := [9544] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9554, 5315], outs := [9558] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9572, 5319], outs := [9576] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [9525], outs := [9527, 9529, 9531], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [9543], outs := [9549], params := [2048, 1] }, { rank := 0, op := "OpName.FW_view", ins := [9557], outs := [9567], params := [2048, 512] }, { rank := 0, op := "OpName.FW_view", ins := [9575], outs := [9585], params := [2048, 512] }, { rank := 1, op := "OpName.FW_topk_routing", ins := [9526], outs := [9528, 9530, 9532], params := [8, 1] }, { rank := 1, op := "OpName.FW_view", ins := [9544], outs := [9550], params := [2048, 1] }, { rank := 1, op := "OpName.FW_view", ins := [9558], outs := [9568], params := [2048, 512] }, { rank := 1, op := "OpName.FW_view", ins := [9576], outs := [9586], params := [2048, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [15702, 9527, 9529, 9533, 9535], outs := [9537], params := [64, 0, 32, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [9549], outs := [9551] }, { rank := 0, op := "OpName.FW_swiglu", ins := [9567, 9585], outs := [9589] }, { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [15725, 9528, 9530, 9534, 9536], outs := [9538], params := [64, 32, 64, 8] }, { rank := 1, op := "OpName.FW_sigmoid", ins := [9550], outs := [9552] }, { rank := 1, op := "OpName.FW_swiglu", ins := [9568, 9586], outs := [9590] }, { rank := 0, op := "OpName.FW_reshape", ins := [9589], outs := [9591], params := [2048, 512] }, { rank := 1, op := "OpName.FW_reshape", ins := [9590], outs := [9592], params := [2048, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9591, 5324], outs := [9597] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9592, 5324], outs := [9598] }, { rank := 0, op := "OpName.FW_view", ins := [9597], outs := [9607], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [9598], outs := [9608], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [9551, 9607], outs := [9611] }, { rank := 1, op := "OpName.FW_mul", ins := [9552, 9608], outs := [9612] }, { rank := 0, op := "OpName.FW_add", ins := [9537, 9611], outs := [9615] }, { rank := 1, op := "OpName.FW_add", ins := [9538, 9612], outs := [9616] }, { rank := 0, op := "OpName.FW_float", ins := [9615], outs := [9621] }, { rank := 1, op := "OpName.FW_float", ins := [9616], outs := [9622] }, { rank := 0, op := "OpName.FW_add", ins := [15683, 9621], outs := [9625] }]

theorem pmChunk_24_wf : ∀ n ∈ pmChunk_24, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_24, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_960_wf
  · rw [h1]
    exact pm_node_961_wf
  · rw [h2]
    exact pm_node_962_wf
  · rw [h3]
    exact pm_node_963_wf
  · rw [h4]
    exact pm_node_964_wf
  · rw [h5]
    exact pm_node_965_wf
  · rw [h6]
    exact pm_node_966_wf
  · rw [h7]
    exact pm_node_967_wf
  · rw [h8]
    exact pm_node_968_wf
  · rw [h9]
    exact pm_node_969_wf
  · rw [h10]
    exact pm_node_970_wf
  · rw [h11]
    exact pm_node_971_wf
  · rw [h12]
    exact pm_node_972_wf
  · rw [h13]
    exact pm_node_973_wf
  · rw [h14]
    exact pm_node_974_wf
  · rw [h15]
    exact pm_node_975_wf
  · rw [h16]
    exact pm_node_976_wf
  · rw [h17]
    exact pm_node_977_wf
  · rw [h18]
    exact pm_node_978_wf
  · rw [h19]
    exact pm_node_979_wf
  · rw [h20]
    exact pm_node_980_wf
  · rw [h21]
    exact pm_node_981_wf
  · rw [h22]
    exact pm_node_982_wf
  · rw [h23]
    exact pm_node_983_wf
  · rw [h24]
    exact pm_node_984_wf
  · rw [h25]
    exact pm_node_985_wf
  · rw [h26]
    exact pm_node_986_wf
  · rw [h27]
    exact pm_node_987_wf
  · rw [h28]
    exact pm_node_988_wf
  · rw [h29]
    exact pm_node_989_wf
  · rw [h30]
    exact pm_node_990_wf
  · rw [h31]
    exact pm_node_991_wf
  · rw [h32]
    exact pm_node_992_wf
  · rw [h33]
    exact pm_node_993_wf
  · rw [h34]
    exact pm_node_994_wf
  · rw [h35]
    exact pm_node_995_wf
  · rw [h36]
    exact pm_node_996_wf
  · rw [h37]
    exact pm_node_997_wf
  · rw [h38]
    exact pm_node_998_wf
  · rw [h39]
    exact pm_node_999_wf

def pmChunk_25 : List NodeDecl :=
  [{ rank := 1, op := "OpName.FW_add", ins := [15691, 9622], outs := [9626] }, { rank := 0, op := "OpName.FW_multiref", ins := [9625], outs := [14597, 13257], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [9626], outs := [14599, 13258], params := [2] }, { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [13257, 5337], outs := [9655], params := [2, 0] }, { rank := 0, op := "OpName.AllGatherPrim", ins := [14597, 14599], outs := [11917], params := [0] }, { rank := 1, op := "OpName.FW_maybe_shuffle", ins := [13258, 5337], outs := [9656], params := [2, 1] }, { rank := 0, op := "OpName.FW_multiref", ins := [9655], outs := [15969, 15973], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [11917, 5331], outs := [5332] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [11917, 5331], outs := [5332] }, { rank := 1, op := "OpName.FW_multiref", ins := [9656], outs := [15977, 15981], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [15969, 5339], outs := [9657] }, { rank := 0, op := "OpName.FW_multiref", ins := [5332], outs := [15741, 15745], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [5332], outs := [15749, 15753], params := [2] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [15977, 5339], outs := [9658] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [9657, 5341], outs := [9659] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15741, 5333], outs := [5334] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15745, 5335], outs := [5336] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15749, 5333], outs := [5334] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15753, 5335], outs := [5336] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [9658, 5341], outs := [9660] }, { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [15767, 15771, 15775, 15779, 15783, 15787, 15791, 15795, 15799, 15803, 15807, 15811], params := [12] }, { rank := 1, op := "OpName.FW_multiref", ins := [5334], outs := [15815, 15819, 15823, 15827, 15831, 15835, 15839, 15843, 15847, 15851, 15855, 15859], params := [12] }, { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [15873, 15877, 15881, 15885, 15889, 15893, 15897, 15901, 15905, 15909, 15913, 15917], params := [12] }, { rank := 1, op := "OpName.FW_multiref", ins := [5336], outs := [15921, 15925, 15929, 15933, 15937, 15941, 15945, 15949, 15953, 15957, 15961, 15965], params := [12] }, { rank := 0, op := "OpName.FW_to", ins := [15767], outs := [5343] }, { rank := 0, op := "OpName.FW_to", ins := [15771], outs := [5392] }, { rank := 0, op := "OpName.FW_to", ins := [15775], outs := [5441] }, { rank := 0, op := "OpName.FW_to", ins := [15779], outs := [5490] }, { rank := 0, op := "OpName.FW_to", ins := [15783], outs := [5539] }, { rank := 0, op := "OpName.FW_to", ins := [15787], outs := [5588] }, { rank := 0, op := "OpName.FW_to", ins := [15791], outs := [5637] }, { rank := 0, op := "OpName.FW_to", ins := [15795], outs := [5686] }, { rank := 0, op := "OpName.FW_to", ins := [15799], outs := [5735] }, { rank := 0, op := "OpName.FW_to", ins := [15803], outs := [5784] }, { rank := 0, op := "OpName.FW_to", ins := [15807], outs := [5833] }, { rank := 0, op := "OpName.FW_to", ins := [15811], outs := [5882] }, { rank := 1, op := "OpName.FW_to", ins := [15815], outs := [5343] }, { rank := 1, op := "OpName.FW_to", ins := [15819], outs := [5392] }, { rank := 1, op := "OpName.FW_to", ins := [15823], outs := [5441] }, { rank := 1, op := "OpName.FW_to", ins := [15827], outs := [5490] }]

theorem pmChunk_25_wf : ∀ n ∈ pmChunk_25, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_25, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_1000_wf
  · rw [h1]
    exact pm_node_1001_wf
  · rw [h2]
    exact pm_node_1002_wf
  · rw [h3]
    exact pm_node_1003_wf
  · rw [h4]
    exact pm_node_1004_wf
  · rw [h5]
    exact pm_node_1005_wf
  · rw [h6]
    exact pm_node_1006_wf
  · rw [h7]
    exact pm_node_1007_wf
  · rw [h8]
    exact pm_node_1008_wf
  · rw [h9]
    exact pm_node_1009_wf
  · rw [h10]
    exact pm_node_1010_wf
  · rw [h11]
    exact pm_node_1011_wf
  · rw [h12]
    exact pm_node_1012_wf
  · rw [h13]
    exact pm_node_1013_wf
  · rw [h14]
    exact pm_node_1014_wf
  · rw [h15]
    exact pm_node_1015_wf
  · rw [h16]
    exact pm_node_1016_wf
  · rw [h17]
    exact pm_node_1017_wf
  · rw [h18]
    exact pm_node_1018_wf
  · rw [h19]
    exact pm_node_1019_wf
  · rw [h20]
    exact pm_node_1020_wf
  · rw [h21]
    exact pm_node_1021_wf
  · rw [h22]
    exact pm_node_1022_wf
  · rw [h23]
    exact pm_node_1023_wf
  · rw [h24]
    exact pm_node_1024_wf
  · rw [h25]
    exact pm_node_1025_wf
  · rw [h26]
    exact pm_node_1026_wf
  · rw [h27]
    exact pm_node_1027_wf
  · rw [h28]
    exact pm_node_1028_wf
  · rw [h29]
    exact pm_node_1029_wf
  · rw [h30]
    exact pm_node_1030_wf
  · rw [h31]
    exact pm_node_1031_wf
  · rw [h32]
    exact pm_node_1032_wf
  · rw [h33]
    exact pm_node_1033_wf
  · rw [h34]
    exact pm_node_1034_wf
  · rw [h35]
    exact pm_node_1035_wf
  · rw [h36]
    exact pm_node_1036_wf
  · rw [h37]
    exact pm_node_1037_wf
  · rw [h38]
    exact pm_node_1038_wf
  · rw [h39]
    exact pm_node_1039_wf

def pmChunk_26 : List NodeDecl :=
  [{ rank := 1, op := "OpName.FW_to", ins := [15831], outs := [5539] }, { rank := 1, op := "OpName.FW_to", ins := [15835], outs := [5588] }, { rank := 1, op := "OpName.FW_to", ins := [15839], outs := [5637] }, { rank := 1, op := "OpName.FW_to", ins := [15843], outs := [5686] }, { rank := 1, op := "OpName.FW_to", ins := [15847], outs := [5735] }, { rank := 1, op := "OpName.FW_to", ins := [15851], outs := [5784] }, { rank := 1, op := "OpName.FW_to", ins := [15855], outs := [5833] }, { rank := 1, op := "OpName.FW_to", ins := [15859], outs := [5882] }, { rank := 0, op := "OpName.FW_to", ins := [15873], outs := [5344] }, { rank := 0, op := "OpName.FW_to", ins := [15877], outs := [5393] }, { rank := 0, op := "OpName.FW_to", ins := [15881], outs := [5442] }, { rank := 0, op := "OpName.FW_to", ins := [15885], outs := [5491] }, { rank := 0, op := "OpName.FW_to", ins := [15889], outs := [5540] }, { rank := 0, op := "OpName.FW_to", ins := [15893], outs := [5589] }, { rank := 0, op := "OpName.FW_to", ins := [15897], outs := [5638] }, { rank := 0, op := "OpName.FW_to", ins := [15901], outs := [5687] }, { rank := 0, op := "OpName.FW_to", ins := [15905], outs := [5736] }, { rank := 0, op := "OpName.FW_to", ins := [15909], outs := [5785] }, { rank := 0, op := "OpName.FW_to", ins := [15913], outs := [5834] }, { rank := 0, op := "OpName.FW_to", ins := [15917], outs := [5883] }, { rank := 1, op := "OpName.FW_to", ins := [15921], outs := [5344] }, { rank := 1, op := "OpName.FW_to", ins := [15925], outs := [5393] }, { rank := 1, op := "OpName.FW_to", ins := [15929], outs := [5442] }, { rank := 1, op := "OpName.FW_to", ins := [15933], outs := [5491] }, { rank := 1, op := "OpName.FW_to", ins := [15937], outs := [5540] }, { rank := 1, op := "OpName.FW_to", ins := [15941], outs := [5589] }, { rank := 1, op := "OpName.FW_to", ins := [15945], outs := [5638] }, { rank := 1, op := "OpName.FW_to", ins := [15949], outs := [5687] }, { rank := 1, op := "OpName.FW_to", ins := [15953], outs := [5736] }, { rank := 1, op := "OpName.FW_to", ins := [15957], outs := [5785] }, { rank := 1, op := "OpName.FW_to", ins := [15961], outs := [5834] }, { rank := 1, op := "OpName.FW_to", ins := [15965], outs := [5883] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [9659, 5343, 5344, 5345, 5346], outs := [9687], params := [16, 4, 64, 64, 1, 0] }, { rank := 1, op := "OpName.FW_attn_zigzag", ins := [9660, 5343, 5344, 5345, 5346], outs := [9688], params := [16, 4, 64, 64, 1, 0] }, { rank := 0, op := "OpName.FW_reshape", ins := [9687], outs := [9689], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [9688], outs := [9690], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [9689], outs := [9695], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [9690], outs := [9696], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9695, 5350], outs := [9699] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9696, 5350], outs := [9700] }]

theorem pmChunk_26_wf : ∀ n ∈ pmChunk_26, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_26, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_1040_wf
  · rw [h1]
    exact pm_node_1041_wf
  · rw [h2]
    exact pm_node_1042_wf
  · rw [h3]
    exact pm_node_1043_wf
  · rw [h4]
    exact pm_node_1044_wf
  · rw [h5]
    exact pm_node_1045_wf
  · rw [h6]
    exact pm_node_1046_wf
  · rw [h7]
    exact pm_node_1047_wf
  · rw [h8]
    exact pm_node_1048_wf
  · rw [h9]
    exact pm_node_1049_wf
  · rw [h10]
    exact pm_node_1050_wf
  · rw [h11]
    exact pm_node_1051_wf
  · rw [h12]
    exact pm_node_1052_wf
  · rw [h13]
    exact pm_node_1053_wf
  · rw [h14]
    exact pm_node_1054_wf
  · rw [h15]
    exact pm_node_1055_wf
  · rw [h16]
    exact pm_node_1056_wf
  · rw [h17]
    exact pm_node_1057_wf
  · rw [h18]
    exact pm_node_1058_wf
  · rw [h19]
    exact pm_node_1059_wf
  · rw [h20]
    exact pm_node_1060_wf
  · rw [h21]
    exact pm_node_1061_wf
  · rw [h22]
    exact pm_node_1062_wf
  · rw [h23]
    exact pm_node_1063_wf
  · rw [h24]
    exact pm_node_1064_wf
  · rw [h25]
    exact pm_node_1065_wf
  · rw [h26]
    exact pm_node_1066_wf
  · rw [h27]
    exact pm_node_1067_wf
  · rw [h28]
    exact pm_node_1068_wf
  · rw [h29]
    exact pm_node_1069_wf
  · rw [h30]
    exact pm_node_1070_wf
  · rw [h31]
    exact pm_node_1071_wf
  · rw [h32]
    exact pm_node_1072_wf
  · rw [h33]
    exact pm_node_1073_wf
  · rw [h34]
    exact pm_node_1074_wf
  · rw [h35]
    exact pm_node_1075_wf
  · rw [h36]
    exact pm_node_1076_wf
  · rw [h37]
    exact pm_node_1077_wf
  · rw [h38]
    exact pm_node_1078_wf
  · rw [h39]
    exact pm_node_1079_wf

def pmChunk_27 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_view", ins := [9699], outs := [9709], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [9700], outs := [9710], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [9709], outs := [9713] }, { rank := 1, op := "OpName.FW_float", ins := [9710], outs := [9714] }, { rank := 0, op := "OpName.FW_add", ins := [15973, 9713], outs := [9717] }, { rank := 1, op := "OpName.FW_add", ins := [15981, 9714], outs := [9718] }, { rank := 0, op := "OpName.FW_multiref", ins := [9717], outs := [15985, 15989], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [9718], outs := [15993, 15997], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [15985, 5355], outs := [9721] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [15993, 5355], outs := [9722] }, { rank := 0, op := "OpName.FW_multiref", ins := [9721], outs := [16004, 16008, 16012, 16016, 16020], params := [5] }, { rank := 1, op := "OpName.FW_multiref", ins := [9722], outs := [16027, 16031, 16035, 16039, 16043], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [16004], outs := [9723] }, { rank := 0, op := "OpName.FW_reshape", ins := [16012], outs := [9743], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [16016], outs := [9757], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [16020], outs := [9775], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_float", ins := [16027], outs := [9724] }, { rank := 1, op := "OpName.FW_reshape", ins := [16035], outs := [9744], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [16039], outs := [9758], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [16043], outs := [9776], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [9723, 5358], outs := [9729] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9743, 5367], outs := [9747] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9757, 5372], outs := [9761] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9775, 5376], outs := [9779] }, { rank := 1, op := "OpName.FW_norm_linear", ins := [9724, 5358], outs := [9730] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9744, 5367], outs := [9748] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9758, 5372], outs := [9762] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9776, 5376], outs := [9780] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [9729], outs := [9731, 9733, 9735], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [9747], outs := [9753], params := [2048, 1] }, { rank := 0, op := "OpName.FW_view", ins := [9761], outs := [9771], params := [2048, 512] }, { rank := 0, op := "OpName.FW_view", ins := [9779], outs := [9789], params := [2048, 512] }, { rank := 1, op := "OpName.FW_topk_routing", ins := [9730], outs := [9732, 9734, 9736], params := [8, 1] }, { rank := 1, op := "OpName.FW_view", ins := [9748], outs := [9754], params := [2048, 1] }, { rank := 1, op := "OpName.FW_view", ins := [9762], outs := [9772], params := [2048, 512] }, { rank := 1, op := "OpName.FW_view", ins := [9780], outs := [9790], params := [2048, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16008, 9731, 9733, 9737, 9739], outs := [9741], params := [64, 0, 32, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [9753], outs := [9755] }, { rank := 0, op := "OpName.FW_swiglu", ins := [9771, 9789], outs := [9793] }, { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16031, 9732, 9734, 9738, 9740], outs := [9742], params := [64, 32, 64, 8] }]

theorem pmChunk_27_wf : ∀ n ∈ pmChunk_27, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_27, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_1080_wf
  · rw [h1]
    exact pm_node_1081_wf
  · rw [h2]
    exact pm_node_1082_wf
  · rw [h3]
    exact pm_node_1083_wf
  · rw [h4]
    exact pm_node_1084_wf
  · rw [h5]
    exact pm_node_1085_wf
  · rw [h6]
    exact pm_node_1086_wf
  · rw [h7]
    exact pm_node_1087_wf
  · rw [h8]
    exact pm_node_1088_wf
  · rw [h9]
    exact pm_node_1089_wf
  · rw [h10]
    exact pm_node_1090_wf
  · rw [h11]
    exact pm_node_1091_wf
  · rw [h12]
    exact pm_node_1092_wf
  · rw [h13]
    exact pm_node_1093_wf
  · rw [h14]
    exact pm_node_1094_wf
  · rw [h15]
    exact pm_node_1095_wf
  · rw [h16]
    exact pm_node_1096_wf
  · rw [h17]
    exact pm_node_1097_wf
  · rw [h18]
    exact pm_node_1098_wf
  · rw [h19]
    exact pm_node_1099_wf
  · rw [h20]
    exact pm_node_1100_wf
  · rw [h21]
    exact pm_node_1101_wf
  · rw [h22]
    exact pm_node_1102_wf
  · rw [h23]
    exact pm_node_1103_wf
  · rw [h24]
    exact pm_node_1104_wf
  · rw [h25]
    exact pm_node_1105_wf
  · rw [h26]
    exact pm_node_1106_wf
  · rw [h27]
    exact pm_node_1107_wf
  · rw [h28]
    exact pm_node_1108_wf
  · rw [h29]
    exact pm_node_1109_wf
  · rw [h30]
    exact pm_node_1110_wf
  · rw [h31]
    exact pm_node_1111_wf
  · rw [h32]
    exact pm_node_1112_wf
  · rw [h33]
    exact pm_node_1113_wf
  · rw [h34]
    exact pm_node_1114_wf
  · rw [h35]
    exact pm_node_1115_wf
  · rw [h36]
    exact pm_node_1116_wf
  · rw [h37]
    exact pm_node_1117_wf
  · rw [h38]
    exact pm_node_1118_wf
  · rw [h39]
    exact pm_node_1119_wf

def pmChunk_28 : List NodeDecl :=
  [{ rank := 1, op := "OpName.FW_sigmoid", ins := [9754], outs := [9756] }, { rank := 1, op := "OpName.FW_swiglu", ins := [9772, 9790], outs := [9794] }, { rank := 0, op := "OpName.FW_reshape", ins := [9793], outs := [9795], params := [2048, 512] }, { rank := 1, op := "OpName.FW_reshape", ins := [9794], outs := [9796], params := [2048, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9795, 5381], outs := [9801] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9796, 5381], outs := [9802] }, { rank := 0, op := "OpName.FW_view", ins := [9801], outs := [9811], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [9802], outs := [9812], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [9755, 9811], outs := [9815] }, { rank := 1, op := "OpName.FW_mul", ins := [9756, 9812], outs := [9816] }, { rank := 0, op := "OpName.FW_add", ins := [9741, 9815], outs := [9819] }, { rank := 1, op := "OpName.FW_add", ins := [9742, 9816], outs := [9820] }, { rank := 0, op := "OpName.FW_float", ins := [9819], outs := [9825] }, { rank := 1, op := "OpName.FW_float", ins := [9820], outs := [9826] }, { rank := 0, op := "OpName.FW_add", ins := [15989, 9825], outs := [9829] }, { rank := 1, op := "OpName.FW_add", ins := [15997, 9826], outs := [9830] }, { rank := 0, op := "OpName.FW_multiref", ins := [9829], outs := [16047, 16051], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [9830], outs := [16055, 16059], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [16047, 5388], outs := [9833] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [16055, 5388], outs := [9834] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [9833, 5390], outs := [9835] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [9834, 5390], outs := [9836] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [9835, 5392, 5393, 5394, 5395], outs := [9859], params := [16, 4, 64, 64, 1, 0] }, { rank := 1, op := "OpName.FW_attn_zigzag", ins := [9836, 5392, 5393, 5394, 5395], outs := [9860], params := [16, 4, 64, 64, 1, 0] }, { rank := 0, op := "OpName.FW_reshape", ins := [9859], outs := [9861], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [9860], outs := [9862], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [9861], outs := [9867], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [9862], outs := [9868], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9867, 5399], outs := [9871] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9868, 5399], outs := [9872] }, { rank := 0, op := "OpName.FW_view", ins := [9871], outs := [9881], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [9872], outs := [9882], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [9881], outs := [9885] }, { rank := 1, op := "OpName.FW_float", ins := [9882], outs := [9886] }, { rank := 0, op := "OpName.FW_add", ins := [16051, 9885], outs := [9889] }, { rank := 1, op := "OpName.FW_add", ins := [16059, 9886], outs := [9890] }, { rank := 0, op := "OpName.FW_multiref", ins := [9889], outs := [16063, 16067], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [9890], outs := [16071, 16075], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [16063, 5404], outs := [9893] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [16071, 5404], outs := [9894] }]

theorem pmChunk_28_wf : ∀ n ∈ pmChunk_28, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_28, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_1120_wf
  · rw [h1]
    exact pm_node_1121_wf
  · rw [h2]
    exact pm_node_1122_wf
  · rw [h3]
    exact pm_node_1123_wf
  · rw [h4]
    exact pm_node_1124_wf
  · rw [h5]
    exact pm_node_1125_wf
  · rw [h6]
    exact pm_node_1126_wf
  · rw [h7]
    exact pm_node_1127_wf
  · rw [h8]
    exact pm_node_1128_wf
  · rw [h9]
    exact pm_node_1129_wf
  · rw [h10]
    exact pm_node_1130_wf
  · rw [h11]
    exact pm_node_1131_wf
  · rw [h12]
    exact pm_node_1132_wf
  · rw [h13]
    exact pm_node_1133_wf
  · rw [h14]
    exact pm_node_1134_wf
  · rw [h15]
    exact pm_node_1135_wf
  · rw [h16]
    exact pm_node_1136_wf
  · rw [h17]
    exact pm_node_1137_wf
  · rw [h18]
    exact pm_node_1138_wf
  · rw [h19]
    exact pm_node_1139_wf
  · rw [h20]
    exact pm_node_1140_wf
  · rw [h21]
    exact pm_node_1141_wf
  · rw [h22]
    exact pm_node_1142_wf
  · rw [h23]
    exact pm_node_1143_wf
  · rw [h24]
    exact pm_node_1144_wf
  · rw [h25]
    exact pm_node_1145_wf
  · rw [h26]
    exact pm_node_1146_wf
  · rw [h27]
    exact pm_node_1147_wf
  · rw [h28]
    exact pm_node_1148_wf
  · rw [h29]
    exact pm_node_1149_wf
  · rw [h30]
    exact pm_node_1150_wf
  · rw [h31]
    exact pm_node_1151_wf
  · rw [h32]
    exact pm_node_1152_wf
  · rw [h33]
    exact pm_node_1153_wf
  · rw [h34]
    exact pm_node_1154_wf
  · rw [h35]
    exact pm_node_1155_wf
  · rw [h36]
    exact pm_node_1156_wf
  · rw [h37]
    exact pm_node_1157_wf
  · rw [h38]
    exact pm_node_1158_wf
  · rw [h39]
    exact pm_node_1159_wf

def pmChunk_29 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_multiref", ins := [9893], outs := [16082, 16086, 16090, 16094, 16098], params := [5] }, { rank := 1, op := "OpName.FW_multiref", ins := [9894], outs := [16105, 16109, 16113, 16117, 16121], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [16082], outs := [9895] }, { rank := 0, op := "OpName.FW_reshape", ins := [16090], outs := [9915], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [16094], outs := [9929], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [16098], outs := [9947], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_float", ins := [16105], outs := [9896] }, { rank := 1, op := "OpName.FW_reshape", ins := [16113], outs := [9916], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [16117], outs := [9930], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [16121], outs := [9948], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [9895, 5407], outs := [9901] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9915, 5416], outs := [9919] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9929, 5421], outs := [9933] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9947, 5425], outs := [9951] }, { rank := 1, op := "OpName.FW_norm_linear", ins := [9896, 5407], outs := [9902] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9916, 5416], outs := [9920] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9930, 5421], outs := [9934] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9948, 5425], outs := [9952] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [9901], outs := [9903, 9905, 9907], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [9919], outs := [9925], params := [2048, 1] }, { rank := 0, op := "OpName.FW_view", ins := [9933], outs := [9943], params := [2048, 512] }, { rank := 0, op := "OpName.FW_view", ins := [9951], outs := [9961], params := [2048, 512] }, { rank := 1, op := "OpName.FW_topk_routing", ins := [9902], outs := [9904, 9906, 9908], params := [8, 1] }, { rank := 1, op := "OpName.FW_view", ins := [9920], outs := [9926], params := [2048, 1] }, { rank := 1, op := "OpName.FW_view", ins := [9934], outs := [9944], params := [2048, 512] }, { rank := 1, op := "OpName.FW_view", ins := [9952], outs := [9962], params := [2048, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16086, 9903, 9905, 9909, 9911], outs := [9913], params := [64, 0, 32, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [9925], outs := [9927] }, { rank := 0, op := "OpName.FW_swiglu", ins := [9943, 9961], outs := [9965] }, { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16109, 9904, 9906, 9910, 9912], outs := [9914], params := [64, 32, 64, 8] }, { rank := 1, op := "OpName.FW_sigmoid", ins := [9926], outs := [9928] }, { rank := 1, op := "OpName.FW_swiglu", ins := [9944, 9962], outs := [9966] }, { rank := 0, op := "OpName.FW_reshape", ins := [9965], outs := [9967], params := [2048, 512] }, { rank := 1, op := "OpName.FW_reshape", ins := [9966], outs := [9968], params := [2048, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9967, 5430], outs := [9973] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9968, 5430], outs := [9974] }, { rank := 0, op := "OpName.FW_view", ins := [9973], outs := [9983], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [9974], outs := [9984], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [9927, 9983], outs := [9987] }, { rank := 1, op := "OpName.FW_mul", ins := [9928, 9984], outs := [9988] }]

theorem pmChunk_29_wf : ∀ n ∈ pmChunk_29, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_29, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_1160_wf
  · rw [h1]
    exact pm_node_1161_wf
  · rw [h2]
    exact pm_node_1162_wf
  · rw [h3]
    exact pm_node_1163_wf
  · rw [h4]
    exact pm_node_1164_wf
  · rw [h5]
    exact pm_node_1165_wf
  · rw [h6]
    exact pm_node_1166_wf
  · rw [h7]
    exact pm_node_1167_wf
  · rw [h8]
    exact pm_node_1168_wf
  · rw [h9]
    exact pm_node_1169_wf
  · rw [h10]
    exact pm_node_1170_wf
  · rw [h11]
    exact pm_node_1171_wf
  · rw [h12]
    exact pm_node_1172_wf
  · rw [h13]
    exact pm_node_1173_wf
  · rw [h14]
    exact pm_node_1174_wf
  · rw [h15]
    exact pm_node_1175_wf
  · rw [h16]
    exact pm_node_1176_wf
  · rw [h17]
    exact pm_node_1177_wf
  · rw [h18]
    exact pm_node_1178_wf
  · rw [h19]
    exact pm_node_1179_wf
  · rw [h20]
    exact pm_node_1180_wf
  · rw [h21]
    exact pm_node_1181_wf
  · rw [h22]
    exact pm_node_1182_wf
  · rw [h23]
    exact pm_node_1183_wf
  · rw [h24]
    exact pm_node_1184_wf
  · rw [h25]
    exact pm_node_1185_wf
  · rw [h26]
    exact pm_node_1186_wf
  · rw [h27]
    exact pm_node_1187_wf
  · rw [h28]
    exact pm_node_1188_wf
  · rw [h29]
    exact pm_node_1189_wf
  · rw [h30]
    exact pm_node_1190_wf
  · rw [h31]
    exact pm_node_1191_wf
  · rw [h32]
    exact pm_node_1192_wf
  · rw [h33]
    exact pm_node_1193_wf
  · rw [h34]
    exact pm_node_1194_wf
  · rw [h35]
    exact pm_node_1195_wf
  · rw [h36]
    exact pm_node_1196_wf
  · rw [h37]
    exact pm_node_1197_wf
  · rw [h38]
    exact pm_node_1198_wf
  · rw [h39]
    exact pm_node_1199_wf

def pmChunk_30 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_add", ins := [9913, 9987], outs := [9991] }, { rank := 1, op := "OpName.FW_add", ins := [9914, 9988], outs := [9992] }, { rank := 0, op := "OpName.FW_float", ins := [9991], outs := [9997] }, { rank := 1, op := "OpName.FW_float", ins := [9992], outs := [9998] }, { rank := 0, op := "OpName.FW_add", ins := [16067, 9997], outs := [10001] }, { rank := 1, op := "OpName.FW_add", ins := [16075, 9998], outs := [10002] }, { rank := 0, op := "OpName.FW_multiref", ins := [10001], outs := [16125, 16129], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [10002], outs := [16133, 16137], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [16125, 5437], outs := [10005] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [16133, 5437], outs := [10006] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [10005, 5439], outs := [10007] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [10006, 5439], outs := [10008] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [10007, 5441, 5442, 5443, 5444], outs := [10031], params := [16, 4, 64, 64, 1, 0] }, { rank := 1, op := "OpName.FW_attn_zigzag", ins := [10008, 5441, 5442, 5443, 5444], outs := [10032], params := [16, 4, 64, 64, 1, 0] }, { rank := 0, op := "OpName.FW_reshape", ins := [10031], outs := [10033], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [10032], outs := [10034], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [10033], outs := [10039], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [10034], outs := [10040], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10039, 5448], outs := [10043] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10040, 5448], outs := [10044] }, { rank := 0, op := "OpName.FW_view", ins := [10043], outs := [10053], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [10044], outs := [10054], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [10053], outs := [10057] }, { rank := 1, op := "OpName.FW_float", ins := [10054], outs := [10058] }, { rank := 0, op := "OpName.FW_add", ins := [16129, 10057], outs := [10061] }, { rank := 1, op := "OpName.FW_add", ins := [16137, 10058], outs := [10062] }, { rank := 0, op := "OpName.FW_multiref", ins := [10061], outs := [16141, 16145], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [10062], outs := [16149, 16153], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [16141, 5453], outs := [10065] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [16149, 5453], outs := [10066] }, { rank := 0, op := "OpName.FW_multiref", ins := [10065], outs := [16160, 16164, 16168, 16172, 16176], params := [5] }, { rank := 1, op := "OpName.FW_multiref", ins := [10066], outs := [16183, 16187, 16191, 16195, 16199], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [16160], outs := [10067] }, { rank := 0, op := "OpName.FW_reshape", ins := [16168], outs := [10087], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [16172], outs := [10101], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [16176], outs := [10119], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_float", ins := [16183], outs := [10068] }, { rank := 1, op := "OpName.FW_reshape", ins := [16191], outs := [10088], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [16195], outs := [10102], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [16199], outs := [10120], params := [2048, 1024] }]

theorem pmChunk_30_wf : ∀ n ∈ pmChunk_30, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_30, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_1200_wf
  · rw [h1]
    exact pm_node_1201_wf
  · rw [h2]
    exact pm_node_1202_wf
  · rw [h3]
    exact pm_node_1203_wf
  · rw [h4]
    exact pm_node_1204_wf
  · rw [h5]
    exact pm_node_1205_wf
  · rw [h6]
    exact pm_node_1206_wf
  · rw [h7]
    exact pm_node_1207_wf
  · rw [h8]
    exact pm_node_1208_wf
  · rw [h9]
    exact pm_node_1209_wf
  · rw [h10]
    exact pm_node_1210_wf
  · rw [h11]
    exact pm_node_1211_wf
  · rw [h12]
    exact pm_node_1212_wf
  · rw [h13]
    exact pm_node_1213_wf
  · rw [h14]
    exact pm_node_1214_wf
  · rw [h15]
    exact pm_node_1215_wf
  · rw [h16]
    exact pm_node_1216_wf
  · rw [h17]
    exact pm_node_1217_wf
  · rw [h18]
    exact pm_node_1218_wf
  · rw [h19]
    exact pm_node_1219_wf
  · rw [h20]
    exact pm_node_1220_wf
  · rw [h21]
    exact pm_node_1221_wf
  · rw [h22]
    exact pm_node_1222_wf
  · rw [h23]
    exact pm_node_1223_wf
  · rw [h24]
    exact pm_node_1224_wf
  · rw [h25]
    exact pm_node_1225_wf
  · rw [h26]
    exact pm_node_1226_wf
  · rw [h27]
    exact pm_node_1227_wf
  · rw [h28]
    exact pm_node_1228_wf
  · rw [h29]
    exact pm_node_1229_wf
  · rw [h30]
    exact pm_node_1230_wf
  · rw [h31]
    exact pm_node_1231_wf
  · rw [h32]
    exact pm_node_1232_wf
  · rw [h33]
    exact pm_node_1233_wf
  · rw [h34]
    exact pm_node_1234_wf
  · rw [h35]
    exact pm_node_1235_wf
  · rw [h36]
    exact pm_node_1236_wf
  · rw [h37]
    exact pm_node_1237_wf
  · rw [h38]
    exact pm_node_1238_wf
  · rw [h39]
    exact pm_node_1239_wf

def pmChunk_31 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_norm_linear", ins := [10067, 5456], outs := [10073] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10087, 5465], outs := [10091] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10101, 5470], outs := [10105] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10119, 5474], outs := [10123] }, { rank := 1, op := "OpName.FW_norm_linear", ins := [10068, 5456], outs := [10074] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10088, 5465], outs := [10092] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10102, 5470], outs := [10106] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10120, 5474], outs := [10124] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [10073], outs := [10075, 10077, 10079], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [10091], outs := [10097], params := [2048, 1] }, { rank := 0, op := "OpName.FW_view", ins := [10105], outs := [10115], params := [2048, 512] }, { rank := 0, op := "OpName.FW_view", ins := [10123], outs := [10133], params := [2048, 512] }, { rank := 1, op := "OpName.FW_topk_routing", ins := [10074], outs := [10076, 10078, 10080], params := [8, 1] }, { rank := 1, op := "OpName.FW_view", ins := [10092], outs := [10098], params := [2048, 1] }, { rank := 1, op := "OpName.FW_view", ins := [10106], outs := [10116], params := [2048, 512] }, { rank := 1, op := "OpName.FW_view", ins := [10124], outs := [10134], params := [2048, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16164, 10075, 10077, 10081, 10083], outs := [10085], params := [64, 0, 32, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [10097], outs := [10099] }, { rank := 0, op := "OpName.FW_swiglu", ins := [10115, 10133], outs := [10137] }, { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16187, 10076, 10078, 10082, 10084], outs := [10086], params := [64, 32, 64, 8] }, { rank := 1, op := "OpName.FW_sigmoid", ins := [10098], outs := [10100] }, { rank := 1, op := "OpName.FW_swiglu", ins := [10116, 10134], outs := [10138] }, { rank := 0, op := "OpName.FW_reshape", ins := [10137], outs := [10139], params := [2048, 512] }, { rank := 1, op := "OpName.FW_reshape", ins := [10138], outs := [10140], params := [2048, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10139, 5479], outs := [10145] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10140, 5479], outs := [10146] }, { rank := 0, op := "OpName.FW_view", ins := [10145], outs := [10155], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [10146], outs := [10156], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [10099, 10155], outs := [10159] }, { rank := 1, op := "OpName.FW_mul", ins := [10100, 10156], outs := [10160] }, { rank := 0, op := "OpName.FW_add", ins := [10085, 10159], outs := [10163] }, { rank := 1, op := "OpName.FW_add", ins := [10086, 10160], outs := [10164] }, { rank := 0, op := "OpName.FW_float", ins := [10163], outs := [10169] }, { rank := 1, op := "OpName.FW_float", ins := [10164], outs := [10170] }, { rank := 0, op := "OpName.FW_add", ins := [16145, 10169], outs := [10173] }, { rank := 1, op := "OpName.FW_add", ins := [16153, 10170], outs := [10174] }, { rank := 0, op := "OpName.FW_multiref", ins := [10173], outs := [16203, 16207], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [10174], outs := [16211, 16215], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [16203, 5486], outs := [10177] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [16211, 5486], outs := [10178] }]

theorem pmChunk_31_wf : ∀ n ∈ pmChunk_31, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_31, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_1240_wf
  · rw [h1]
    exact pm_node_1241_wf
  · rw [h2]
    exact pm_node_1242_wf
  · rw [h3]
    exact pm_node_1243_wf
  · rw [h4]
    exact pm_node_1244_wf
  · rw [h5]
    exact pm_node_1245_wf
  · rw [h6]
    exact pm_node_1246_wf
  · rw [h7]
    exact pm_node_1247_wf
  · rw [h8]
    exact pm_node_1248_wf
  · rw [h9]
    exact pm_node_1249_wf
  · rw [h10]
    exact pm_node_1250_wf
  · rw [h11]
    exact pm_node_1251_wf
  · rw [h12]
    exact pm_node_1252_wf
  · rw [h13]
    exact pm_node_1253_wf
  · rw [h14]
    exact pm_node_1254_wf
  · rw [h15]
    exact pm_node_1255_wf
  · rw [h16]
    exact pm_node_1256_wf
  · rw [h17]
    exact pm_node_1257_wf
  · rw [h18]
    exact pm_node_1258_wf
  · rw [h19]
    exact pm_node_1259_wf
  · rw [h20]
    exact pm_node_1260_wf
  · rw [h21]
    exact pm_node_1261_wf
  · rw [h22]
    exact pm_node_1262_wf
  · rw [h23]
    exact pm_node_1263_wf
  · rw [h24]
    exact pm_node_1264_wf
  · rw [h25]
    exact pm_node_1265_wf
  · rw [h26]
    exact pm_node_1266_wf
  · rw [h27]
    exact pm_node_1267_wf
  · rw [h28]
    exact pm_node_1268_wf
  · rw [h29]
    exact pm_node_1269_wf
  · rw [h30]
    exact pm_node_1270_wf
  · rw [h31]
    exact pm_node_1271_wf
  · rw [h32]
    exact pm_node_1272_wf
  · rw [h33]
    exact pm_node_1273_wf
  · rw [h34]
    exact pm_node_1274_wf
  · rw [h35]
    exact pm_node_1275_wf
  · rw [h36]
    exact pm_node_1276_wf
  · rw [h37]
    exact pm_node_1277_wf
  · rw [h38]
    exact pm_node_1278_wf
  · rw [h39]
    exact pm_node_1279_wf

def pmChunk_32 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [10177, 5488], outs := [10179] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [10178, 5488], outs := [10180] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [10179, 5490, 5491, 5492, 5493], outs := [10203], params := [16, 4, 64, 64, 1, 0] }, { rank := 1, op := "OpName.FW_attn_zigzag", ins := [10180, 5490, 5491, 5492, 5493], outs := [10204], params := [16, 4, 64, 64, 1, 0] }, { rank := 0, op := "OpName.FW_reshape", ins := [10203], outs := [10205], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [10204], outs := [10206], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [10205], outs := [10211], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [10206], outs := [10212], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10211, 5497], outs := [10215] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10212, 5497], outs := [10216] }, { rank := 0, op := "OpName.FW_view", ins := [10215], outs := [10225], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [10216], outs := [10226], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [10225], outs := [10229] }, { rank := 1, op := "OpName.FW_float", ins := [10226], outs := [10230] }, { rank := 0, op := "OpName.FW_add", ins := [16207, 10229], outs := [10233] }, { rank := 1, op := "OpName.FW_add", ins := [16215, 10230], outs := [10234] }, { rank := 0, op := "OpName.FW_multiref", ins := [10233], outs := [16219, 16223], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [10234], outs := [16227, 16231], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [16219, 5502], outs := [10237] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [16227, 5502], outs := [10238] }, { rank := 0, op := "OpName.FW_multiref", ins := [10237], outs := [16238, 16242, 16246, 16250, 16254], params := [5] }, { rank := 1, op := "OpName.FW_multiref", ins := [10238], outs := [16261, 16265, 16269, 16273, 16277], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [16238], outs := [10239] }, { rank := 0, op := "OpName.FW_reshape", ins := [16246], outs := [10259], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [16250], outs := [10273], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [16254], outs := [10291], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_float", ins := [16261], outs := [10240] }, { rank := 1, op := "OpName.FW_reshape", ins := [16269], outs := [10260], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [16273], outs := [10274], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [16277], outs := [10292], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [10239, 5505], outs := [10245] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10259, 5514], outs := [10263] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10273, 5519], outs := [10277] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10291, 5523], outs := [10295] }, { rank := 1, op := "OpName.FW_norm_linear", ins := [10240, 5505], outs := [10246] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10260, 5514], outs := [10264] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10274, 5519], outs := [10278] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10292, 5523], outs := [10296] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [10245], outs := [10247, 10249, 10251], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [10263], outs := [10269], params := [2048, 1] }]

theorem pmChunk_32_wf : ∀ n ∈ pmChunk_32, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_32, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_1280_wf
  · rw [h1]
    exact pm_node_1281_wf
  · rw [h2]
    exact pm_node_1282_wf
  · rw [h3]
    exact pm_node_1283_wf
  · rw [h4]
    exact pm_node_1284_wf
  · rw [h5]
    exact pm_node_1285_wf
  · rw [h6]
    exact pm_node_1286_wf
  · rw [h7]
    exact pm_node_1287_wf
  · rw [h8]
    exact pm_node_1288_wf
  · rw [h9]
    exact pm_node_1289_wf
  · rw [h10]
    exact pm_node_1290_wf
  · rw [h11]
    exact pm_node_1291_wf
  · rw [h12]
    exact pm_node_1292_wf
  · rw [h13]
    exact pm_node_1293_wf
  · rw [h14]
    exact pm_node_1294_wf
  · rw [h15]
    exact pm_node_1295_wf
  · rw [h16]
    exact pm_node_1296_wf
  · rw [h17]
    exact pm_node_1297_wf
  · rw [h18]
    exact pm_node_1298_wf
  · rw [h19]
    exact pm_node_1299_wf
  · rw [h20]
    exact pm_node_1300_wf
  · rw [h21]
    exact pm_node_1301_wf
  · rw [h22]
    exact pm_node_1302_wf
  · rw [h23]
    exact pm_node_1303_wf
  · rw [h24]
    exact pm_node_1304_wf
  · rw [h25]
    exact pm_node_1305_wf
  · rw [h26]
    exact pm_node_1306_wf
  · rw [h27]
    exact pm_node_1307_wf
  · rw [h28]
    exact pm_node_1308_wf
  · rw [h29]
    exact pm_node_1309_wf
  · rw [h30]
    exact pm_node_1310_wf
  · rw [h31]
    exact pm_node_1311_wf
  · rw [h32]
    exact pm_node_1312_wf
  · rw [h33]
    exact pm_node_1313_wf
  · rw [h34]
    exact pm_node_1314_wf
  · rw [h35]
    exact pm_node_1315_wf
  · rw [h36]
    exact pm_node_1316_wf
  · rw [h37]
    exact pm_node_1317_wf
  · rw [h38]
    exact pm_node_1318_wf
  · rw [h39]
    exact pm_node_1319_wf

def pmChunk_33 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_view", ins := [10277], outs := [10287], params := [2048, 512] }, { rank := 0, op := "OpName.FW_view", ins := [10295], outs := [10305], params := [2048, 512] }, { rank := 1, op := "OpName.FW_topk_routing", ins := [10246], outs := [10248, 10250, 10252], params := [8, 1] }, { rank := 1, op := "OpName.FW_view", ins := [10264], outs := [10270], params := [2048, 1] }, { rank := 1, op := "OpName.FW_view", ins := [10278], outs := [10288], params := [2048, 512] }, { rank := 1, op := "OpName.FW_view", ins := [10296], outs := [10306], params := [2048, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16242, 10247, 10249, 10253, 10255], outs := [10257], params := [64, 0, 32, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [10269], outs := [10271] }, { rank := 0, op := "OpName.FW_swiglu", ins := [10287, 10305], outs := [10309] }, { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16265, 10248, 10250, 10254, 10256], outs := [10258], params := [64, 32, 64, 8] }, { rank := 1, op := "OpName.FW_sigmoid", ins := [10270], outs := [10272] }, { rank := 1, op := "OpName.FW_swiglu", ins := [10288, 10306], outs := [10310] }, { rank := 0, op := "OpName.FW_reshape", ins := [10309], outs := [10311], params := [2048, 512] }, { rank := 1, op := "OpName.FW_reshape", ins := [10310], outs := [10312], params := [2048, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10311, 5528], outs := [10317] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10312, 5528], outs := [10318] }, { rank := 0, op := "OpName.FW_view", ins := [10317], outs := [10327], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [10318], outs := [10328], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [10271, 10327], outs := [10331] }, { rank := 1, op := "OpName.FW_mul", ins := [10272, 10328], outs := [10332] }, { rank := 0, op := "OpName.FW_add", ins := [10257, 10331], outs := [10335] }, { rank := 1, op := "OpName.FW_add", ins := [10258, 10332], outs := [10336] }, { rank := 0, op := "OpName.FW_float", ins := [10335], outs := [10341] }, { rank := 1, op := "OpName.FW_float", ins := [10336], outs := [10342] }, { rank := 0, op := "OpName.FW_add", ins := [16223, 10341], outs := [10345] }, { rank := 1, op := "OpName.FW_add", ins := [16231, 10342], outs := [10346] }, { rank := 0, op := "OpName.FW_multiref", ins := [10345], outs := [16281, 16285], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [10346], outs := [16289, 16293], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [16281, 5535], outs := [10349] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [16289, 5535], outs := [10350] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [10349, 5537], outs := [10351] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [10350, 5537], outs := [10352] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [10351, 5539, 5540, 5541, 5542], outs := [10375], params := [16, 4, 64, 64, 1, 0] }, { rank := 1, op := "OpName.FW_attn_zigzag", ins := [10352, 5539, 5540, 5541, 5542], outs := [10376], params := [16, 4, 64, 64, 1, 0] }, { rank := 0, op := "OpName.FW_reshape", ins := [10375], outs := [10377], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [10376], outs := [10378], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [10377], outs := [10383], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [10378], outs := [10384], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10383, 5546], outs := [10387] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10384, 5546], outs := [10388] }]

theorem pmChunk_33_wf : ∀ n ∈ pmChunk_33, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_33, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_1320_wf
  · rw [h1]
    exact pm_node_1321_wf
  · rw [h2]
    exact pm_node_1322_wf
  · rw [h3]
    exact pm_node_1323_wf
  · rw [h4]
    exact pm_node_1324_wf
  · rw [h5]
    exact pm_node_1325_wf
  · rw [h6]
    exact pm_node_1326_wf
  · rw [h7]
    exact pm_node_1327_wf
  · rw [h8]
    exact pm_node_1328_wf
  · rw [h9]
    exact pm_node_1329_wf
  · rw [h10]
    exact pm_node_1330_wf
  · rw [h11]
    exact pm_node_1331_wf
  · rw [h12]
    exact pm_node_1332_wf
  · rw [h13]
    exact pm_node_1333_wf
  · rw [h14]
    exact pm_node_1334_wf
  · rw [h15]
    exact pm_node_1335_wf
  · rw [h16]
    exact pm_node_1336_wf
  · rw [h17]
    exact pm_node_1337_wf
  · rw [h18]
    exact pm_node_1338_wf
  · rw [h19]
    exact pm_node_1339_wf
  · rw [h20]
    exact pm_node_1340_wf
  · rw [h21]
    exact pm_node_1341_wf
  · rw [h22]
    exact pm_node_1342_wf
  · rw [h23]
    exact pm_node_1343_wf
  · rw [h24]
    exact pm_node_1344_wf
  · rw [h25]
    exact pm_node_1345_wf
  · rw [h26]
    exact pm_node_1346_wf
  · rw [h27]
    exact pm_node_1347_wf
  · rw [h28]
    exact pm_node_1348_wf
  · rw [h29]
    exact pm_node_1349_wf
  · rw [h30]
    exact pm_node_1350_wf
  · rw [h31]
    exact pm_node_1351_wf
  · rw [h32]
    exact pm_node_1352_wf
  · rw [h33]
    exact pm_node_1353_wf
  · rw [h34]
    exact pm_node_1354_wf
  · rw [h35]
    exact pm_node_1355_wf
  · rw [h36]
    exact pm_node_1356_wf
  · rw [h37]
    exact pm_node_1357_wf
  · rw [h38]
    exact pm_node_1358_wf
  · rw [h39]
    exact pm_node_1359_wf

def pmChunk_34 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_view", ins := [10387], outs := [10397], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [10388], outs := [10398], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [10397], outs := [10401] }, { rank := 1, op := "OpName.FW_float", ins := [10398], outs := [10402] }, { rank := 0, op := "OpName.FW_add", ins := [16285, 10401], outs := [10405] }, { rank := 1, op := "OpName.FW_add", ins := [16293, 10402], outs := [10406] }, { rank := 0, op := "OpName.FW_multiref", ins := [10405], outs := [16297, 16301], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [10406], outs := [16305, 16309], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [16297, 5551], outs := [10409] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [16305, 5551], outs := [10410] }, { rank := 0, op := "OpName.FW_multiref", ins := [10409], outs := [16316, 16320, 16324, 16328, 16332], params := [5] }, { rank := 1, op := "OpName.FW_multiref", ins := [10410], outs := [16339, 16343, 16347, 16351, 16355], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [16316], outs := [10411] }, { rank := 0, op := "OpName.FW_reshape", ins := [16324], outs := [10431], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [16328], outs := [10445], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [16332], outs := [10463], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_float", ins := [16339], outs := [10412] }, { rank := 1, op := "OpName.FW_reshape", ins := [16347], outs := [10432], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [16351], outs := [10446], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [16355], outs := [10464], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [10411, 5554], outs := [10417] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10431, 5563], outs := [10435] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10445, 5568], outs := [10449] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10463, 5572], outs := [10467] }, { rank := 1, op := "OpName.FW_norm_linear", ins := [10412, 5554], outs := [10418] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10432, 5563], outs := [10436] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10446, 5568], outs := [10450] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10464, 5572], outs := [10468] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [10417], outs := [10419, 10421, 10423], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [10435], outs := [10441], params := [2048, 1] }, { rank := 0, op := "OpName.FW_view", ins := [10449], outs := [10459], params := [2048, 512] }, { rank := 0, op := "OpName.FW_view", ins := [10467], outs := [10477], params := [2048, 512] }, { rank := 1, op := "OpName.FW_topk_routing", ins := [10418], outs := [10420, 10422, 10424], params := [8, 1] }, { rank := 1, op := "OpName.FW_view", ins := [10436], outs := [10442], params := [2048, 1] }, { rank := 1, op := "OpName.FW_view", ins := [10450], outs := [10460], params := [2048, 512] }, { rank := 1, op := "OpName.FW_view", ins := [10468], outs := [10478], params := [2048, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16320, 10419, 10421, 10425, 10427], outs := [10429], params := [64, 0, 32, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [10441], outs := [10443] }, { rank := 0, op := "OpName.FW_swiglu", ins := [10459, 10477], outs := [10481] }, { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16343, 10420, 10422, 10426, 10428], outs := [10430], params := [64, 32, 64, 8] }]

theorem pmChunk_34_wf : ∀ n ∈ pmChunk_34, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_34, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_1360_wf
  · rw [h1]
    exact pm_node_1361_wf
  · rw [h2]
    exact pm_node_1362_wf
  · rw [h3]
    exact pm_node_1363_wf
  · rw [h4]
    exact pm_node_1364_wf
  · rw [h5]
    exact pm_node_1365_wf
  · rw [h6]
    exact pm_node_1366_wf
  · rw [h7]
    exact pm_node_1367_wf
  · rw [h8]
    exact pm_node_1368_wf
  · rw [h9]
    exact pm_node_1369_wf
  · rw [h10]
    exact pm_node_1370_wf
  · rw [h11]
    exact pm_node_1371_wf
  · rw [h12]
    exact pm_node_1372_wf
  · rw [h13]
    exact pm_node_1373_wf
  · rw [h14]
    exact pm_node_1374_wf
  · rw [h15]
    exact pm_node_1375_wf
  · rw [h16]
    exact pm_node_1376_wf
  · rw [h17]
    exact pm_node_1377_wf
  · rw [h18]
    exact pm_node_1378_wf
  · rw [h19]
    exact pm_node_1379_wf
  · rw [h20]
    exact pm_node_1380_wf
  · rw [h21]
    exact pm_node_1381_wf
  · rw [h22]
    exact pm_node_1382_wf
  · rw [h23]
    exact pm_node_1383_wf
  · rw [h24]
    exact pm_node_1384_wf
  · rw [h25]
    exact pm_node_1385_wf
  · rw [h26]
    exact pm_node_1386_wf
  · rw [h27]
    exact pm_node_1387_wf
  · rw [h28]
    exact pm_node_1388_wf
  · rw [h29]
    exact pm_node_1389_wf
  · rw [h30]
    exact pm_node_1390_wf
  · rw [h31]
    exact pm_node_1391_wf
  · rw [h32]
    exact pm_node_1392_wf
  · rw [h33]
    exact pm_node_1393_wf
  · rw [h34]
    exact pm_node_1394_wf
  · rw [h35]
    exact pm_node_1395_wf
  · rw [h36]
    exact pm_node_1396_wf
  · rw [h37]
    exact pm_node_1397_wf
  · rw [h38]
    exact pm_node_1398_wf
  · rw [h39]
    exact pm_node_1399_wf

def pmChunk_35 : List NodeDecl :=
  [{ rank := 1, op := "OpName.FW_sigmoid", ins := [10442], outs := [10444] }, { rank := 1, op := "OpName.FW_swiglu", ins := [10460, 10478], outs := [10482] }, { rank := 0, op := "OpName.FW_reshape", ins := [10481], outs := [10483], params := [2048, 512] }, { rank := 1, op := "OpName.FW_reshape", ins := [10482], outs := [10484], params := [2048, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10483, 5577], outs := [10489] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10484, 5577], outs := [10490] }, { rank := 0, op := "OpName.FW_view", ins := [10489], outs := [10499], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [10490], outs := [10500], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [10443, 10499], outs := [10503] }, { rank := 1, op := "OpName.FW_mul", ins := [10444, 10500], outs := [10504] }, { rank := 0, op := "OpName.FW_add", ins := [10429, 10503], outs := [10507] }, { rank := 1, op := "OpName.FW_add", ins := [10430, 10504], outs := [10508] }, { rank := 0, op := "OpName.FW_float", ins := [10507], outs := [10513] }, { rank := 1, op := "OpName.FW_float", ins := [10508], outs := [10514] }, { rank := 0, op := "OpName.FW_add", ins := [16301, 10513], outs := [10517] }, { rank := 1, op := "OpName.FW_add", ins := [16309, 10514], outs := [10518] }, { rank := 0, op := "OpName.FW_multiref", ins := [10517], outs := [16359, 16363], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [10518], outs := [16367, 16371], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [16359, 5584], outs := [10521] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [16367, 5584], outs := [10522] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [10521, 5586], outs := [10523] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [10522, 5586], outs := [10524] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [10523, 5588, 5589, 5590, 5591], outs := [10547], params := [16, 4, 64, 64, 1, 0] }, { rank := 1, op := "OpName.FW_attn_zigzag", ins := [10524, 5588, 5589, 5590, 5591], outs := [10548], params := [16, 4, 64, 64, 1, 0] }, { rank := 0, op := "OpName.FW_reshape", ins := [10547], outs := [10549], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [10548], outs := [10550], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [10549], outs := [10555], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [10550], outs := [10556], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10555, 5595], outs := [10559] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10556, 5595], outs := [10560] }, { rank := 0, op := "OpName.FW_view", ins := [10559], outs := [10569], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [10560], outs := [10570], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [10569], outs := [10573] }, { rank := 1, op := "OpName.FW_float", ins := [10570], outs := [10574] }, { rank := 0, op := "OpName.FW_add", ins := [16363, 10573], outs := [10577] }, { rank := 1, op := "OpName.FW_add", ins := [16371, 10574], outs := [10578] }, { rank := 0, op := "OpName.FW_multiref", ins := [10577], outs := [16375, 16379], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [10578], outs := [16383, 16387], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [16375, 5600], outs := [10581] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [16383, 5600], outs := [10582] }]

theorem pmChunk_35_wf : ∀ n ∈ pmChunk_35, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_35, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_1400_wf
  · rw [h1]
    exact pm_node_1401_wf
  · rw [h2]
    exact pm_node_1402_wf
  · rw [h3]
    exact pm_node_1403_wf
  · rw [h4]
    exact pm_node_1404_wf
  · rw [h5]
    exact pm_node_1405_wf
  · rw [h6]
    exact pm_node_1406_wf
  · rw [h7]
    exact pm_node_1407_wf
  · rw [h8]
    exact pm_node_1408_wf
  · rw [h9]
    exact pm_node_1409_wf
  · rw [h10]
    exact pm_node_1410_wf
  · rw [h11]
    exact pm_node_1411_wf
  · rw [h12]
    exact pm_node_1412_wf
  · rw [h13]
    exact pm_node_1413_wf
  · rw [h14]
    exact pm_node_1414_wf
  · rw [h15]
    exact pm_node_1415_wf
  · rw [h16]
    exact pm_node_1416_wf
  · rw [h17]
    exact pm_node_1417_wf
  · rw [h18]
    exact pm_node_1418_wf
  · rw [h19]
    exact pm_node_1419_wf
  · rw [h20]
    exact pm_node_1420_wf
  · rw [h21]
    exact pm_node_1421_wf
  · rw [h22]
    exact pm_node_1422_wf
  · rw [h23]
    exact pm_node_1423_wf
  · rw [h24]
    exact pm_node_1424_wf
  · rw [h25]
    exact pm_node_1425_wf
  · rw [h26]
    exact pm_node_1426_wf
  · rw [h27]
    exact pm_node_1427_wf
  · rw [h28]
    exact pm_node_1428_wf
  · rw [h29]
    exact pm_node_1429_wf
  · rw [h30]
    exact pm_node_1430_wf
  · rw [h31]
    exact pm_node_1431_wf
  · rw [h32]
    exact pm_node_1432_wf
  · rw [h33]
    exact pm_node_1433_wf
  · rw [h34]
    exact pm_node_1434_wf
  · rw [h35]
    exact pm_node_1435_wf
  · rw [h36]
    exact pm_node_1436_wf
  · rw [h37]
    exact pm_node_1437_wf
  · rw [h38]
    exact pm_node_1438_wf
  · rw [h39]
    exact pm_node_1439_wf

def pmChunk_36 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_multiref", ins := [10581], outs := [16394, 16398, 16402, 16406, 16410], params := [5] }, { rank := 1, op := "OpName.FW_multiref", ins := [10582], outs := [16417, 16421, 16425, 16429, 16433], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [16394], outs := [10583] }, { rank := 0, op := "OpName.FW_reshape", ins := [16402], outs := [10603], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [16406], outs := [10617], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [16410], outs := [10635], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_float", ins := [16417], outs := [10584] }, { rank := 1, op := "OpName.FW_reshape", ins := [16425], outs := [10604], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [16429], outs := [10618], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [16433], outs := [10636], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [10583, 5603], outs := [10589] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10603, 5612], outs := [10607] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10617, 5617], outs := [10621] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10635, 5621], outs := [10639] }, { rank := 1, op := "OpName.FW_norm_linear", ins := [10584, 5603], outs := [10590] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10604, 5612], outs := [10608] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10618, 5617], outs := [10622] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10636, 5621], outs := [10640] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [10589], outs := [10591, 10593, 10595], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [10607], outs := [10613], params := [2048, 1] }, { rank := 0, op := "OpName.FW_view", ins := [10621], outs := [10631], params := [2048, 512] }, { rank := 0, op := "OpName.FW_view", ins := [10639], outs := [10649], params := [2048, 512] }, { rank := 1, op := "OpName.FW_topk_routing", ins := [10590], outs := [10592, 10594, 10596], params := [8, 1] }, { rank := 1, op := "OpName.FW_view", ins := [10608], outs := [10614], params := [2048, 1] }, { rank := 1, op := "OpName.FW_view", ins := [10622], outs := [10632], params := [2048, 512] }, { rank := 1, op := "OpName.FW_view", ins := [10640], outs := [10650], params := [2048, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16398, 10591, 10593, 10597, 10599], outs := [10601], params := [64, 0, 32, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [10613], outs := [10615] }, { rank := 0, op := "OpName.FW_swiglu", ins := [10631, 10649], outs := [10653] }, { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16421, 10592, 10594, 10598, 10600], outs := [10602], params := [64, 32, 64, 8] }, { rank := 1, op := "OpName.FW_sigmoid", ins := [10614], outs := [10616] }, { rank := 1, op := "OpName.FW_swiglu", ins := [10632, 10650], outs := [10654] }, { rank := 0, op := "OpName.FW_reshape", ins := [10653], outs := [10655], params := [2048, 512] }, { rank := 1, op := "OpName.FW_reshape", ins := [10654], outs := [10656], params := [2048, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10655, 5626], outs := [10661] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10656, 5626], outs := [10662] }, { rank := 0, op := "OpName.FW_view", ins := [10661], outs := [10671], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [10662], outs := [10672], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [10615, 10671], outs := [10675] }, { rank := 1, op := "OpName.FW_mul", ins := [10616, 10672], outs := [10676] }]

theorem pmChunk_36_wf : ∀ n ∈ pmChunk_36, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_36, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_1440_wf
  · rw [h1]
    exact pm_node_1441_wf
  · rw [h2]
    exact pm_node_1442_wf
  · rw [h3]
    exact pm_node_1443_wf
  · rw [h4]
    exact pm_node_1444_wf
  · rw [h5]
    exact pm_node_1445_wf
  · rw [h6]
    exact pm_node_1446_wf
  · rw [h7]
    exact pm_node_1447_wf
  · rw [h8]
    exact pm_node_1448_wf
  · rw [h9]
    exact pm_node_1449_wf
  · rw [h10]
    exact pm_node_1450_wf
  · rw [h11]
    exact pm_node_1451_wf
  · rw [h12]
    exact pm_node_1452_wf
  · rw [h13]
    exact pm_node_1453_wf
  · rw [h14]
    exact pm_node_1454_wf
  · rw [h15]
    exact pm_node_1455_wf
  · rw [h16]
    exact pm_node_1456_wf
  · rw [h17]
    exact pm_node_1457_wf
  · rw [h18]
    exact pm_node_1458_wf
  · rw [h19]
    exact pm_node_1459_wf
  · rw [h20]
    exact pm_node_1460_wf
  · rw [h21]
    exact pm_node_1461_wf
  · rw [h22]
    exact pm_node_1462_wf
  · rw [h23]
    exact pm_node_1463_wf
  · rw [h24]
    exact pm_node_1464_wf
  · rw [h25]
    exact pm_node_1465_wf
  · rw [h26]
    exact pm_node_1466_wf
  · rw [h27]
    exact pm_node_1467_wf
  · rw [h28]
    exact pm_node_1468_wf
  · rw [h29]
    exact pm_node_1469_wf
  · rw [h30]
    exact pm_node_1470_wf
  · rw [h31]
    exact pm_node_1471_wf
  · rw [h32]
    exact pm_node_1472_wf
  · rw [h33]
    exact pm_node_1473_wf
  · rw [h34]
    exact pm_node_1474_wf
  · rw [h35]
    exact pm_node_1475_wf
  · rw [h36]
    exact pm_node_1476_wf
  · rw [h37]
    exact pm_node_1477_wf
  · rw [h38]
    exact pm_node_1478_wf
  · rw [h39]
    exact pm_node_1479_wf

def pmChunk_37 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_add", ins := [10601, 10675], outs := [10679] }, { rank := 1, op := "OpName.FW_add", ins := [10602, 10676], outs := [10680] }, { rank := 0, op := "OpName.FW_float", ins := [10679], outs := [10685] }, { rank := 1, op := "OpName.FW_float", ins := [10680], outs := [10686] }, { rank := 0, op := "OpName.FW_add", ins := [16379, 10685], outs := [10689] }, { rank := 1, op := "OpName.FW_add", ins := [16387, 10686], outs := [10690] }, { rank := 0, op := "OpName.FW_multiref", ins := [10689], outs := [16437, 16441], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [10690], outs := [16445, 16449], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [16437, 5633], outs := [10693] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [16445, 5633], outs := [10694] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [10693, 5635], outs := [10695] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [10694, 5635], outs := [10696] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [10695, 5637, 5638, 5639, 5640], outs := [10719], params := [16, 4, 64, 64, 1, 0] }, { rank := 1, op := "OpName.FW_attn_zigzag", ins := [10696, 5637, 5638, 5639, 5640], outs := [10720], params := [16, 4, 64, 64, 1, 0] }, { rank := 0, op := "OpName.FW_reshape", ins := [10719], outs := [10721], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [10720], outs := [10722], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [10721], outs := [10727], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [10722], outs := [10728], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10727, 5644], outs := [10731] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10728, 5644], outs := [10732] }, { rank := 0, op := "OpName.FW_view", ins := [10731], outs := [10741], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [10732], outs := [10742], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [10741], outs := [10745] }, { rank := 1, op := "OpName.FW_float", ins := [10742], outs := [10746] }, { rank := 0, op := "OpName.FW_add", ins := [16441, 10745], outs := [10749] }, { rank := 1, op := "OpName.FW_add", ins := [16449, 10746], outs := [10750] }, { rank := 0, op := "OpName.FW_multiref", ins := [10749], outs := [16453, 16457], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [10750], outs := [16461, 16465], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [16453, 5649], outs := [10753] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [16461, 5649], outs := [10754] }, { rank := 0, op := "OpName.FW_multiref", ins := [10753], outs := [16472, 16476, 16480, 16484, 16488], params := [5] }, { rank := 1, op := "OpName.FW_multiref", ins := [10754], outs := [16495, 16499, 16503, 16507, 16511], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [16472], outs := [10755] }, { rank := 0, op := "OpName.FW_reshape", ins := [16480], outs := [10775], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [16484], outs := [10789], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [16488], outs := [10807], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_float", ins := [16495], outs := [10756] }, { rank := 1, op := "OpName.FW_reshape", ins := [16503], outs := [10776], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [16507], outs := [10790], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [16511], outs := [10808], params := [2048, 1024] }]

theorem pmChunk_37_wf : ∀ n ∈ pmChunk_37, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_37, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_1480_wf
  · rw [h1]
    exact pm_node_1481_wf
  · rw [h2]
    exact pm_node_1482_wf
  · rw [h3]
    exact pm_node_1483_wf
  · rw [h4]
    exact pm_node_1484_wf
  · rw [h5]
    exact pm_node_1485_wf
  · rw [h6]
    exact pm_node_1486_wf
  · rw [h7]
    exact pm_node_1487_wf
  · rw [h8]
    exact pm_node_1488_wf
  · rw [h9]
    exact pm_node_1489_wf
  · rw [h10]
    exact pm_node_1490_wf
  · rw [h11]
    exact pm_node_1491_wf
  · rw [h12]
    exact pm_node_1492_wf
  · rw [h13]
    exact pm_node_1493_wf
  · rw [h14]
    exact pm_node_1494_wf
  · rw [h15]
    exact pm_node_1495_wf
  · rw [h16]
    exact pm_node_1496_wf
  · rw [h17]
    exact pm_node_1497_wf
  · rw [h18]
    exact pm_node_1498_wf
  · rw [h19]
    exact pm_node_1499_wf
  · rw [h20]
    exact pm_node_1500_wf
  · rw [h21]
    exact pm_node_1501_wf
  · rw [h22]
    exact pm_node_1502_wf
  · rw [h23]
    exact pm_node_1503_wf
  · rw [h24]
    exact pm_node_1504_wf
  · rw [h25]
    exact pm_node_1505_wf
  · rw [h26]
    exact pm_node_1506_wf
  · rw [h27]
    exact pm_node_1507_wf
  · rw [h28]
    exact pm_node_1508_wf
  · rw [h29]
    exact pm_node_1509_wf
  · rw [h30]
    exact pm_node_1510_wf
  · rw [h31]
    exact pm_node_1511_wf
  · rw [h32]
    exact pm_node_1512_wf
  · rw [h33]
    exact pm_node_1513_wf
  · rw [h34]
    exact pm_node_1514_wf
  · rw [h35]
    exact pm_node_1515_wf
  · rw [h36]
    exact pm_node_1516_wf
  · rw [h37]
    exact pm_node_1517_wf
  · rw [h38]
    exact pm_node_1518_wf
  · rw [h39]
    exact pm_node_1519_wf

def pmChunk_38 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_norm_linear", ins := [10755, 5652], outs := [10761] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10775, 5661], outs := [10779] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10789, 5666], outs := [10793] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10807, 5670], outs := [10811] }, { rank := 1, op := "OpName.FW_norm_linear", ins := [10756, 5652], outs := [10762] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10776, 5661], outs := [10780] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10790, 5666], outs := [10794] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10808, 5670], outs := [10812] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [10761], outs := [10763, 10765, 10767], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [10779], outs := [10785], params := [2048, 1] }, { rank := 0, op := "OpName.FW_view", ins := [10793], outs := [10803], params := [2048, 512] }, { rank := 0, op := "OpName.FW_view", ins := [10811], outs := [10821], params := [2048, 512] }, { rank := 1, op := "OpName.FW_topk_routing", ins := [10762], outs := [10764, 10766, 10768], params := [8, 1] }, { rank := 1, op := "OpName.FW_view", ins := [10780], outs := [10786], params := [2048, 1] }, { rank := 1, op := "OpName.FW_view", ins := [10794], outs := [10804], params := [2048, 512] }, { rank := 1, op := "OpName.FW_view", ins := [10812], outs := [10822], params := [2048, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16476, 10763, 10765, 10769, 10771], outs := [10773], params := [64, 0, 32, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [10785], outs := [10787] }, { rank := 0, op := "OpName.FW_swiglu", ins := [10803, 10821], outs := [10825] }, { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16499, 10764, 10766, 10770, 10772], outs := [10774], params := [64, 32, 64, 8] }, { rank := 1, op := "OpName.FW_sigmoid", ins := [10786], outs := [10788] }, { rank := 1, op := "OpName.FW_swiglu", ins := [10804, 10822], outs := [10826] }, { rank := 0, op := "OpName.FW_reshape", ins := [10825], outs := [10827], params := [2048, 512] }, { rank := 1, op := "OpName.FW_reshape", ins := [10826], outs := [10828], params := [2048, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10827, 5675], outs := [10833] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10828, 5675], outs := [10834] }, { rank := 0, op := "OpName.FW_view", ins := [10833], outs := [10843], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [10834], outs := [10844], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [10787, 10843], outs := [10847] }, { rank := 1, op := "OpName.FW_mul", ins := [10788, 10844], outs := [10848] }, { rank := 0, op := "OpName.FW_add", ins := [10773, 10847], outs := [10851] }, { rank := 1, op := "OpName.FW_add", ins := [10774, 10848], outs := [10852] }, { rank := 0, op := "OpName.FW_float", ins := [10851], outs := [10857] }, { rank := 1, op := "OpName.FW_float", ins := [10852], outs := [10858] }, { rank := 0, op := "OpName.FW_add", ins := [16457, 10857], outs := [10861] }, { rank := 1, op := "OpName.FW_add", ins := [16465, 10858], outs := [10862] }, { rank := 0, op := "OpName.FW_multiref", ins := [10861], outs := [16515, 16519], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [10862], outs := [16523, 16527], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [16515, 5682], outs := [10865] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [16523, 5682], outs := [10866] }]

theorem pmChunk_38_wf : ∀ n ∈ pmChunk_38, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_38, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_1520_wf
  · rw [h1]
    exact pm_node_1521_wf
  · rw [h2]
    exact pm_node_1522_wf
  · rw [h3]
    exact pm_node_1523_wf
  · rw [h4]
    exact pm_node_1524_wf
  · rw [h5]
    exact pm_node_1525_wf
  · rw [h6]
    exact pm_node_1526_wf
  · rw [h7]
    exact pm_node_1527_wf
  · rw [h8]
    exact pm_node_1528_wf
  · rw [h9]
    exact pm_node_1529_wf
  · rw [h10]
    exact pm_node_1530_wf
  · rw [h11]
    exact pm_node_1531_wf
  · rw [h12]
    exact pm_node_1532_wf
  · rw [h13]
    exact pm_node_1533_wf
  · rw [h14]
    exact pm_node_1534_wf
  · rw [h15]
    exact pm_node_1535_wf
  · rw [h16]
    exact pm_node_1536_wf
  · rw [h17]
    exact pm_node_1537_wf
  · rw [h18]
    exact pm_node_1538_wf
  · rw [h19]
    exact pm_node_1539_wf
  · rw [h20]
    exact pm_node_1540_wf
  · rw [h21]
    exact pm_node_1541_wf
  · rw [h22]
    exact pm_node_1542_wf
  · rw [h23]
    exact pm_node_1543_wf
  · rw [h24]
    exact pm_node_1544_wf
  · rw [h25]
    exact pm_node_1545_wf
  · rw [h26]
    exact pm_node_1546_wf
  · rw [h27]
    exact pm_node_1547_wf
  · rw [h28]
    exact pm_node_1548_wf
  · rw [h29]
    exact pm_node_1549_wf
  · rw [h30]
    exact pm_node_1550_wf
  · rw [h31]
    exact pm_node_1551_wf
  · rw [h32]
    exact pm_node_1552_wf
  · rw [h33]
    exact pm_node_1553_wf
  · rw [h34]
    exact pm_node_1554_wf
  · rw [h35]
    exact pm_node_1555_wf
  · rw [h36]
    exact pm_node_1556_wf
  · rw [h37]
    exact pm_node_1557_wf
  · rw [h38]
    exact pm_node_1558_wf
  · rw [h39]
    exact pm_node_1559_wf

def pmChunk_39 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [10865, 5684], outs := [10867] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [10866, 5684], outs := [10868] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [10867, 5686, 5687, 5688, 5689], outs := [10891], params := [16, 4, 64, 64, 1, 0] }, { rank := 1, op := "OpName.FW_attn_zigzag", ins := [10868, 5686, 5687, 5688, 5689], outs := [10892], params := [16, 4, 64, 64, 1, 0] }, { rank := 0, op := "OpName.FW_reshape", ins := [10891], outs := [10893], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [10892], outs := [10894], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [10893], outs := [10899], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [10894], outs := [10900], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10899, 5693], outs := [10903] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10900, 5693], outs := [10904] }, { rank := 0, op := "OpName.FW_view", ins := [10903], outs := [10913], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [10904], outs := [10914], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [10913], outs := [10917] }, { rank := 1, op := "OpName.FW_float", ins := [10914], outs := [10918] }, { rank := 0, op := "OpName.FW_add", ins := [16519, 10917], outs := [10921] }, { rank := 1, op := "OpName.FW_add", ins := [16527, 10918], outs := [10922] }, { rank := 0, op := "OpName.FW_multiref", ins := [10921], outs := [16531, 16535], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [10922], outs := [16539, 16543], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [16531, 5698], outs := [10925] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [16539, 5698], outs := [10926] }, { rank := 0, op := "OpName.FW_multiref", ins := [10925], outs := [16550, 16554, 16558, 16562, 16566], params := [5] }, { rank := 1, op := "OpName.FW_multiref", ins := [10926], outs := [16573, 16577, 16581, 16585, 16589], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [16550], outs := [10927] }, { rank := 0, op := "OpName.FW_reshape", ins := [16558], outs := [10947], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [16562], outs := [10961], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [16566], outs := [10979], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_float", ins := [16573], outs := [10928] }, { rank := 1, op := "OpName.FW_reshape", ins := [16581], outs := [10948], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [16585], outs := [10962], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [16589], outs := [10980], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [10927, 5701], outs := [10933] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10947, 5710], outs := [10951] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10961, 5715], outs := [10965] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10979, 5719], outs := [10983] }, { rank := 1, op := "OpName.FW_norm_linear", ins := [10928, 5701], outs := [10934] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10948, 5710], outs := [10952] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10962, 5715], outs := [10966] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10980, 5719], outs := [10984] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [10933], outs := [10935, 10937, 10939], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [10951], outs := [10957], params := [2048, 1] }]

theorem pmChunk_39_wf : ∀ n ∈ pmChunk_39, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_39, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_1560_wf
  · rw [h1]
    exact pm_node_1561_wf
  · rw [h2]
    exact pm_node_1562_wf
  · rw [h3]
    exact pm_node_1563_wf
  · rw [h4]
    exact pm_node_1564_wf
  · rw [h5]
    exact pm_node_1565_wf
  · rw [h6]
    exact pm_node_1566_wf
  · rw [h7]
    exact pm_node_1567_wf
  · rw [h8]
    exact pm_node_1568_wf
  · rw [h9]
    exact pm_node_1569_wf
  · rw [h10]
    exact pm_node_1570_wf
  · rw [h11]
    exact pm_node_1571_wf
  · rw [h12]
    exact pm_node_1572_wf
  · rw [h13]
    exact pm_node_1573_wf
  · rw [h14]
    exact pm_node_1574_wf
  · rw [h15]
    exact pm_node_1575_wf
  · rw [h16]
    exact pm_node_1576_wf
  · rw [h17]
    exact pm_node_1577_wf
  · rw [h18]
    exact pm_node_1578_wf
  · rw [h19]
    exact pm_node_1579_wf
  · rw [h20]
    exact pm_node_1580_wf
  · rw [h21]
    exact pm_node_1581_wf
  · rw [h22]
    exact pm_node_1582_wf
  · rw [h23]
    exact pm_node_1583_wf
  · rw [h24]
    exact pm_node_1584_wf
  · rw [h25]
    exact pm_node_1585_wf
  · rw [h26]
    exact pm_node_1586_wf
  · rw [h27]
    exact pm_node_1587_wf
  · rw [h28]
    exact pm_node_1588_wf
  · rw [h29]
    exact pm_node_1589_wf
  · rw [h30]
    exact pm_node_1590_wf
  · rw [h31]
    exact pm_node_1591_wf
  · rw [h32]
    exact pm_node_1592_wf
  · rw [h33]
    exact pm_node_1593_wf
  · rw [h34]
    exact pm_node_1594_wf
  · rw [h35]
    exact pm_node_1595_wf
  · rw [h36]
    exact pm_node_1596_wf
  · rw [h37]
    exact pm_node_1597_wf
  · rw [h38]
    exact pm_node_1598_wf
  · rw [h39]
    exact pm_node_1599_wf

def pmChunk_40 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_view", ins := [10965], outs := [10975], params := [2048, 512] }, { rank := 0, op := "OpName.FW_view", ins := [10983], outs := [10993], params := [2048, 512] }, { rank := 1, op := "OpName.FW_topk_routing", ins := [10934], outs := [10936, 10938, 10940], params := [8, 1] }, { rank := 1, op := "OpName.FW_view", ins := [10952], outs := [10958], params := [2048, 1] }, { rank := 1, op := "OpName.FW_view", ins := [10966], outs := [10976], params := [2048, 512] }, { rank := 1, op := "OpName.FW_view", ins := [10984], outs := [10994], params := [2048, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16554, 10935, 10937, 10941, 10943], outs := [10945], params := [64, 0, 32, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [10957], outs := [10959] }, { rank := 0, op := "OpName.FW_swiglu", ins := [10975, 10993], outs := [10997] }, { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16577, 10936, 10938, 10942, 10944], outs := [10946], params := [64, 32, 64, 8] }, { rank := 1, op := "OpName.FW_sigmoid", ins := [10958], outs := [10960] }, { rank := 1, op := "OpName.FW_swiglu", ins := [10976, 10994], outs := [10998] }, { rank := 0, op := "OpName.FW_reshape", ins := [10997], outs := [10999], params := [2048, 512] }, { rank := 1, op := "OpName.FW_reshape", ins := [10998], outs := [11000], params := [2048, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10999, 5724], outs := [11005] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11000, 5724], outs := [11006] }, { rank := 0, op := "OpName.FW_view", ins := [11005], outs := [11015], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [11006], outs := [11016], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [10959, 11015], outs := [11019] }, { rank := 1, op := "OpName.FW_mul", ins := [10960, 11016], outs := [11020] }, { rank := 0, op := "OpName.FW_add", ins := [10945, 11019], outs := [11023] }, { rank := 1, op := "OpName.FW_add", ins := [10946, 11020], outs := [11024] }, { rank := 0, op := "OpName.FW_float", ins := [11023], outs := [11029] }, { rank := 1, op := "OpName.FW_float", ins := [11024], outs := [11030] }, { rank := 0, op := "OpName.FW_add", ins := [16535, 11029], outs := [11033] }, { rank := 1, op := "OpName.FW_add", ins := [16543, 11030], outs := [11034] }, { rank := 0, op := "OpName.FW_multiref", ins := [11033], outs := [16593, 16597], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [11034], outs := [16601, 16605], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [16593, 5731], outs := [11037] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [16601, 5731], outs := [11038] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [11037, 5733], outs := [11039] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [11038, 5733], outs := [11040] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [11039, 5735, 5736, 5737, 5738], outs := [11063], params := [16, 4, 64, 64, 1, 0] }, { rank := 1, op := "OpName.FW_attn_zigzag", ins := [11040, 5735, 5736, 5737, 5738], outs := [11064], params := [16, 4, 64, 64, 1, 0] }, { rank := 0, op := "OpName.FW_reshape", ins := [11063], outs := [11065], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [11064], outs := [11066], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [11065], outs := [11071], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [11066], outs := [11072], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11071, 5742], outs := [11075] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11072, 5742], outs := [11076] }]

theorem pmChunk_40_wf : ∀ n ∈ pmChunk_40, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_40, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_1600_wf
  · rw [h1]
    exact pm_node_1601_wf
  · rw [h2]
    exact pm_node_1602_wf
  · rw [h3]
    exact pm_node_1603_wf
  · rw [h4]
    exact pm_node_1604_wf
  · rw [h5]
    exact pm_node_1605_wf
  · rw [h6]
    exact pm_node_1606_wf
  · rw [h7]
    exact pm_node_1607_wf
  · rw [h8]
    exact pm_node_1608_wf
  · rw [h9]
    exact pm_node_1609_wf
  · rw [h10]
    exact pm_node_1610_wf
  · rw [h11]
    exact pm_node_1611_wf
  · rw [h12]
    exact pm_node_1612_wf
  · rw [h13]
    exact pm_node_1613_wf
  · rw [h14]
    exact pm_node_1614_wf
  · rw [h15]
    exact pm_node_1615_wf
  · rw [h16]
    exact pm_node_1616_wf
  · rw [h17]
    exact pm_node_1617_wf
  · rw [h18]
    exact pm_node_1618_wf
  · rw [h19]
    exact pm_node_1619_wf
  · rw [h20]
    exact pm_node_1620_wf
  · rw [h21]
    exact pm_node_1621_wf
  · rw [h22]
    exact pm_node_1622_wf
  · rw [h23]
    exact pm_node_1623_wf
  · rw [h24]
    exact pm_node_1624_wf
  · rw [h25]
    exact pm_node_1625_wf
  · rw [h26]
    exact pm_node_1626_wf
  · rw [h27]
    exact pm_node_1627_wf
  · rw [h28]
    exact pm_node_1628_wf
  · rw [h29]
    exact pm_node_1629_wf
  · rw [h30]
    exact pm_node_1630_wf
  · rw [h31]
    exact pm_node_1631_wf
  · rw [h32]
    exact pm_node_1632_wf
  · rw [h33]
    exact pm_node_1633_wf
  · rw [h34]
    exact pm_node_1634_wf
  · rw [h35]
    exact pm_node_1635_wf
  · rw [h36]
    exact pm_node_1636_wf
  · rw [h37]
    exact pm_node_1637_wf
  · rw [h38]
    exact pm_node_1638_wf
  · rw [h39]
    exact pm_node_1639_wf

def pmChunk_41 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_view", ins := [11075], outs := [11085], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [11076], outs := [11086], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [11085], outs := [11089] }, { rank := 1, op := "OpName.FW_float", ins := [11086], outs := [11090] }, { rank := 0, op := "OpName.FW_add", ins := [16597, 11089], outs := [11093] }, { rank := 1, op := "OpName.FW_add", ins := [16605, 11090], outs := [11094] }, { rank := 0, op := "OpName.FW_multiref", ins := [11093], outs := [16609, 16613], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [11094], outs := [16617, 16621], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [16609, 5747], outs := [11097] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [16617, 5747], outs := [11098] }, { rank := 0, op := "OpName.FW_multiref", ins := [11097], outs := [16628, 16632, 16636, 16640, 16644], params := [5] }, { rank := 1, op := "OpName.FW_multiref", ins := [11098], outs := [16651, 16655, 16659, 16663, 16667], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [16628], outs := [11099] }, { rank := 0, op := "OpName.FW_reshape", ins := [16636], outs := [11119], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [16640], outs := [11133], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [16644], outs := [11151], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_float", ins := [16651], outs := [11100] }, { rank := 1, op := "OpName.FW_reshape", ins := [16659], outs := [11120], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [16663], outs := [11134], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [16667], outs := [11152], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [11099, 5750], outs := [11105] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11119, 5759], outs := [11123] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11133, 5764], outs := [11137] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11151, 5768], outs := [11155] }, { rank := 1, op := "OpName.FW_norm_linear", ins := [11100, 5750], outs := [11106] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11120, 5759], outs := [11124] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11134, 5764], outs := [11138] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11152, 5768], outs := [11156] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [11105], outs := [11107, 11109, 11111], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [11123], outs := [11129], params := [2048, 1] }, { rank := 0, op := "OpName.FW_view", ins := [11137], outs := [11147], params := [2048, 512] }, { rank := 0, op := "OpName.FW_view", ins := [11155], outs := [11165], params := [2048, 512] }, { rank := 1, op := "OpName.FW_topk_routing", ins := [11106], outs := [11108, 11110, 11112], params := [8, 1] }, { rank := 1, op := "OpName.FW_view", ins := [11124], outs := [11130], params := [2048, 1] }, { rank := 1, op := "OpName.FW_view", ins := [11138], outs := [11148], params := [2048, 512] }, { rank := 1, op := "OpName.FW_view", ins := [11156], outs := [11166], params := [2048, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16632, 11107, 11109, 11113, 11115], outs := [11117], params := [64, 0, 32, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [11129], outs := [11131] }, { rank := 0, op := "OpName.FW_swiglu", ins := [11147, 11165], outs := [11169] }, { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16655, 11108, 11110, 11114, 11116], outs := [11118], params := [64, 32, 64, 8] }]

theorem pmChunk_41_wf : ∀ n ∈ pmChunk_41, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_41, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_1640_wf
  · rw [h1]
    exact pm_node_1641_wf
  · rw [h2]
    exact pm_node_1642_wf
  · rw [h3]
    exact pm_node_1643_wf
  · rw [h4]
    exact pm_node_1644_wf
  · rw [h5]
    exact pm_node_1645_wf
  · rw [h6]
    exact pm_node_1646_wf
  · rw [h7]
    exact pm_node_1647_wf
  · rw [h8]
    exact pm_node_1648_wf
  · rw [h9]
    exact pm_node_1649_wf
  · rw [h10]
    exact pm_node_1650_wf
  · rw [h11]
    exact pm_node_1651_wf
  · rw [h12]
    exact pm_node_1652_wf
  · rw [h13]
    exact pm_node_1653_wf
  · rw [h14]
    exact pm_node_1654_wf
  · rw [h15]
    exact pm_node_1655_wf
  · rw [h16]
    exact pm_node_1656_wf
  · rw [h17]
    exact pm_node_1657_wf
  · rw [h18]
    exact pm_node_1658_wf
  · rw [h19]
    exact pm_node_1659_wf
  · rw [h20]
    exact pm_node_1660_wf
  · rw [h21]
    exact pm_node_1661_wf
  · rw [h22]
    exact pm_node_1662_wf
  · rw [h23]
    exact pm_node_1663_wf
  · rw [h24]
    exact pm_node_1664_wf
  · rw [h25]
    exact pm_node_1665_wf
  · rw [h26]
    exact pm_node_1666_wf
  · rw [h27]
    exact pm_node_1667_wf
  · rw [h28]
    exact pm_node_1668_wf
  · rw [h29]
    exact pm_node_1669_wf
  · rw [h30]
    exact pm_node_1670_wf
  · rw [h31]
    exact pm_node_1671_wf
  · rw [h32]
    exact pm_node_1672_wf
  · rw [h33]
    exact pm_node_1673_wf
  · rw [h34]
    exact pm_node_1674_wf
  · rw [h35]
    exact pm_node_1675_wf
  · rw [h36]
    exact pm_node_1676_wf
  · rw [h37]
    exact pm_node_1677_wf
  · rw [h38]
    exact pm_node_1678_wf
  · rw [h39]
    exact pm_node_1679_wf

def pmChunk_42 : List NodeDecl :=
  [{ rank := 1, op := "OpName.FW_sigmoid", ins := [11130], outs := [11132] }, { rank := 1, op := "OpName.FW_swiglu", ins := [11148, 11166], outs := [11170] }, { rank := 0, op := "OpName.FW_reshape", ins := [11169], outs := [11171], params := [2048, 512] }, { rank := 1, op := "OpName.FW_reshape", ins := [11170], outs := [11172], params := [2048, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11171, 5773], outs := [11177] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11172, 5773], outs := [11178] }, { rank := 0, op := "OpName.FW_view", ins := [11177], outs := [11187], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [11178], outs := [11188], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [11131, 11187], outs := [11191] }, { rank := 1, op := "OpName.FW_mul", ins := [11132, 11188], outs := [11192] }, { rank := 0, op := "OpName.FW_add", ins := [11117, 11191], outs := [11195] }, { rank := 1, op := "OpName.FW_add", ins := [11118, 11192], outs := [11196] }, { rank := 0, op := "OpName.FW_float", ins := [11195], outs := [11201] }, { rank := 1, op := "OpName.FW_float", ins := [11196], outs := [11202] }, { rank := 0, op := "OpName.FW_add", ins := [16613, 11201], outs := [11205] }, { rank := 1, op := "OpName.FW_add", ins := [16621, 11202], outs := [11206] }, { rank := 0, op := "OpName.FW_multiref", ins := [11205], outs := [16671, 16675], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [11206], outs := [16679, 16683], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [16671, 5780], outs := [11209] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [16679, 5780], outs := [11210] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [11209, 5782], outs := [11211] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [11210, 5782], outs := [11212] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [11211, 5784, 5785, 5786, 5787], outs := [11235], params := [16, 4, 64, 64, 1, 0] }, { rank := 1, op := "OpName.FW_attn_zigzag", ins := [11212, 5784, 5785, 5786, 5787], outs := [11236], params := [16, 4, 64, 64, 1, 0] }, { rank := 0, op := "OpName.FW_reshape", ins := [11235], outs := [11237], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [11236], outs := [11238], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [11237], outs := [11243], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [11238], outs := [11244], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11243, 5791], outs := [11247] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11244, 5791], outs := [11248] }, { rank := 0, op := "OpName.FW_view", ins := [11247], outs := [11257], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [11248], outs := [11258], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [11257], outs := [11261] }, { rank := 1, op := "OpName.FW_float", ins := [11258], outs := [11262] }, { rank := 0, op := "OpName.FW_add", ins := [16675, 11261], outs := [11265] }, { rank := 1, op := "OpName.FW_add", ins := [16683, 11262], outs := [11266] }, { rank := 0, op := "OpName.FW_multiref", ins := [11265], outs := [16687, 16691], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [11266], outs := [16695, 16699], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [16687, 5796], outs := [11269] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [16695, 5796], outs := [11270] }]

theorem pmChunk_42_wf : ∀ n ∈ pmChunk_42, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_42, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_1680_wf
  · rw [h1]
    exact pm_node_1681_wf
  · rw [h2]
    exact pm_node_1682_wf
  · rw [h3]
    exact pm_node_1683_wf
  · rw [h4]
    exact pm_node_1684_wf
  · rw [h5]
    exact pm_node_1685_wf
  · rw [h6]
    exact pm_node_1686_wf
  · rw [h7]
    exact pm_node_1687_wf
  · rw [h8]
    exact pm_node_1688_wf
  · rw [h9]
    exact pm_node_1689_wf
  · rw [h10]
    exact pm_node_1690_wf
  · rw [h11]
    exact pm_node_1691_wf
  · rw [h12]
    exact pm_node_1692_wf
  · rw [h13]
    exact pm_node_1693_wf
  · rw [h14]
    exact pm_node_1694_wf
  · rw [h15]
    exact pm_node_1695_wf
  · rw [h16]
    exact pm_node_1696_wf
  · rw [h17]
    exact pm_node_1697_wf
  · rw [h18]
    exact pm_node_1698_wf
  · rw [h19]
    exact pm_node_1699_wf
  · rw [h20]
    exact pm_node_1700_wf
  · rw [h21]
    exact pm_node_1701_wf
  · rw [h22]
    exact pm_node_1702_wf
  · rw [h23]
    exact pm_node_1703_wf
  · rw [h24]
    exact pm_node_1704_wf
  · rw [h25]
    exact pm_node_1705_wf
  · rw [h26]
    exact pm_node_1706_wf
  · rw [h27]
    exact pm_node_1707_wf
  · rw [h28]
    exact pm_node_1708_wf
  · rw [h29]
    exact pm_node_1709_wf
  · rw [h30]
    exact pm_node_1710_wf
  · rw [h31]
    exact pm_node_1711_wf
  · rw [h32]
    exact pm_node_1712_wf
  · rw [h33]
    exact pm_node_1713_wf
  · rw [h34]
    exact pm_node_1714_wf
  · rw [h35]
    exact pm_node_1715_wf
  · rw [h36]
    exact pm_node_1716_wf
  · rw [h37]
    exact pm_node_1717_wf
  · rw [h38]
    exact pm_node_1718_wf
  · rw [h39]
    exact pm_node_1719_wf

def pmChunk_43 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_multiref", ins := [11269], outs := [16706, 16710, 16714, 16718, 16722], params := [5] }, { rank := 1, op := "OpName.FW_multiref", ins := [11270], outs := [16729, 16733, 16737, 16741, 16745], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [16706], outs := [11271] }, { rank := 0, op := "OpName.FW_reshape", ins := [16714], outs := [11291], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [16718], outs := [11305], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [16722], outs := [11323], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_float", ins := [16729], outs := [11272] }, { rank := 1, op := "OpName.FW_reshape", ins := [16737], outs := [11292], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [16741], outs := [11306], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [16745], outs := [11324], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [11271, 5799], outs := [11277] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11291, 5808], outs := [11295] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11305, 5813], outs := [11309] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11323, 5817], outs := [11327] }, { rank := 1, op := "OpName.FW_norm_linear", ins := [11272, 5799], outs := [11278] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11292, 5808], outs := [11296] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11306, 5813], outs := [11310] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11324, 5817], outs := [11328] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [11277], outs := [11279, 11281, 11283], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [11295], outs := [11301], params := [2048, 1] }, { rank := 0, op := "OpName.FW_view", ins := [11309], outs := [11319], params := [2048, 512] }, { rank := 0, op := "OpName.FW_view", ins := [11327], outs := [11337], params := [2048, 512] }, { rank := 1, op := "OpName.FW_topk_routing", ins := [11278], outs := [11280, 11282, 11284], params := [8, 1] }, { rank := 1, op := "OpName.FW_view", ins := [11296], outs := [11302], params := [2048, 1] }, { rank := 1, op := "OpName.FW_view", ins := [11310], outs := [11320], params := [2048, 512] }, { rank := 1, op := "OpName.FW_view", ins := [11328], outs := [11338], params := [2048, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16710, 11279, 11281, 11285, 11287], outs := [11289], params := [64, 0, 32, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [11301], outs := [11303] }, { rank := 0, op := "OpName.FW_swiglu", ins := [11319, 11337], outs := [11341] }, { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16733, 11280, 11282, 11286, 11288], outs := [11290], params := [64, 32, 64, 8] }, { rank := 1, op := "OpName.FW_sigmoid", ins := [11302], outs := [11304] }, { rank := 1, op := "OpName.FW_swiglu", ins := [11320, 11338], outs := [11342] }, { rank := 0, op := "OpName.FW_reshape", ins := [11341], outs := [11343], params := [2048, 512] }, { rank := 1, op := "OpName.FW_reshape", ins := [11342], outs := [11344], params := [2048, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11343, 5822], outs := [11349] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11344, 5822], outs := [11350] }, { rank := 0, op := "OpName.FW_view", ins := [11349], outs := [11359], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [11350], outs := [11360], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [11303, 11359], outs := [11363] }, { rank := 1, op := "OpName.FW_mul", ins := [11304, 11360], outs := [11364] }]

theorem pmChunk_43_wf : ∀ n ∈ pmChunk_43, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_43, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_1720_wf
  · rw [h1]
    exact pm_node_1721_wf
  · rw [h2]
    exact pm_node_1722_wf
  · rw [h3]
    exact pm_node_1723_wf
  · rw [h4]
    exact pm_node_1724_wf
  · rw [h5]
    exact pm_node_1725_wf
  · rw [h6]
    exact pm_node_1726_wf
  · rw [h7]
    exact pm_node_1727_wf
  · rw [h8]
    exact pm_node_1728_wf
  · rw [h9]
    exact pm_node_1729_wf
  · rw [h10]
    exact pm_node_1730_wf
  · rw [h11]
    exact pm_node_1731_wf
  · rw [h12]
    exact pm_node_1732_wf
  · rw [h13]
    exact pm_node_1733_wf
  · rw [h14]
    exact pm_node_1734_wf
  · rw [h15]
    exact pm_node_1735_wf
  · rw [h16]
    exact pm_node_1736_wf
  · rw [h17]
    exact pm_node_1737_wf
  · rw [h18]
    exact pm_node_1738_wf
  · rw [h19]
    exact pm_node_1739_wf
  · rw [h20]
    exact pm_node_1740_wf
  · rw [h21]
    exact pm_node_1741_wf
  · rw [h22]
    exact pm_node_1742_wf
  · rw [h23]
    exact pm_node_1743_wf
  · rw [h24]
    exact pm_node_1744_wf
  · rw [h25]
    exact pm_node_1745_wf
  · rw [h26]
    exact pm_node_1746_wf
  · rw [h27]
    exact pm_node_1747_wf
  · rw [h28]
    exact pm_node_1748_wf
  · rw [h29]
    exact pm_node_1749_wf
  · rw [h30]
    exact pm_node_1750_wf
  · rw [h31]
    exact pm_node_1751_wf
  · rw [h32]
    exact pm_node_1752_wf
  · rw [h33]
    exact pm_node_1753_wf
  · rw [h34]
    exact pm_node_1754_wf
  · rw [h35]
    exact pm_node_1755_wf
  · rw [h36]
    exact pm_node_1756_wf
  · rw [h37]
    exact pm_node_1757_wf
  · rw [h38]
    exact pm_node_1758_wf
  · rw [h39]
    exact pm_node_1759_wf

def pmChunk_44 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_add", ins := [11289, 11363], outs := [11367] }, { rank := 1, op := "OpName.FW_add", ins := [11290, 11364], outs := [11368] }, { rank := 0, op := "OpName.FW_float", ins := [11367], outs := [11373] }, { rank := 1, op := "OpName.FW_float", ins := [11368], outs := [11374] }, { rank := 0, op := "OpName.FW_add", ins := [16691, 11373], outs := [11377] }, { rank := 1, op := "OpName.FW_add", ins := [16699, 11374], outs := [11378] }, { rank := 0, op := "OpName.FW_multiref", ins := [11377], outs := [16749, 16753], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [11378], outs := [16757, 16761], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [16749, 5829], outs := [11381] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [16757, 5829], outs := [11382] }, { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [11381, 5831], outs := [11383] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [11382, 5831], outs := [11384] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [11383, 5833, 5834, 5835, 5836], outs := [11407], params := [16, 4, 64, 64, 1, 0] }, { rank := 1, op := "OpName.FW_attn_zigzag", ins := [11384, 5833, 5834, 5835, 5836], outs := [11408], params := [16, 4, 64, 64, 1, 0] }, { rank := 0, op := "OpName.FW_reshape", ins := [11407], outs := [11409], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [11408], outs := [11410], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [11409], outs := [11415], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [11410], outs := [11416], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11415, 5840], outs := [11419] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11416, 5840], outs := [11420] }, { rank := 0, op := "OpName.FW_view", ins := [11419], outs := [11429], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [11420], outs := [11430], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [11429], outs := [11433] }, { rank := 1, op := "OpName.FW_float", ins := [11430], outs := [11434] }, { rank := 0, op := "OpName.FW_add", ins := [16753, 11433], outs := [11437] }, { rank := 1, op := "OpName.FW_add", ins := [16761, 11434], outs := [11438] }, { rank := 0, op := "OpName.FW_multiref", ins := [11437], outs := [16765, 16769], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [11438], outs := [16773, 16777], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [16765, 5845], outs := [11441] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [16773, 5845], outs := [11442] }, { rank := 0, op := "OpName.FW_multiref", ins := [11441], outs := [16784, 16788, 16792, 16796, 16800], params := [5] }, { rank := 1, op := "OpName.FW_multiref", ins := [11442], outs := [16807, 16811, 16815, 16819, 16823], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [16784], outs := [11443] }, { rank := 0, op := "OpName.FW_reshape", ins := [16792], outs := [11463], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [16796], outs := [11477], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [16800], outs := [11495], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_float", ins := [16807], outs := [11444] }, { rank := 1, op := "OpName.FW_reshape", ins := [16815], outs := [11464], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [16819], outs := [11478], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [16823], outs := [11496], params := [2048, 1024] }]

theorem pmChunk_44_wf : ∀ n ∈ pmChunk_44, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_44, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_1760_wf
  · rw [h1]
    exact pm_node_1761_wf
  · rw [h2]
    exact pm_node_1762_wf
  · rw [h3]
    exact pm_node_1763_wf
  · rw [h4]
    exact pm_node_1764_wf
  · rw [h5]
    exact pm_node_1765_wf
  · rw [h6]
    exact pm_node_1766_wf
  · rw [h7]
    exact pm_node_1767_wf
  · rw [h8]
    exact pm_node_1768_wf
  · rw [h9]
    exact pm_node_1769_wf
  · rw [h10]
    exact pm_node_1770_wf
  · rw [h11]
    exact pm_node_1771_wf
  · rw [h12]
    exact pm_node_1772_wf
  · rw [h13]
    exact pm_node_1773_wf
  · rw [h14]
    exact pm_node_1774_wf
  · rw [h15]
    exact pm_node_1775_wf
  · rw [h16]
    exact pm_node_1776_wf
  · rw [h17]
    exact pm_node_1777_wf
  · rw [h18]
    exact pm_node_1778_wf
  · rw [h19]
    exact pm_node_1779_wf
  · rw [h20]
    exact pm_node_1780_wf
  · rw [h21]
    exact pm_node_1781_wf
  · rw [h22]
    exact pm_node_1782_wf
  · rw [h23]
    exact pm_node_1783_wf
  · rw [h24]
    exact pm_node_1784_wf
  · rw [h25]
    exact pm_node_1785_wf
  · rw [h26]
    exact pm_node_1786_wf
  · rw [h27]
    exact pm_node_1787_wf
  · rw [h28]
    exact pm_node_1788_wf
  · rw [h29]
    exact pm_node_1789_wf
  · rw [h30]
    exact pm_node_1790_wf
  · rw [h31]
    exact pm_node_1791_wf
  · rw [h32]
    exact pm_node_1792_wf
  · rw [h33]
    exact pm_node_1793_wf
  · rw [h34]
    exact pm_node_1794_wf
  · rw [h35]
    exact pm_node_1795_wf
  · rw [h36]
    exact pm_node_1796_wf
  · rw [h37]
    exact pm_node_1797_wf
  · rw [h38]
    exact pm_node_1798_wf
  · rw [h39]
    exact pm_node_1799_wf

def pmChunk_45 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_norm_linear", ins := [11443, 5848], outs := [11449] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11463, 5857], outs := [11467] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11477, 5862], outs := [11481] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11495, 5866], outs := [11499] }, { rank := 1, op := "OpName.FW_norm_linear", ins := [11444, 5848], outs := [11450] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11464, 5857], outs := [11468] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11478, 5862], outs := [11482] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11496, 5866], outs := [11500] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [11449], outs := [11451, 11453, 11455], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [11467], outs := [11473], params := [2048, 1] }, { rank := 0, op := "OpName.FW_view", ins := [11481], outs := [11491], params := [2048, 512] }, { rank := 0, op := "OpName.FW_view", ins := [11499], outs := [11509], params := [2048, 512] }, { rank := 1, op := "OpName.FW_topk_routing", ins := [11450], outs := [11452, 11454, 11456], params := [8, 1] }, { rank := 1, op := "OpName.FW_view", ins := [11468], outs := [11474], params := [2048, 1] }, { rank := 1, op := "OpName.FW_view", ins := [11482], outs := [11492], params := [2048, 512] }, { rank := 1, op := "OpName.FW_view", ins := [11500], outs := [11510], params := [2048, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16788, 11451, 11453, 11457, 11459], outs := [11461], params := [64, 0, 32, 8] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [11473], outs := [11475] }, { rank := 0, op := "OpName.FW_swiglu", ins := [11491, 11509], outs := [11513] }, { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16811, 11452, 11454, 11458, 11460], outs := [11462], params := [64, 32, 64, 8] }, { rank := 1, op := "OpName.FW_sigmoid", ins := [11474], outs := [11476] }, { rank := 1, op := "OpName.FW_swiglu", ins := [11492, 11510], outs := [11514] }, { rank := 0, op := "OpName.FW_reshape", ins := [11513], outs := [11515], params := [2048, 512] }, { rank := 1, op := "OpName.FW_reshape", ins := [11514], outs := [11516], params := [2048, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11515, 5871], outs := [11521] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11516, 5871], outs := [11522] }, { rank := 0, op := "OpName.FW_view", ins := [11521], outs := [11531], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [11522], outs := [11532], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [11475, 11531], outs := [11535] }, { rank := 1, op := "OpName.FW_mul", ins := [11476, 11532], outs := [11536] }, { rank := 0, op := "OpName.FW_add", ins := [11461, 11535], outs := [11539] }, { rank := 1, op := "OpName.FW_add", ins := [11462, 11536], outs := [11540] }, { rank := 0, op := "OpName.FW_float", ins := [11539], outs := [11545] }, { rank := 1, op := "OpName.FW_float", ins := [11540], outs := [11546] }, { rank := 0, op := "OpName.FW_add", ins := [16769, 11545], outs := [11549] }, { rank := 1, op := "OpName.FW_add", ins := [16777, 11546], outs := [11550] }, { rank := 0, op := "OpName.FW_multiref", ins := [11549], outs := [16827, 16831], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [11550], outs := [16835, 16839], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [16827, 5878], outs := [11553] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [16835, 5878], outs := [11554] }]

theorem pmChunk_45_wf : ∀ n ∈ pmChunk_45, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_45, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_1800_wf
  · rw [h1]
    exact pm_node_1801_wf
  · rw [h2]
    exact pm_node_1802_wf
  · rw [h3]
    exact pm_node_1803_wf
  · rw [h4]
    exact pm_node_1804_wf
  · rw [h5]
    exact pm_node_1805_wf
  · rw [h6]
    exact pm_node_1806_wf
  · rw [h7]
    exact pm_node_1807_wf
  · rw [h8]
    exact pm_node_1808_wf
  · rw [h9]
    exact pm_node_1809_wf
  · rw [h10]
    exact pm_node_1810_wf
  · rw [h11]
    exact pm_node_1811_wf
  · rw [h12]
    exact pm_node_1812_wf
  · rw [h13]
    exact pm_node_1813_wf
  · rw [h14]
    exact pm_node_1814_wf
  · rw [h15]
    exact pm_node_1815_wf
  · rw [h16]
    exact pm_node_1816_wf
  · rw [h17]
    exact pm_node_1817_wf
  · rw [h18]
    exact pm_node_1818_wf
  · rw [h19]
    exact pm_node_1819_wf
  · rw [h20]
    exact pm_node_1820_wf
  · rw [h21]
    exact pm_node_1821_wf
  · rw [h22]
    exact pm_node_1822_wf
  · rw [h23]
    exact pm_node_1823_wf
  · rw [h24]
    exact pm_node_1824_wf
  · rw [h25]
    exact pm_node_1825_wf
  · rw [h26]
    exact pm_node_1826_wf
  · rw [h27]
    exact pm_node_1827_wf
  · rw [h28]
    exact pm_node_1828_wf
  · rw [h29]
    exact pm_node_1829_wf
  · rw [h30]
    exact pm_node_1830_wf
  · rw [h31]
    exact pm_node_1831_wf
  · rw [h32]
    exact pm_node_1832_wf
  · rw [h33]
    exact pm_node_1833_wf
  · rw [h34]
    exact pm_node_1834_wf
  · rw [h35]
    exact pm_node_1835_wf
  · rw [h36]
    exact pm_node_1836_wf
  · rw [h37]
    exact pm_node_1837_wf
  · rw [h38]
    exact pm_node_1838_wf
  · rw [h39]
    exact pm_node_1839_wf

def pmChunk_46 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [11553, 5880], outs := [11555] }, { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [11554, 5880], outs := [11556] }, { rank := 0, op := "OpName.FW_attn_zigzag", ins := [11555, 5882, 5883, 5884, 5885], outs := [11579], params := [16, 4, 64, 64, 1, 0] }, { rank := 1, op := "OpName.FW_attn_zigzag", ins := [11556, 5882, 5883, 5884, 5885], outs := [11580], params := [16, 4, 64, 64, 1, 0] }, { rank := 0, op := "OpName.FW_reshape", ins := [11579], outs := [11581], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [11580], outs := [11582], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [11581], outs := [11587], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [11582], outs := [11588], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11587, 5889], outs := [11591] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11588, 5889], outs := [11592] }, { rank := 0, op := "OpName.FW_view", ins := [11591], outs := [11601], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [11592], outs := [11602], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_float", ins := [11601], outs := [11605] }, { rank := 1, op := "OpName.FW_float", ins := [11602], outs := [11606] }, { rank := 0, op := "OpName.FW_add", ins := [16831, 11605], outs := [11609] }, { rank := 1, op := "OpName.FW_add", ins := [16839, 11606], outs := [11610] }, { rank := 0, op := "OpName.FW_multiref", ins := [11609], outs := [16843, 16847], params := [2] }, { rank := 1, op := "OpName.FW_multiref", ins := [11610], outs := [16851, 16855], params := [2] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [16843, 5894], outs := [11613] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [16851, 5894], outs := [11614] }, { rank := 0, op := "OpName.FW_multiref", ins := [11613], outs := [16862, 16866, 16870, 16874, 16878], params := [5] }, { rank := 1, op := "OpName.FW_multiref", ins := [11614], outs := [16885, 16889, 16893, 16897, 16901], params := [5] }, { rank := 0, op := "OpName.FW_float", ins := [16862], outs := [11615] }, { rank := 0, op := "OpName.FW_reshape", ins := [16870], outs := [11635], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [16874], outs := [11649], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_reshape", ins := [16878], outs := [11667], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_float", ins := [16885], outs := [11616] }, { rank := 1, op := "OpName.FW_reshape", ins := [16893], outs := [11636], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [16897], outs := [11650], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_reshape", ins := [16901], outs := [11668], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_norm_linear", ins := [11615, 5897], outs := [11621] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11635, 5906], outs := [11639] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11649, 5911], outs := [11653] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11667, 5915], outs := [11671] }, { rank := 1, op := "OpName.FW_norm_linear", ins := [11616, 5897], outs := [11622] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11636, 5906], outs := [11640] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11650, 5911], outs := [11654] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11668, 5915], outs := [11672] }, { rank := 0, op := "OpName.FW_topk_routing", ins := [11621], outs := [11623, 11625, 11627], params := [8, 1] }, { rank := 0, op := "OpName.FW_view", ins := [11639], outs := [11645], params := [2048, 1] }]

theorem pmChunk_46_wf : ∀ n ∈ pmChunk_46, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_46, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_1840_wf
  · rw [h1]
    exact pm_node_1841_wf
  · rw [h2]
    exact pm_node_1842_wf
  · rw [h3]
    exact pm_node_1843_wf
  · rw [h4]
    exact pm_node_1844_wf
  · rw [h5]
    exact pm_node_1845_wf
  · rw [h6]
    exact pm_node_1846_wf
  · rw [h7]
    exact pm_node_1847_wf
  · rw [h8]
    exact pm_node_1848_wf
  · rw [h9]
    exact pm_node_1849_wf
  · rw [h10]
    exact pm_node_1850_wf
  · rw [h11]
    exact pm_node_1851_wf
  · rw [h12]
    exact pm_node_1852_wf
  · rw [h13]
    exact pm_node_1853_wf
  · rw [h14]
    exact pm_node_1854_wf
  · rw [h15]
    exact pm_node_1855_wf
  · rw [h16]
    exact pm_node_1856_wf
  · rw [h17]
    exact pm_node_1857_wf
  · rw [h18]
    exact pm_node_1858_wf
  · rw [h19]
    exact pm_node_1859_wf
  · rw [h20]
    exact pm_node_1860_wf
  · rw [h21]
    exact pm_node_1861_wf
  · rw [h22]
    exact pm_node_1862_wf
  · rw [h23]
    exact pm_node_1863_wf
  · rw [h24]
    exact pm_node_1864_wf
  · rw [h25]
    exact pm_node_1865_wf
  · rw [h26]
    exact pm_node_1866_wf
  · rw [h27]
    exact pm_node_1867_wf
  · rw [h28]
    exact pm_node_1868_wf
  · rw [h29]
    exact pm_node_1869_wf
  · rw [h30]
    exact pm_node_1870_wf
  · rw [h31]
    exact pm_node_1871_wf
  · rw [h32]
    exact pm_node_1872_wf
  · rw [h33]
    exact pm_node_1873_wf
  · rw [h34]
    exact pm_node_1874_wf
  · rw [h35]
    exact pm_node_1875_wf
  · rw [h36]
    exact pm_node_1876_wf
  · rw [h37]
    exact pm_node_1877_wf
  · rw [h38]
    exact pm_node_1878_wf
  · rw [h39]
    exact pm_node_1879_wf

def pmChunk_47 : List NodeDecl :=
  [{ rank := 0, op := "OpName.FW_view", ins := [11653], outs := [11663], params := [2048, 512] }, { rank := 0, op := "OpName.FW_view", ins := [11671], outs := [11681], params := [2048, 512] }, { rank := 1, op := "OpName.FW_topk_routing", ins := [11622], outs := [11624, 11626, 11628], params := [8, 1] }, { rank := 1, op := "OpName.FW_view", ins := [11640], outs := [11646], params := [2048, 1] }, { rank := 1, op := "OpName.FW_view", ins := [11654], outs := [11664], params := [2048, 512] }, { rank := 1, op := "OpName.FW_view", ins := [11672], outs := [11682], params := [2048, 512] }, { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16866, 11623, 11625, 11629, 11631], outs := [11633], params := [64, 0, 32, 8] }, { rank := 0, op := "OpName.FW_stack", ins := [7483, 7669, 7855, 8041, 8227, 8413, 8599, 8785, 8971, 9157, 9343, 9529, 9733, 9905, 10077, 10249, 10421, 10593, 10765, 10937, 11109, 11281, 11453, 11625], outs := [11729] }, { rank := 0, op := "OpName.FW_stack", ins := [7485, 7671, 7857, 8043, 8229, 8415, 8601, 8787, 8973, 9159, 9345, 9531, 9735, 9907, 10079, 10251, 10423, 10595, 10767, 10939, 11111, 11283, 11455, 11627], outs := [11781] }, { rank := 0, op := "OpName.FW_sigmoid", ins := [11645], outs := [11647] }, { rank := 0, op := "OpName.FW_swiglu", ins := [11663, 11681], outs := [11685] }, { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16889, 11624, 11626, 11630, 11632], outs := [11634], params := [64, 32, 64, 8] }, { rank := 1, op := "OpName.FW_stack", ins := [7484, 7670, 7856, 8042, 8228, 8414, 8600, 8786, 8972, 9158, 9344, 9530, 9734, 9906, 10078, 10250, 10422, 10594, 10766, 10938, 11110, 11282, 11454, 11626], outs := [11730] }, { rank := 1, op := "OpName.FW_stack", ins := [7486, 7672, 7858, 8044, 8230, 8416, 8602, 8788, 8974, 9160, 9346, 9532, 9736, 9908, 10080, 10252, 10424, 10596, 10768, 10940, 11112, 11284, 11456, 11628], outs := [11782] }, { rank := 1, op := "OpName.FW_sigmoid", ins := [11646], outs := [11648] }, { rank := 1, op := "OpName.FW_swiglu", ins := [11664, 11682], outs := [11686] }, { rank := 0, op := "OpName.FW_reshape", ins := [11685], outs := [11687], params := [2048, 512] }, { rank := 0, op := "OpName.AllGatherPrim", ins := [11729, 11730], outs := [4675], params := [1] }, { rank := 0, op := "OpName.AllGatherPrim", ins := [11781, 11782], outs := [4676], params := [1] }, { rank := 1, op := "OpName.FW_reshape", ins := [11686], outs := [11688], params := [2048, 512] }, { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11687, 5920], outs := [11693] }, { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11688, 5920], outs := [11694] }, { rank := 0, op := "OpName.FW_view", ins := [11693], outs := [11703], params := [2048, 1024] }, { rank := 1, op := "OpName.FW_view", ins := [11694], outs := [11704], params := [2048, 1024] }, { rank := 0, op := "OpName.FW_mul", ins := [11647, 11703], outs := [11707] }, { rank := 1, op := "OpName.FW_mul", ins := [11648, 11704], outs := [11708] }, { rank := 0, op := "OpName.FW_add", ins := [11633, 11707], outs := [11711] }, { rank := 1, op := "OpName.FW_add", ins := [11634, 11708], outs := [11712] }, { rank := 0, op := "OpName.FW_float", ins := [11711], outs := [11717] }, { rank := 1, op := "OpName.FW_float", ins := [11712], outs := [11718] }, { rank := 0, op := "OpName.FW_add", ins := [16847, 11717], outs := [11721] }, { rank := 1, op := "OpName.FW_add", ins := [16855, 11718], outs := [11722] }, { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11721, 5927], outs := [11727], params := [2, 0] }, { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11722, 5927], outs := [11728], params := [2, 1] }, { rank := 0, op := "OpName.FW_rms_norm", ins := [11727, 5929], outs := [11833] }, { rank := 1, op := "OpName.FW_rms_norm", ins := [11728, 5929], outs := [11834] }, { rank := 0, op := "OpName.FW_inner_chunk_ce", ins := [11833, 5931, 11835], outs := [11837, 11839], params := [1024] }, { rank := 1, op := "OpName.FW_inner_chunk_ce", ins := [11834, 5931, 11836], outs := [11838, 11840], params := [1024] }, { rank := 0, op := "OpName.AllGatherPrim", ins := [11837, 11838], outs := [4673], params := [0] }, { rank := 0, op := "OpName.AllGatherPrim", ins := [11839, 11840], outs := [4674], params := [0] }]

theorem pmChunk_47_wf : ∀ n ∈ pmChunk_47, IsWellFormedNode pm n := by
  intro n hn
  simp only [pmChunk_47, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · rw [h0]
    exact pm_node_1880_wf
  · rw [h1]
    exact pm_node_1881_wf
  · rw [h2]
    exact pm_node_1882_wf
  · rw [h3]
    exact pm_node_1883_wf
  · rw [h4]
    exact pm_node_1884_wf
  · rw [h5]
    exact pm_node_1885_wf
  · rw [h6]
    exact pm_node_1886_wf
  · rw [h7]
    exact pm_node_1887_wf
  · rw [h8]
    exact pm_node_1888_wf
  · rw [h9]
    exact pm_node_1889_wf
  · rw [h10]
    exact pm_node_1890_wf
  · rw [h11]
    exact pm_node_1891_wf
  · rw [h12]
    exact pm_node_1892_wf
  · rw [h13]
    exact pm_node_1893_wf
  · rw [h14]
    exact pm_node_1894_wf
  · rw [h15]
    exact pm_node_1895_wf
  · rw [h16]
    exact pm_node_1896_wf
  · rw [h17]
    exact pm_node_1897_wf
  · rw [h18]
    exact pm_node_1898_wf
  · rw [h19]
    exact pm_node_1899_wf
  · rw [h20]
    exact pm_node_1900_wf
  · rw [h21]
    exact pm_node_1901_wf
  · rw [h22]
    exact pm_node_1902_wf
  · rw [h23]
    exact pm_node_1903_wf
  · rw [h24]
    exact pm_node_1904_wf
  · rw [h25]
    exact pm_node_1905_wf
  · rw [h26]
    exact pm_node_1906_wf
  · rw [h27]
    exact pm_node_1907_wf
  · rw [h28]
    exact pm_node_1908_wf
  · rw [h29]
    exact pm_node_1909_wf
  · rw [h30]
    exact pm_node_1910_wf
  · rw [h31]
    exact pm_node_1911_wf
  · rw [h32]
    exact pm_node_1912_wf
  · rw [h33]
    exact pm_node_1913_wf
  · rw [h34]
    exact pm_node_1914_wf
  · rw [h35]
    exact pm_node_1915_wf
  · rw [h36]
    exact pm_node_1916_wf
  · rw [h37]
    exact pm_node_1917_wf
  · rw [h38]
    exact pm_node_1918_wf
  · rw [h39]
    exact pm_node_1919_wf

def pmNodeChunks : List NodeDecl :=
  pmChunk_0 ++ (pmChunk_1 ++ (pmChunk_2 ++ (pmChunk_3 ++ (pmChunk_4 ++ (pmChunk_5 ++ (pmChunk_6 ++ (pmChunk_7 ++ (pmChunk_8 ++ (pmChunk_9 ++ (pmChunk_10 ++ (pmChunk_11 ++ (pmChunk_12 ++ (pmChunk_13 ++ (pmChunk_14 ++ (pmChunk_15 ++ (pmChunk_16 ++ (pmChunk_17 ++ (pmChunk_18 ++ (pmChunk_19 ++ (pmChunk_20 ++ (pmChunk_21 ++ (pmChunk_22 ++ (pmChunk_23 ++ (pmChunk_24 ++ (pmChunk_25 ++ (pmChunk_26 ++ (pmChunk_27 ++ (pmChunk_28 ++ (pmChunk_29 ++ (pmChunk_30 ++ (pmChunk_31 ++ (pmChunk_32 ++ (pmChunk_33 ++ (pmChunk_34 ++ (pmChunk_35 ++ (pmChunk_36 ++ (pmChunk_37 ++ (pmChunk_38 ++ (pmChunk_39 ++ (pmChunk_40 ++ (pmChunk_41 ++ (pmChunk_42 ++ (pmChunk_43 ++ (pmChunk_44 ++ (pmChunk_45 ++ (pmChunk_46 ++ (pmChunk_47)))))))))))))))))))))))))))))))))))))))))))))))

theorem pm_nodes_eq_chunks : pm.nodes = pmNodeChunks := by
  rfl

theorem pm_wellFormed : IsWellFormedGraph pm := by
  intro n hn
  rw [pm_nodes_eq_chunks] at hn
  simp only [pmNodeChunks, List.mem_append] at hn
  rcases hn with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47
  · exact pmChunk_0_wf n h0
  · exact pmChunk_1_wf n h1
  · exact pmChunk_2_wf n h2
  · exact pmChunk_3_wf n h3
  · exact pmChunk_4_wf n h4
  · exact pmChunk_5_wf n h5
  · exact pmChunk_6_wf n h6
  · exact pmChunk_7_wf n h7
  · exact pmChunk_8_wf n h8
  · exact pmChunk_9_wf n h9
  · exact pmChunk_10_wf n h10
  · exact pmChunk_11_wf n h11
  · exact pmChunk_12_wf n h12
  · exact pmChunk_13_wf n h13
  · exact pmChunk_14_wf n h14
  · exact pmChunk_15_wf n h15
  · exact pmChunk_16_wf n h16
  · exact pmChunk_17_wf n h17
  · exact pmChunk_18_wf n h18
  · exact pmChunk_19_wf n h19
  · exact pmChunk_20_wf n h20
  · exact pmChunk_21_wf n h21
  · exact pmChunk_22_wf n h22
  · exact pmChunk_23_wf n h23
  · exact pmChunk_24_wf n h24
  · exact pmChunk_25_wf n h25
  · exact pmChunk_26_wf n h26
  · exact pmChunk_27_wf n h27
  · exact pmChunk_28_wf n h28
  · exact pmChunk_29_wf n h29
  · exact pmChunk_30_wf n h30
  · exact pmChunk_31_wf n h31
  · exact pmChunk_32_wf n h32
  · exact pmChunk_33_wf n h33
  · exact pmChunk_34_wf n h34
  · exact pmChunk_35_wf n h35
  · exact pmChunk_36_wf n h36
  · exact pmChunk_37_wf n h37
  · exact pmChunk_38_wf n h38
  · exact pmChunk_39_wf n h39
  · exact pmChunk_40_wf n h40
  · exact pmChunk_41_wf n h41
  · exact pmChunk_42_wf n h42
  · exact pmChunk_43_wf n h43
  · exact pmChunk_44_wf n h44
  · exact pmChunk_45_wf n h45
  · exact pmChunk_46_wf n h46
  · exact pmChunk_47_wf n h47

theorem pm_topoSorted : IsTopoSorted pm.nodes := by
  apply isTopoSorted_of_bool
  native_decide

theorem pm_nodes_nodup : pm.nodes.Nodup := by native_decide

end TrainVerify.Denote.GeneratedStructuralFacts
