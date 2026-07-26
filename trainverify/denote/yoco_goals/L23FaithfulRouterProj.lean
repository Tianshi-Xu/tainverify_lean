/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.L23FaithfulEntry
import denote.yoco_goals.ZigzagRouterRel
import denote.yoco_goals.ZigzagElemwiseRel

/-!
# Faithful zigzag relations for the block-11 MoE branch (router projections)

Mechanical transport of the (green) block-10 段 `L13FaithfulRouterProj` to block 11.
Every tensor id / node index is re-certified by `native_decide`.
The block-11 cu tensor is **5884**.

* SM 900 `FW_float [8587] → [5896]`                          (PM 1862 / 1866 → 11615 / 11616)
* SM 901 `FW_reshape [8595] → [5905]`                        (PM 1863 / 1867 → 11635 / 11636)
* SM 902 `FW_reshape [8599] → [5910]`                        (PM 1864 / 1868 → 11649 / 11650)
* SM 903 `FW_reshape [8603] → [5914]`                        (PM 1865 / 1869 → 11667 / 11668)
* SM 904 `FW_norm_linear [5896, 5897] → [5898]`              (PM 1870 / 1874 → 11621 / 11622)
* SM 905 `FW_mix_precision_linear [5905, 5906] → [5907]`     (PM 1871 / 1875 → 11639 / 11640)
* SM 906 `FW_mix_precision_linear [5910, 5911] → [5912]`     (PM 1872 / 1876 → 11653 / 11654)
* SM 907 `FW_mix_precision_linear [5914, 5915] → [5916]`     (PM 1873 / 1877 → 11671 / 11672)

Weights 5897 `[64,1024]`, 5906 `[1,1024]`, 5911 `[512,1024]`, 5915 `[512,1024]` are
replicated singletons.

The `hdec : decodeCuSeqlens cu = [0, 2 * 2048]` side condition of the router lemma is
**derived** from the ambient zigzag well-formedness carried by the parent relation.
No new hypotheses are introduced.
-/

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option linter.style.setOption false

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

/-! ### Node literals -/

private def l23rpSmFloat5896 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [8587], outs := [5896] }
private def l23rpSmResh5905 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8595], outs := [5905],
    params := [4096,1024] }
private def l23rpSmResh5910 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8599], outs := [5910],
    params := [4096,1024] }
private def l23rpSmResh5914 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [8603], outs := [5914],
    params := [4096,1024] }
private def l23rpSmNL5898 : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [5896,5897], outs := [5898] }
private def l23rpSmMPL5907 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5905,5906], outs := [5907] }
private def l23rpSmMPL5912 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5910,5911], outs := [5912] }
private def l23rpSmMPL5916 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5914,5915], outs := [5916] }

private def l23rpPmFloat11615 : NodeDecl :=
  { rank := 0, op := "OpName.FW_float", ins := [16862], outs := [11615] }
private def l23rpPmResh11635 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16870], outs := [11635],
    params := [2048,1024] }
private def l23rpPmResh11649 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16874], outs := [11649],
    params := [2048,1024] }
private def l23rpPmResh11667 : NodeDecl :=
  { rank := 0, op := "OpName.FW_reshape", ins := [16878], outs := [11667],
    params := [2048,1024] }
private def l23rpPmFloat11616 : NodeDecl :=
  { rank := 1, op := "OpName.FW_float", ins := [16885], outs := [11616] }
private def l23rpPmResh11636 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16893], outs := [11636],
    params := [2048,1024] }
private def l23rpPmResh11650 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16897], outs := [11650],
    params := [2048,1024] }
private def l23rpPmResh11668 : NodeDecl :=
  { rank := 1, op := "OpName.FW_reshape", ins := [16901], outs := [11668],
    params := [2048,1024] }
private def l23rpPmNL11621 : NodeDecl :=
  { rank := 0, op := "OpName.FW_norm_linear", ins := [11615,5897], outs := [11621] }
private def l23rpPmMPL11639 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11635,5906], outs := [11639] }
private def l23rpPmMPL11653 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11649,5911], outs := [11653] }
private def l23rpPmMPL11671 : NodeDecl :=
  { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11667,5915], outs := [11671] }
private def l23rpPmNL11622 : NodeDecl :=
  { rank := 1, op := "OpName.FW_norm_linear", ins := [11616,5897], outs := [11622] }
private def l23rpPmMPL11640 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11636,5906], outs := [11640] }
private def l23rpPmMPL11654 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11650,5911], outs := [11654] }
private def l23rpPmMPL11672 : NodeDecl :=
  { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11668,5915], outs := [11672] }

/-! ### Certified node indices -/

set_option maxRecDepth 1000000 in
private theorem l23rp_sm_node_facts :
    sm.nodes[900]'(by native_decide) = l23rpSmFloat5896 ∧
    sm.nodes[901]'(by native_decide) = l23rpSmResh5905 ∧
    sm.nodes[902]'(by native_decide) = l23rpSmResh5910 ∧
    sm.nodes[903]'(by native_decide) = l23rpSmResh5914 ∧
    sm.nodes[904]'(by native_decide) = l23rpSmNL5898 ∧
    sm.nodes[905]'(by native_decide) = l23rpSmMPL5907 ∧
    sm.nodes[906]'(by native_decide) = l23rpSmMPL5912 ∧
    sm.nodes[907]'(by native_decide) = l23rpSmMPL5916 := by
  native_decide

set_option maxRecDepth 1000000 in
private theorem l23rp_pm_node_facts :
    pm.nodes[1862]'(by native_decide) = l23rpPmFloat11615 ∧
    pm.nodes[1863]'(by native_decide) = l23rpPmResh11635 ∧
    pm.nodes[1864]'(by native_decide) = l23rpPmResh11649 ∧
    pm.nodes[1865]'(by native_decide) = l23rpPmResh11667 ∧
    pm.nodes[1866]'(by native_decide) = l23rpPmFloat11616 ∧
    pm.nodes[1867]'(by native_decide) = l23rpPmResh11636 ∧
    pm.nodes[1868]'(by native_decide) = l23rpPmResh11650 ∧
    pm.nodes[1869]'(by native_decide) = l23rpPmResh11668 ∧
    pm.nodes[1870]'(by native_decide) = l23rpPmNL11621 ∧
    pm.nodes[1871]'(by native_decide) = l23rpPmMPL11639 ∧
    pm.nodes[1872]'(by native_decide) = l23rpPmMPL11653 ∧
    pm.nodes[1873]'(by native_decide) = l23rpPmMPL11671 ∧
    pm.nodes[1874]'(by native_decide) = l23rpPmNL11622 ∧
    pm.nodes[1875]'(by native_decide) = l23rpPmMPL11640 ∧
    pm.nodes[1876]'(by native_decide) = l23rpPmMPL11654 ∧
    pm.nodes[1877]'(by native_decide) = l23rpPmMPL11672 := by
  native_decide

private theorem l23rp_nonempty_sm (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_sm_nodes_nonempty n (List.mem_of_mem_drop hn)

private theorem l23rp_nonempty_pm (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, n.outs ≠ [] := by
  intro n hn
  exact layer1_pm_nodes_nonempty n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l23rp_weights_not_written :
    ((∀ n ∈ sm.nodes, 5897 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5906 ∉ n.outs) ∧
      (∀ n ∈ sm.nodes, 5911 ∉ n.outs) ∧ (∀ n ∈ sm.nodes, 5915 ∉ n.outs)) ∧
    ((∀ n ∈ pm.nodes, 5897 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5906 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5911 ∉ n.outs) ∧ (∀ n ∈ pm.nodes, 5915 ∉ n.outs) ∧
      (∀ n ∈ pm.nodes, 5884 ∉ n.outs)) := by
  native_decide

private theorem l23rp_w5897_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5897 ∉ n.outs := by
  intro n hn
  exact l23rp_weights_not_written.1.1 n (List.mem_of_mem_drop hn)

private theorem l23rp_w5897_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5897 ∉ n.outs := by
  intro n hn
  exact l23rp_weights_not_written.2.1 n (List.mem_of_mem_drop hn)

private theorem l23rp_w5906_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5906 ∉ n.outs := by
  intro n hn
  exact l23rp_weights_not_written.1.2.1 n (List.mem_of_mem_drop hn)

private theorem l23rp_w5906_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5906 ∉ n.outs := by
  intro n hn
  exact l23rp_weights_not_written.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l23rp_w5911_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5911 ∉ n.outs := by
  intro n hn
  exact l23rp_weights_not_written.1.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l23rp_w5911_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5911 ∉ n.outs := by
  intro n hn
  exact l23rp_weights_not_written.2.2.2.1 n (List.mem_of_mem_drop hn)

private theorem l23rp_w5915_sm_drop (k : Nat) :
    ∀ n ∈ sm.nodes.drop k, 5915 ∉ n.outs := by
  intro n hn
  exact l23rp_weights_not_written.1.2.2.2 n (List.mem_of_mem_drop hn)

private theorem l23rp_w5915_pm_drop (k : Nat) :
    ∀ n ∈ pm.nodes.drop k, 5915 ∉ n.outs := by
  intro n hn
  exact l23rp_weights_not_written.2.2.2.2.1 n (List.mem_of_mem_drop hn)

set_option maxRecDepth 1000000 in
private theorem l23rp_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(901, 5896), (900, 8587), (902, 5905), (901, 8595), (903, 5910), (902, 8599), (904, 5914), (903, 8603), (905, 5898), (904, 5896), (906, 5907), (905, 5905), (907, 5912), (906, 5910), (908, 5916), (907, 5914)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

set_option maxRecDepth 1000000 in
private theorem l23rp_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1863, 11615), (1862, 16862), (1864, 11635), (1863, 16870), (1865, 11649), (1864, 16874), (1866, 11667), (1865, 16878), (1867, 11616), (1866, 16885), (1868, 11636), (1867, 16893), (1869, 11650), (1868, 16897), (1870, 11668), (1869, 16901), (1871, 11621), (1870, 11615), (1872, 11639), (1871, 11635), (1873, 11653), (1872, 11649), (1874, 11671), (1873, 11667), (1875, 11622), (1874, 11616), (1876, 11640), (1875, 11636), (1877, 11654), (1876, 11650), (1878, 11672), (1877, 11668)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

/-! ### Node reductions -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_red_sm5896 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5896 =
      denoteGraphDistributedFaithful sm initSM 8587 := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 900 l23rpSmFloat5896
    8587 5896 (fun x => x)
    (by native_decide) l23rp_sm_node_facts.1 ?_
    (l23rp_nonempty_sm 901) (l23rp_sm_not_written 901 5896 (by decide))
    (l23rp_nonempty_sm 900) (l23rp_sm_not_written 900 8587 (by decide))
  intro s
  unfold l23rpSmFloat5896
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out sm s 0 8587 5896 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_red_sm5905 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5905 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8595) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 901 l23rpSmResh5905
    8595 5905 (fun x => fw_view [4096,1024] x)
    (by native_decide) l23rp_sm_node_facts.2.1 ?_
    (l23rp_nonempty_sm 902) (l23rp_sm_not_written 902 5905 (by decide))
    (l23rp_nonempty_sm 901) (l23rp_sm_not_written 901 8595 (by decide))
  intro s
  unfold l23rpSmResh5905
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8595 5905 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_red_sm5910 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5910 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8599) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 902 l23rpSmResh5910
    8599 5910 (fun x => fw_view [4096,1024] x)
    (by native_decide) l23rp_sm_node_facts.2.2.1 ?_
    (l23rp_nonempty_sm 903) (l23rp_sm_not_written 903 5910 (by decide))
    (l23rp_nonempty_sm 902) (l23rp_sm_not_written 902 8599 (by decide))
  intro s
  unfold l23rpSmResh5910
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8599 5910 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_red_sm5914 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5914 =
      fw_view [4096,1024] (denoteGraphDistributedFaithful sm initSM 8603) := by
  refine denoteGraphDistributedFaithful_reduce1 sm initSM 903 l23rpSmResh5914
    8603 5914 (fun x => fw_view [4096,1024] x)
    (by native_decide) l23rp_sm_node_facts.2.2.2.1 ?_
    (l23rp_nonempty_sm 904) (l23rp_sm_not_written 904 5914 (by decide))
    (l23rp_nonempty_sm 903) (l23rp_sm_not_written 903 8603 (by decide))
  intro s
  unfold l23rpSmResh5914
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out sm s 0 8603 5914 [4096,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_red_sm5898 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5898 =
      fw_norm_linear (denoteGraphDistributedFaithful sm initSM 5896)
        (denoteGraphDistributedFaithful sm initSM 5897) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 904 l23rpSmNL5898
    5896 5897 5898 fw_norm_linear
    (by native_decide) l23rp_sm_node_facts.2.2.2.2.1 ?_
    (l23rp_nonempty_sm 905) (l23rp_sm_not_written 905 5898 (by decide))
    (l23rp_nonempty_sm 904) (l23rp_sm_not_written 904 5896 (by decide))
    (l23rp_w5897_sm_drop 904)
  intro s
  unfold l23rpSmNL5898
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out sm s 0 5896 5897 5898

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_red_sm5907 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5907 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5905)
        (denoteGraphDistributedFaithful sm initSM 5906) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 905 l23rpSmMPL5907
    5905 5906 5907 fw_linear
    (by native_decide) l23rp_sm_node_facts.2.2.2.2.2.1 ?_
    (l23rp_nonempty_sm 906) (l23rp_sm_not_written 906 5907 (by decide))
    (l23rp_nonempty_sm 905) (l23rp_sm_not_written 905 5905 (by decide))
    (l23rp_w5906_sm_drop 905)
  intro s
  unfold l23rpSmMPL5907
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5905 5906 5907

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_red_sm5912 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5912 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5910)
        (denoteGraphDistributedFaithful sm initSM 5911) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 906 l23rpSmMPL5912
    5910 5911 5912 fw_linear
    (by native_decide) l23rp_sm_node_facts.2.2.2.2.2.2.1 ?_
    (l23rp_nonempty_sm 907) (l23rp_sm_not_written 907 5912 (by decide))
    (l23rp_nonempty_sm 906) (l23rp_sm_not_written 906 5910 (by decide))
    (l23rp_w5911_sm_drop 906)
  intro s
  unfold l23rpSmMPL5912
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5910 5911 5912

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_red_sm5916 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5916 =
      fw_linear (denoteGraphDistributedFaithful sm initSM 5914)
        (denoteGraphDistributedFaithful sm initSM 5915) := by
  refine denoteGraphDistributedFaithful_reduce2 sm initSM 907 l23rpSmMPL5916
    5914 5915 5916 fw_linear
    (by native_decide) l23rp_sm_node_facts.2.2.2.2.2.2.2 ?_
    (l23rp_nonempty_sm 908) (l23rp_sm_not_written 908 5916 (by decide))
    (l23rp_nonempty_sm 907) (l23rp_sm_not_written 907 5914 (by decide))
    (l23rp_w5915_sm_drop 907)
  intro s
  unfold l23rpSmMPL5916
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p sm s 0 5914 5915 5916

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_red_pm11615 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11615 =
      denoteGraphDistributedFaithful pm initPM 16862 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1862 l23rpPmFloat11615
    16862 11615 (fun x => x)
    (by native_decide) l23rp_pm_node_facts.1 ?_
    (l23rp_nonempty_pm 1863) (l23rp_pm_not_written 1863 11615 (by decide))
    (l23rp_nonempty_pm 1862) (l23rp_pm_not_written 1862 16862 (by decide))
  intro s
  unfold l23rpPmFloat11615
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 0 16862 11615 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_red_pm11635 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11635 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16870) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1863 l23rpPmResh11635
    16870 11635 (fun x => fw_view [2048,1024] x)
    (by native_decide) l23rp_pm_node_facts.2.1 ?_
    (l23rp_nonempty_pm 1864) (l23rp_pm_not_written 1864 11635 (by decide))
    (l23rp_nonempty_pm 1863) (l23rp_pm_not_written 1863 16870 (by decide))
  intro s
  unfold l23rpPmResh11635
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16870 11635 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_red_pm11649 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11649 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16874) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1864 l23rpPmResh11649
    16874 11649 (fun x => fw_view [2048,1024] x)
    (by native_decide) l23rp_pm_node_facts.2.2.1 ?_
    (l23rp_nonempty_pm 1865) (l23rp_pm_not_written 1865 11649 (by decide))
    (l23rp_nonempty_pm 1864) (l23rp_pm_not_written 1864 16874 (by decide))
  intro s
  unfold l23rpPmResh11649
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16874 11649 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_red_pm11667 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11667 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16878) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1865 l23rpPmResh11667
    16878 11667 (fun x => fw_view [2048,1024] x)
    (by native_decide) l23rp_pm_node_facts.2.2.2.1 ?_
    (l23rp_nonempty_pm 1866) (l23rp_pm_not_written 1866 11667 (by decide))
    (l23rp_nonempty_pm 1865) (l23rp_pm_not_written 1865 16878 (by decide))
  intro s
  unfold l23rpPmResh11667
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 0 16878 11667 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_red_pm11616 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11616 =
      denoteGraphDistributedFaithful pm initPM 16885 := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1866 l23rpPmFloat11616
    16885 11616 (fun x => x)
    (by native_decide) l23rp_pm_node_facts.2.2.2.2.1 ?_
    (l23rp_nonempty_pm 1867) (l23rp_pm_not_written 1867 11616 (by decide))
    (l23rp_nonempty_pm 1866) (l23rp_pm_not_written 1866 16885 (by decide))
  intro s
  unfold l23rpPmFloat11616
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_float_out pm s 1 16885 11616 []

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_red_pm11636 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11636 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16893) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1867 l23rpPmResh11636
    16893 11636 (fun x => fw_view [2048,1024] x)
    (by native_decide) l23rp_pm_node_facts.2.2.2.2.2.1 ?_
    (l23rp_nonempty_pm 1868) (l23rp_pm_not_written 1868 11636 (by decide))
    (l23rp_nonempty_pm 1867) (l23rp_pm_not_written 1867 16893 (by decide))
  intro s
  unfold l23rpPmResh11636
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16893 11636 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_red_pm11650 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11650 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16897) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1868 l23rpPmResh11650
    16897 11650 (fun x => fw_view [2048,1024] x)
    (by native_decide) l23rp_pm_node_facts.2.2.2.2.2.2.1 ?_
    (l23rp_nonempty_pm 1869) (l23rp_pm_not_written 1869 11650 (by decide))
    (l23rp_nonempty_pm 1868) (l23rp_pm_not_written 1868 16897 (by decide))
  intro s
  unfold l23rpPmResh11650
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16897 11650 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_red_pm11668 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11668 =
      fw_view [2048,1024] (denoteGraphDistributedFaithful pm initPM 16901) := by
  refine denoteGraphDistributedFaithful_reduce1 pm initPM 1869 l23rpPmResh11668
    16901 11668 (fun x => fw_view [2048,1024] x)
    (by native_decide) l23rp_pm_node_facts.2.2.2.2.2.2.2.1 ?_
    (l23rp_nonempty_pm 1870) (l23rp_pm_not_written 1870 11668 (by decide))
    (l23rp_nonempty_pm 1869) (l23rp_pm_not_written 1869 16901 (by decide))
  intro s
  unfold l23rpPmResh11668
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_reshape_out pm s 1 16901 11668 [2048,1024]

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_red_pm11621 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11621 =
      fw_norm_linear (denoteGraphDistributedFaithful pm initPM 11615)
        (denoteGraphDistributedFaithful pm initPM 5897) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1870 l23rpPmNL11621
    11615 5897 11621 fw_norm_linear
    (by native_decide) l23rp_pm_node_facts.2.2.2.2.2.2.2.2.1 ?_
    (l23rp_nonempty_pm 1871) (l23rp_pm_not_written 1871 11621 (by decide))
    (l23rp_nonempty_pm 1870) (l23rp_pm_not_written 1870 11615 (by decide))
    (l23rp_w5897_pm_drop 1870)
  intro s
  unfold l23rpPmNL11621
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm s 0 11615 5897 11621

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_red_pm11639 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11639 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11635)
        (denoteGraphDistributedFaithful pm initPM 5906) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1871 l23rpPmMPL11639
    11635 5906 11639 fw_linear
    (by native_decide) l23rp_pm_node_facts.2.2.2.2.2.2.2.2.2.1 ?_
    (l23rp_nonempty_pm 1872) (l23rp_pm_not_written 1872 11639 (by decide))
    (l23rp_nonempty_pm 1871) (l23rp_pm_not_written 1871 11635 (by decide))
    (l23rp_w5906_pm_drop 1871)
  intro s
  unfold l23rpPmMPL11639
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 11635 5906 11639

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_red_pm11653 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11653 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11649)
        (denoteGraphDistributedFaithful pm initPM 5911) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1872 l23rpPmMPL11653
    11649 5911 11653 fw_linear
    (by native_decide) l23rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l23rp_nonempty_pm 1873) (l23rp_pm_not_written 1873 11653 (by decide))
    (l23rp_nonempty_pm 1872) (l23rp_pm_not_written 1872 11649 (by decide))
    (l23rp_w5911_pm_drop 1872)
  intro s
  unfold l23rpPmMPL11653
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 11649 5911 11653

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_red_pm11671 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11671 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11667)
        (denoteGraphDistributedFaithful pm initPM 5915) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1873 l23rpPmMPL11671
    11667 5915 11671 fw_linear
    (by native_decide) l23rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l23rp_nonempty_pm 1874) (l23rp_pm_not_written 1874 11671 (by decide))
    (l23rp_nonempty_pm 1873) (l23rp_pm_not_written 1873 11667 (by decide))
    (l23rp_w5915_pm_drop 1873)
  intro s
  unfold l23rpPmMPL11671
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 0 11667 5915 11671

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_red_pm11622 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11622 =
      fw_norm_linear (denoteGraphDistributedFaithful pm initPM 11616)
        (denoteGraphDistributedFaithful pm initPM 5897) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1874 l23rpPmNL11622
    11616 5897 11622 fw_norm_linear
    (by native_decide) l23rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l23rp_nonempty_pm 1875) (l23rp_pm_not_written 1875 11622 (by decide))
    (l23rp_nonempty_pm 1874) (l23rp_pm_not_written 1874 11616 (by decide))
    (l23rp_w5897_pm_drop 1874)
  intro s
  unfold l23rpPmNL11622
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_norm_linear_out pm s 1 11616 5897 11622

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_red_pm11640 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11640 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11636)
        (denoteGraphDistributedFaithful pm initPM 5906) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1875 l23rpPmMPL11640
    11636 5906 11640 fw_linear
    (by native_decide) l23rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l23rp_nonempty_pm 1876) (l23rp_pm_not_written 1876 11640 (by decide))
    (l23rp_nonempty_pm 1875) (l23rp_pm_not_written 1875 11636 (by decide))
    (l23rp_w5906_pm_drop 1875)
  intro s
  unfold l23rpPmMPL11640
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 11636 5906 11640

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_red_pm11654 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11654 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11650)
        (denoteGraphDistributedFaithful pm initPM 5911) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1876 l23rpPmMPL11654
    11650 5911 11654 fw_linear
    (by native_decide) l23rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ?_
    (l23rp_nonempty_pm 1877) (l23rp_pm_not_written 1877 11654 (by decide))
    (l23rp_nonempty_pm 1876) (l23rp_pm_not_written 1876 11650 (by decide))
    (l23rp_w5911_pm_drop 1876)
  intro s
  unfold l23rpPmMPL11654
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 11650 5911 11654

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_red_pm11672 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11672 =
      fw_linear (denoteGraphDistributedFaithful pm initPM 11668)
        (denoteGraphDistributedFaithful pm initPM 5915) := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 1877 l23rpPmMPL11672
    11668 5915 11672 fw_linear
    (by native_decide) l23rp_pm_node_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ?_
    (l23rp_nonempty_pm 1878) (l23rp_pm_not_written 1878 11672 (by decide))
    (l23rp_nonempty_pm 1877) (l23rp_pm_not_written 1877 11668 (by decide))
    (l23rp_w5915_pm_drop 1877)
  intro s
  unfold l23rpPmMPL11672
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_fw_mix_precision_linear_out_1p pm s 1 11668 5915 11672

/-! ### Replicated weight agreement -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_weight_eq (initSM initPM : Store)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (W : Tid) (g : LineageGoal) (hg : g ∈ initGoals)
    (htp : g.tps = [{rank := 0, tid := W}]) (hgd : g.gatherDim = 0)
    (hrep : g.replicated = false) (hts : g.ts = W)
    (hsw : ∀ n ∈ sm.nodes, W ∉ n.outs) (hpw : ∀ n ∈ pm.nodes, W ∉ n.outs) :
    denoteGraphDistributedFaithful sm initSM W =
      denoteGraphDistributedFaithful pm initPM W := by
  have h : initSM W = initPM W := by
    have hr := recon_weight initSM initPM hInit g hg W htp hgd hrep hts
    unfold denoteGraph at hr
    rw [foldl_applyNode_at_not_written sm sm.nodes initSM W hsw,
      foldl_applyNode_at_not_written pm pm.nodes initPM W hpw] at hr
    exact hr
  have e1 : denoteGraphDistributedFaithful sm initSM W = initSM W := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written sm sm.nodes initSM W
      layer1_sm_nodes_nonempty hsw
  have e2 : denoteGraphDistributedFaithful pm initPM W = initPM W := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM W
      layer1_pm_nodes_nonempty hpw
  rw [e1, e2]; exact h

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
private theorem l23rp_pm_weight_shape (initPM : Store)
    (hPM : StoreShapesHold initPM pmInitEnv) (W : Tid) (sh : Shape)
    (hmem : pmInitEnv W = some sh)
    (hpw : ∀ n ∈ pm.nodes, W ∉ n.outs) :
    (denoteGraphDistributedFaithful pm initPM W).shape = sh := by
  have e2 : denoteGraphDistributedFaithful pm initPM W = initPM W := by
    unfold denoteGraphDistributedFaithful
    exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes initPM W
      layer1_pm_nodes_nonempty hpw
  rw [e2]
  exact hPM W sh hmem

/-! ### Goals -/

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5896_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5896)
      (denoteGraphDistributedFaithful pm initPM 11615)
      (denoteGraphDistributedFaithful pm initPM 11616)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8587_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l23rp_red_sm5896 initSM, l23rp_red_pm11615 initPM, l23rp_red_pm11616 initPM]
  exact hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5905_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5905)
      (denoteGraphDistributedFaithful pm initPM 11635)
      (denoteGraphDistributedFaithful pm initPM 11636)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8595_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l23rp_red_sm5905 initSM, l23rp_red_pm11635 initPM, l23rp_red_pm11636 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5910_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5910)
      (denoteGraphDistributedFaithful pm initPM 11649)
      (denoteGraphDistributedFaithful pm initPM 11650)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8599_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l23rp_red_sm5910 initSM, l23rp_red_pm11649 initPM, l23rp_red_pm11650 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5914_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5914)
      (denoteGraphDistributedFaithful pm initPM 11667)
      (denoteGraphDistributedFaithful pm initPM 11668)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1024] [2048, 1024] := by
  have hparent :=
    recon_zigzagGoal_8603_faithful initSM initPM hSM hPM hInit hValues hCu
  rw [l23rp_red_sm5914 initSM, l23rp_red_pm11667 initPM, l23rp_red_pm11668 initPM]
  exact Zigzag2Rel.view_id' hparent

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5907_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5907)
      (denoteGraphDistributedFaithful pm initPM 11639)
      (denoteGraphDistributedFaithful pm initPM 11640)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 1] [2048, 1] := by
  have hparent :=
    recon_zigzagGoal_5905_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5906 =
      denoteGraphDistributedFaithful pm initPM 5906 :=
    l23rp_weight_eq initSM initPM hInit 5906 initGoal_5906 (by native_decide)
      rfl rfl rfl rfl
      l23rp_weights_not_written.1.2.1 l23rp_weights_not_written.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5906).shape = [1,1024] :=
    l23rp_pm_weight_shape initPM hPM 5906 [1,1024] (by native_decide)
      l23rp_weights_not_written.2.2.1
  rw [l23rp_red_sm5907 initSM, l23rp_red_pm11639 initPM, l23rp_red_pm11640 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 1 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5912_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5912)
      (denoteGraphDistributedFaithful pm initPM 11653)
      (denoteGraphDistributedFaithful pm initPM 11654)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5910_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5911 =
      denoteGraphDistributedFaithful pm initPM 5911 :=
    l23rp_weight_eq initSM initPM hInit 5911 initGoal_5911 (by native_decide)
      rfl rfl rfl rfl
      l23rp_weights_not_written.1.2.2.1 l23rp_weights_not_written.2.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5911).shape = [512,1024] :=
    l23rp_pm_weight_shape initPM hPM 5911 [512,1024] (by native_decide)
      l23rp_weights_not_written.2.2.2.1
  rw [l23rp_red_sm5912 initSM, l23rp_red_pm11653 initPM, l23rp_red_pm11654 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5916_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5916)
      (denoteGraphDistributedFaithful pm initPM 11671)
      (denoteGraphDistributedFaithful pm initPM 11672)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 512] [2048, 512] := by
  have hparent :=
    recon_zigzagGoal_5914_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5915 =
      denoteGraphDistributedFaithful pm initPM 5915 :=
    l23rp_weight_eq initSM initPM hInit 5915 initGoal_5915 (by native_decide)
      rfl rfl rfl rfl
      l23rp_weights_not_written.1.2.2.2 l23rp_weights_not_written.2.2.2.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5915).shape = [512,1024] :=
    l23rp_pm_weight_shape initPM hPM 5915 [512,1024] (by native_decide)
      l23rp_weights_not_written.2.2.2.2.1
  rw [l23rp_red_sm5916 initSM, l23rp_red_pm11671 initPM, l23rp_red_pm11672 initPM, hwEq]
  exact Zigzag2Rel.mix_precision_linear 2048 1024 512 hparent hwShape
    (by decide) (by decide) (by decide)

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 16000000 in
theorem recon_zigzagGoal_5898_faithful (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM)
    (hValues : InputValueClassesHold smInputValueClasses initSM ∧
      InputValueClassesHold pmInputValueClasses initPM)
    (hCu : ZigzagCuWF
      (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5337))
      [denoteGraphDistributedFaithful pm initPM 13257,
       denoteGraphDistributedFaithful pm initPM 13258] 2) :
    Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5898)
      (denoteGraphDistributedFaithful pm initPM 11621)
      (denoteGraphDistributedFaithful pm initPM 11622)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [4096, 64] [2048, 64] := by
  have hparent :=
    recon_zigzagGoal_5896_faithful initSM initPM hSM hPM hInit hValues hCu
  have hwEq : denoteGraphDistributedFaithful sm initSM 5897 =
      denoteGraphDistributedFaithful pm initPM 5897 :=
    l23rp_weight_eq initSM initPM hInit 5897 initGoal_5897 (by native_decide)
      rfl rfl rfl rfl
      l23rp_weights_not_written.1.1 l23rp_weights_not_written.2.1
  have hwShape : (denoteGraphDistributedFaithful pm initPM 5897).shape = [64,1024] :=
    l23rp_pm_weight_shape initPM hPM 5897 [64,1024] (by native_decide)
      l23rp_weights_not_written.2.1
  -- `hdec` is *derived* from the ambient zigzag well-formedness carried by `hparent`.
  have hcuShape : (denoteGraphDistributedFaithful pm initPM 5884).shape = [2] :=
    l23rp_pm_weight_shape initPM hPM 5884 [2] (by native_decide)
      l23rp_weights_not_written.2.2.2.2.2
  have hdecLen : (decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5884)).length = 2 := by
    unfold decodeCuSeqlens
    rw [List.length_map, List.length_range, hcuShape]
    rfl
  obtain ⟨source0, source1, hs⟩ := hparent
  have hdec : decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5884)
      = [0, 2 * 2048] := by
    apply list_eq_pair_of_length_head_last _ (2 * 2048) hdecLen hs.cu_wf.cu_starts_zero
    have ht := hs.cu_wf.local_tokens
    simp only [List.getD_cons_zero] at ht
    rw [hs.source0_shape] at ht
    norm_num at ht
    norm_num
    exact ht.symm
  have hparent' : Zigzag2Rel (denoteGraphDistributedFaithful sm initSM 5896)
      (denoteGraphDistributedFaithful pm initPM 11615)
      (denoteGraphDistributedFaithful pm initPM 11616)
      (denoteGraphDistributedFaithful pm initPM 5884)
      [2048 * 2, 1024] [2048, 1024] := ⟨source0, source1, hs⟩
  rw [l23rp_red_sm5898 initSM, l23rp_red_pm11621 initPM, l23rp_red_pm11622 initPM, hwEq]
  exact Zigzag2Rel.norm_linear 2048 1024 64 hparent' hwShape
    (by decide) (by decide) (by decide) (by decide) hdec


end

end TrainVerify.Denote.GeneratedPatterns
