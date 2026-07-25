import denote.GeneratedYOCOMoE

set_option linter.style.nativeDecide false

namespace TrainVerify.Denote.YOCInputValueClasses

open Generated

/-- The exact `cu_seqlens_q` value class emitted for YOCO MoE. -/
def cuseqQClass : InputValueClass :=
  { source := "getitem:root=4188:key=cu_seqlens_q"
    tids := [4694, 4748, 4802, 4856, 4910, 4964, 5018, 5072, 5126,
      5180, 5234, 5288, 5337, 5345, 5394, 5443, 5492, 5541, 5590,
      5639, 5688, 5737, 5786, 5835, 5884, 5927] }

/-- The distinct `cu_seqlens_k` value class emitted for YOCO MoE. -/
def cuseqKClass : InputValueClass :=
  { source := "getitem:root=4188:key=cu_seqlens_k"
    tids := [4695, 4749, 4803, 4857, 4911, 4965, 5019, 5073, 5127,
      5181, 5235, 5289, 5346, 5395, 5444, 5493, 5542, 5591, 5640,
      5689, 5738, 5787, 5836, 5885] }

/-- The exact q class occurs in the generated single-model classes. -/
theorem cuseqQClass_mem_sm : cuseqQClass ∈ smInputValueClasses := by
  native_decide

/-- The exact q class occurs in the generated parallel-model classes. -/
theorem cuseqQClass_mem_pm : cuseqQClass ∈ pmInputValueClasses := by
  native_decide

/-- Both tids involved in the layer-12 alias are members of the q class. -/
theorem tids_5337_5345_mem_cuseqQClass :
    5337 ∈ cuseqQClass.tids ∧ 5345 ∈ cuseqQClass.tids := by
  native_decide

/-- Fidelity guard: the adjacent k tid is not accidentally merged into the q class. -/
theorem tid_5346_not_mem_cuseqQClass : 5346 ∉ cuseqQClass.tids := by
  native_decide

/-- Fidelity guard: the exact k class is separately generated on the SM side. -/
theorem cuseqKClass_mem_sm : cuseqKClass ∈ smInputValueClasses := by
  native_decide

/-- Fidelity guard: the exact k class is separately generated on the PM side. -/
theorem cuseqKClass_mem_pm : cuseqKClass ∈ pmInputValueClasses := by
  native_decide

/-- The nearby tid 5346 belongs to k, not q. -/
theorem tid_5346_mem_cuseqKClass : 5346 ∈ cuseqKClass.tids := by
  native_decide

/-- The generated q and k classes remain distinct. -/
theorem cuseqQClass_ne_cuseqKClass : cuseqQClass ≠ cuseqKClass := by
  native_decide

/-- The generated SM input contract identifies q tids 5337 and 5345. -/
theorem sm_cuseq_q_5337_eq_5345 (init : Store)
    (h : InputValueClassesHold smInputValueClasses init) :
    init 5337 = init 5345 := by
  exact h.eq_of_mem cuseqQClass_mem_sm tids_5337_5345_mem_cuseqQClass.1
    tids_5337_5345_mem_cuseqQClass.2

/-- The generated PM input contract identifies q tids 5337 and 5345. -/
theorem pm_cuseq_q_5337_eq_5345 (init : Store)
    (h : InputValueClassesHold pmInputValueClasses init) :
    init 5337 = init 5345 := by
  exact h.eq_of_mem cuseqQClass_mem_pm tids_5337_5345_mem_cuseqQClass.1
    tids_5337_5345_mem_cuseqQClass.2

/-- A concrete zero store witnessing simultaneous satisfiability of both generated
input-class contracts. -/
def zeroStore : Store := fun _ => zeroTensor []

/-- Nonvacuity guard for the generated SM and PM input-class contracts. -/
theorem zeroStore_respects_generated_classes :
    InputValueClassesHold smInputValueClasses zeroStore ∧
      InputValueClassesHold pmInputValueClasses zeroStore := by
  exact ⟨inputValueClassesHold_const _ _, inputValueClassesHold_const _ _⟩

/-- Existential form of the nonvacuity guard, convenient for contract audits. -/
theorem generated_input_value_classes_satisfiable :
    ∃ smInit pmInit : Store,
      InputValueClassesHold smInputValueClasses smInit ∧
        InputValueClassesHold pmInputValueClasses pmInit := by
  exact ⟨zeroStore, zeroStore, zeroStore_respects_generated_classes⟩

end TrainVerify.Denote.YOCInputValueClasses
