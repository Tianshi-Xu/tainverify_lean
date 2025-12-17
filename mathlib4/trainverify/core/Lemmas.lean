/-
Basic helper lemmas about the generic semantics. These mirror the facts used in the
original TrainVerify development but do not depend on any particular concrete graph.
-/

import Std.Data.HashMap.Lemmas
import Mathlib.Data.List.GetD
import trainverify.core.Semantics

open Std

universe u

namespace TrainVerify

variable {α : Type u}

-- ### Simple Boolean helpers
theorem outputsExist_nil (st : Store α) : outputsExist ([] : List Nat) st = true := by
  simp [outputsExist]

lemma outputsExist_cons (t : Nat) (ts : List Nat) (st : Store α) :
    outputsExist (t :: ts) st = (st.contains t && outputsExist ts st) := by
  simp [outputsExist, List.all_cons, Bool.and_eq_true]

lemma inputsReady_nil (inits : InitMap) (st : Store α) :
    inputsReady inits [] st = true := by
  simp [inputsReady]

lemma outputsExist_of_subset (ts us : List Nat) (st : Store α)
    (hsub : ∀ t ∈ ts, t ∈ us) (hus : outputsExist us st = true) :
    outputsExist ts st = true := by
  classical
  unfold outputsExist at hus ⊢
  have hAll : ∀ t ∈ us, st.contains t = true := by
    simpa [List.all_eq_true] using hus
  have hAll' : ∀ t ∈ ts, st.contains t = true := by
    intro t ht
    exact hAll t (hsub t ht)
  simpa [List.all_eq_true] using hAll'

lemma outputsExist_of_forall_contains (ts : List Nat) (st : Store α)
    (h : ∀ t ∈ ts, st.contains t = true) :
    outputsExist ts st = true := by
  classical
  unfold outputsExist
  simpa [List.all_eq_true] using h

lemma outputsExist_false_of_exists_missing (ts : List Nat) (st : Store α)
    (h : ∃ t ∈ ts, st.contains t = false) :
    outputsExist ts st = false := by
  classical
  unfold outputsExist
  refine List.all_eq_false.mpr ?_
  rcases h with ⟨t, ht_mem, ht_missing⟩
  refine ⟨t, ht_mem, ?_⟩
  simpa [ht_missing]

lemma inputsReady_of_forall_ready (inits : InitMap) (ts : List Nat) (st : Store α)
    (h : ∀ t ∈ ts, st.contains t = true ∨ inits.getD t false = true) :
    inputsReady inits ts st = true := by
  classical
  unfold inputsReady
  refine List.all_eq_true.mpr ?_
  intro t ht
  rcases h t ht with hcont | hinit
  · simp [hcont]
  · simp [hinit]

lemma inputsReady_of_forall_contains (inits : InitMap) (ts : List Nat)
    (st : Store α) (h : ∀ t ∈ ts, st.contains t = true) :
    inputsReady inits ts st = true :=
  inputsReady_of_forall_ready (inits := inits) (ts := ts) (st := st)
    (fun t ht => Or.inl (h t ht))

lemma inputsReady_true_iff (inits : InitMap) (ts : List Nat) (st : Store α) :
    inputsReady inits ts st = true ↔
      ∀ t ∈ ts, st.contains t = true ∨ inits.getD t false = true := by
  classical
  constructor
  · intro h
    unfold inputsReady at h
    have hAll := List.all_eq_true.mp h
    intro t ht
    have := hAll t ht
    by_cases hct : st.contains t = true
    · exact Or.inl hct
    · have : inits.getD t false = true := by
        simpa [hct] using this
      exact Or.inr this
  · intro h
    exact inputsReady_of_forall_ready (inits := inits) (ts := ts) (st := st) h

lemma inputsReady_false_of_exists_missing (inits : InitMap) (ts : List Nat)
    (st : Store α)
    (h : ∃ t ∈ ts, st.contains t = false ∧ inits.getD t false = false) :
    inputsReady inits ts st = false := by
  classical
  unfold inputsReady
  refine List.all_eq_false.mpr ?_
  rcases h with ⟨t, ht_mem, ht_store, ht_init⟩
  refine ⟨t, ht_mem, ?_⟩
  simp [ht_store, ht_init]

lemma inputsReady_mono (inits : InitMap) (ts : List Nat)
    {st st' : Store α}
    (hready : inputsReady inits ts st = true)
    (hle : ∀ k, st.contains k = true → st'.contains k = true) :
    inputsReady inits ts st' = true := by
  classical
  have hAll := (inputsReady_true_iff (inits := inits) (ts := ts) (st := st)).mp hready
  have hAll' : ∀ t ∈ ts, st'.contains t = true ∨ inits.getD t false = true := by
    intro t ht
    rcases hAll t ht with hct | hinit
    · exact Or.inl (hle t hct)
    · exact Or.inr hinit
  exact (inputsReady_true_iff (inits := inits) (ts := ts) (st := st')).mpr hAll'

lemma outputsExist_mono (ts : List Nat) {st st' : Store α}
    (h : outputsExist ts st = true)
    (hle : ∀ k, st.contains k = true → st'.contains k = true) :
    outputsExist ts st' = true := by
  classical
  unfold outputsExist at h ⊢
  have h_all : ∀ t ∈ ts, st.contains t = true := by
    simpa [List.all_eq_true] using h
  have h_all' : ∀ t ∈ ts, st'.contains t = true := by
    intro t ht
    exact hle t (h_all t ht)
  have h_bool : ts.all (fun t => st'.contains t) = true :=
    List.all_eq_true.mpr (by intro t ht; exact h_all' t ht)
  simpa [outputsExist] using h_bool

-- ### Store monotonicity lemmas

section StoreMonotonicity

variable {α : Type u}

lemma contains_insertTensor_self (st : Store α) (tid : Nat) (value : Mat α) :
    (st.insertTensor tid value).contains tid = true := by
  classical
  simpa [Store.insertTensor]
    using (Std.HashMap.contains_insert (m := st) (k := tid) (a := tid) (v := value))

lemma contains_insertTensor_of_contains (st : Store α) (tid tid' : Nat)
    (value : Mat α) (h : st.contains tid = true) :
    (st.insertTensor tid' value).contains tid = true := by
  classical
  simpa [Store.insertTensor, h]
    using (Std.HashMap.contains_insert (m := st) (k := tid') (a := tid) (v := value))

variable [Semiring α]

lemma fetchTensor_preserves_contains (env : Env α) (shapes : ShapeMap)
    (inits : InitMap) (tid req : Nat) (st : Store α)
    (h : st.contains tid = true) :
    (fetchTensor env shapes inits req st).2.contains tid = true := by
  classical
  unfold fetchTensor
  split <;> simp [h, contains_insertTensor_of_contains]

private lemma fetchMany_storeFold_aux (env : Env α) (shapes : ShapeMap)
    (inits : InitMap) (reqs : List Nat)
    (acc : List (Mat α)) (st : Store α) :
    (reqs.foldl
        (fun (acc', store) tid =>
          let (t, store') := fetchTensor env shapes inits tid store
          (acc' ++ [t], store'))
        (acc, st)).2
      =
      reqs.foldl
        (fun store tid => (fetchTensor env shapes inits tid store).2)
        st := by
  classical
  revert acc st
  induction reqs with
  | nil =>
      intro acc st
      simp
  | cons req rest ih =>
      intro acc st
      cases hfetch : fetchTensor env shapes inits req st with
      | mk t st₁ =>
          simpa [List.foldl, hfetch] using ih (acc ++ [t]) st₁

lemma fetchMany_storeFold (env : Env α) (shapes : ShapeMap)
    (inits : InitMap) (reqs : List Nat) (st : Store α) :
    (fetchMany env shapes inits reqs st).2 =
      reqs.foldl
        (fun store tid => (fetchTensor env shapes inits tid store).2)
        st := by
  classical
  simpa [fetchMany]
    using fetchMany_storeFold_aux (env := env) (shapes := shapes) (inits := inits)
      (reqs := reqs) (acc := ([] : List (Mat α))) (st := st)

lemma fetchMany_cons_snd (env : Env α) (shapes : ShapeMap)
    (inits : InitMap) (req : Nat) (rest : List Nat) (st : Store α) :
    (fetchMany env shapes inits (req :: rest) st).2 =
      (fetchMany env shapes inits rest (fetchTensor env shapes inits req st).2).2 := by
  classical
  simp [fetchMany_storeFold, List.foldl]

lemma fetchMany_preserves_contains (env : Env α) (shapes : ShapeMap)
    (inits : InitMap) (reqs : List Nat) (tid : Nat) (st : Store α)
    (h : st.contains tid = true) :
    (fetchMany env shapes inits reqs st).2.contains tid = true := by
  classical
  revert st h
  induction reqs with
  | nil =>
      intro st h
      simpa [fetchMany] using h
  | cons req rest ih =>
      intro st h
      have hstep :=
        fetchTensor_preserves_contains (env := env) (shapes := shapes)
          (inits := inits) (tid := tid) (req := req) (st := st) h
      have hrest := ih _ hstep
      simpa [fetchMany_cons_snd]
        using hrest

lemma runNode_preserves_contains (env : Env α) (shapes : ShapeMap)
    (inits : InitMap) (n : Node) (st : Store α) (tid : Nat)
    (h : st.contains tid = true) :
    ((Runtime.mkStandard env shapes inits).runNode n st).contains tid = true := by
  classical
  cases n with
  | mk op inputs outputs =>
      cases op with
      | dataloader =>
          by_cases hex : outputsExist outputs st = true
          · simpa [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hex, h]
          · cases outputs with
            | nil =>
                simpa [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hex, h]
            | cons out rest =>
                simpa [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hex,
                  contains_insertTensor_of_contains, h]
      | fwLinear =>
          by_cases hready : inputsReady inits inputs st = true
          · by_cases hmiss : outputsExist outputs st = true
            · simpa [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready,
                hmiss, h]
            ·
              simp [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready,
                hmiss, fetchTensor_preserves_contains, contains_insertTensor_of_contains, h]
          · simpa [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready]
      | bwLinear =>
          by_cases hready : inputsReady inits inputs st = true
          · by_cases hmiss : outputsExist outputs st = true
            · simpa [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready,
                hmiss, h]
            ·
              set goId := inputs.getD 0 0
              set xId := inputs.getD 1 0
              set wId := inputs.getD 2 0
              set gxId := outputs.getD 0 0
              set gwId := outputs.getD 1 0
              set fetchGo := fetchTensor env shapes inits goId st
              set st₁ := fetchGo.2
              have h₁ : st₁.contains tid = true := by
                simpa [st₁, fetchGo]
                  using fetchTensor_preserves_contains (env := env) (shapes := shapes)
                    (inits := inits) (tid := tid) (req := goId) (st := st) h
              set fetchX := fetchTensor env shapes inits xId st₁
              set st₂ := fetchX.2
              have h₂ : st₂.contains tid = true := by
                simpa [st₂, fetchX]
                  using fetchTensor_preserves_contains (env := env) (shapes := shapes)
                    (inits := inits) (tid := tid) (req := xId) (st := st₁) h₁
              set fetchW := fetchTensor env shapes inits wId st₂
              set st₃ := fetchW.2
              have h₃ : st₃.contains tid = true := by
                simpa [st₃, fetchW]
                  using fetchTensor_preserves_contains (env := env) (shapes := shapes)
                    (inits := inits) (tid := tid) (req := wId) (st := st₂) h₂
              set st₄ := st₃.insertTensor gxId (matmul fetchGo.1 fetchW.1)
              have h₄ : st₄.contains tid = true := by
                simpa [st₄]
                  using contains_insertTensor_of_contains (st := st₃) (tid := tid)
                    (tid' := gxId) (value := matmul fetchGo.1 fetchW.1) h₃
              set st₅ := st₄.insertTensor gwId (matmul (transpose fetchX.1) fetchGo.1)
              have h₅ : st₅.contains tid = true := by
                simpa [st₅]
                  using contains_insertTensor_of_contains (st := st₄) (tid := tid)
                    (tid' := gwId) (value := matmul (transpose fetchX.1) fetchGo.1) h₄
              simpa [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready,
                hmiss, goId, xId, wId, gxId, gwId, fetchGo, st₁, fetchX, st₂, fetchW, st₃,
                st₄, st₅]
                using h₅
          · simpa [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready]
      | fwSum =>
          by_cases hready : inputsReady inits inputs st = true
          · by_cases hmiss : outputsExist outputs st = true
            · simpa [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready,
                hmiss, h]
            ·
              simp [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready,
                hmiss, fetchTensor_preserves_contains, contains_insertTensor_of_contains, h]
          · simpa [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready]
      | bwSum =>
          by_cases hready : inputsReady inits inputs st = true
          · by_cases hmiss : outputsExist outputs st = true
            · simpa [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready,
                hmiss, h]
            ·
              simp [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready,
                hmiss, fetchTensor_preserves_contains, contains_insertTensor_of_contains, h]
          · simpa [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready]
      | chunk dim idx =>
          by_cases hready : inputsReady inits inputs st = true
          · by_cases hmiss : outputsExist outputs st = true
            · simpa [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready,
                hmiss, h]
            ·
              simp [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready,
                hmiss, fetchTensor_preserves_contains, contains_insertTensor_of_contains, h]
          · simpa [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready]
      | allGather dim =>
          by_cases hready : inputsReady inits inputs st = true
          · by_cases hmiss : outputsExist outputs st = true
            · simpa [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready,
                hmiss, h]
            ·
              simp [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready,
                hmiss, fetchMany_preserves_contains, contains_insertTensor_of_contains, h]
          · simpa [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready]
      | allReduce =>
          by_cases hready : inputsReady inits inputs st = true
          · by_cases hmiss : outputsExist outputs st = true
            · simpa [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready,
                hmiss, h]
            ·
              simp [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready,
                hmiss, fetchMany_preserves_contains, contains_insertTensor_of_contains, h]
          · simpa [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready]
      | custom _ =>
          simpa [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, h]

end StoreMonotonicity

-- ### Run-time semantics lemmas

variable [Semiring α]

/-- Canonical post-state for a dataloader node once guards pass. -/
def dataloaderResult
    (env : Env α) (outs : List Nat) (st : Store α) : Store α :=
  match outs with
  | [] => st
  | out :: _ => st.insertTensor out (env.get out)

/-- Canonical post-state for a forward linear node. -/
def fwLinearResult
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (ins outs : List Nat) (st : Store α) : Store α :=
  let xId := ins.getD 0 0
  let wId := ins.getD 1 0
  let outId := outs.getD 0 0
  let (x, st₁) := fetchTensor env shapes inits xId st
  let (w, st₂) := fetchTensor env shapes inits wId st₁
  st₂.insertTensor outId (matmul x (transpose w))

/-- Canonical post-state for a backward linear node. -/
def bwLinearResult
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (ins outs : List Nat) (st : Store α) : Store α :=
  let goId := ins.getD 0 0
  let xId := ins.getD 1 0
  let wId := ins.getD 2 0
  let gxId := outs.getD 0 0
  let gwId := outs.getD 1 0
  let (go, st₁) := fetchTensor env shapes inits goId st
  let (x, st₂) := fetchTensor env shapes inits xId st₁
  let (w, st₃) := fetchTensor env shapes inits wId st₂
  let gx := matmul go w
  let gw := matmul (transpose x) go
  let st₄ := st₃.insertTensor gxId gx
  st₄.insertTensor gwId gw

/-- Canonical post-state for a forward sum node. -/
def fwSumResult
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (ins outs : List Nat) (st : Store α) : Store α :=
  let xId := ins.getD 0 0
  let outId := outs.getD 0 0
  let (x, st₁) := fetchTensor env shapes inits xId st
  st₁.insertTensor outId [[sumAll x]]

/-- Canonical post-state for a backward sum node. -/
def bwSumResult
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (ins outs : List Nat) (st : Store α) : Store α :=
  let gId := ins.getD 0 0
  let xId := ins.getD 1 0
  let outId := outs.getD 0 0
  let (g, st₁) := fetchTensor env shapes inits gId st
  let (x, st₂) := fetchTensor env shapes inits xId st₁
  let scalar :=
    match g.head? with
    | some row => row.headD 0
    | none => 0
  let gx := x.map (fun row => row.map (fun _ => scalar))
  st₂.insertTensor outId gx

/-- Canonical post-state for a chunk node once guards pass. -/
def chunkResult
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (dim idx : Nat) (ins outs : List Nat) (st : Store α) : Store α :=
  let srcId := ins.getD 0 0
  let outId := outs.getD 0 0
  let (src, st₁) := fetchTensor env shapes inits srcId st
  let shpOut := shapes.getD outId []
  let size :=
    if shpOut.length = 2 then
      if dim = 0 then shpOut.getD 0 0 else shpOut.getD 1 0
    else if shpOut.length = 1 then shpOut.getD 0 0 else 0
  let start := idx * size
  let part := chunkBy src dim start size
  st₁.insertTensor outId part

/-- Canonical post-state for an allGather node once guards pass. -/
def allGatherResult
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (dim : Nat) (ins outs : List Nat) (st : Store α) : Store α :=
  let outId := outs.getD 0 0
  let (parts, st₁) := fetchMany env shapes inits ins st
  st₁.insertTensor outId (gatherBy dim parts)

/-- Canonical post-state for an allReduce node once guards pass. -/
def allReduceResult
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (ins outs : List Nat) (st : Store α) : Store α :=
  let outId := outs.getD 0 0
  let (parts, st₁) := fetchMany env shapes inits ins st
  st₁.insertTensor outId (allReduce parts)

/-- Unified post-state description for the operations handled in this file. -/
def nodeProgressResult
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (n : Node) (st : Store α) : Store α :=
  match n.op with
  | Op.dataloader => dataloaderResult env n.outputs st
  | Op.fwLinear => fwLinearResult env shapes inits n.inputs n.outputs st
  | Op.bwLinear => bwLinearResult env shapes inits n.inputs n.outputs st
  | Op.fwSum => fwSumResult env shapes inits n.inputs n.outputs st
  | Op.bwSum => bwSumResult env shapes inits n.inputs n.outputs st
  | Op.chunk dim idx => chunkResult env shapes inits dim idx n.inputs n.outputs st
  | Op.allGather dim => allGatherResult env shapes inits dim n.inputs n.outputs st
  | Op.allReduce => allReduceResult env shapes inits n.inputs n.outputs st
  | _ => (Runtime.mkStandard env shapes inits).runNode n st

/-- Progress witness for a node: inputs are ready, outputs missing, and execution matches `nodeProgressResult`. -/
structure NodeProgress (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (n : Node) (st : Store α) : Prop where
  ready : inputsReady inits n.inputs st = true
  missing : outputsExist n.outputs st = false
  result : (Runtime.mkStandard env shapes inits).runNode n st =
    nodeProgressResult env shapes inits n st

lemma runNode_noop_if_done
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (n : Node) (st : Store α)
    (h : outputsExist n.outputs st = true) :
    (Runtime.mkStandard env shapes inits).runNode n st = st := by
  cases n with
  | mk op inputs outputs =>
    simp [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, h]

lemma runNode_noop_if_not_ready
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (op : Op) (ins outs : List Nat) (st : Store α)
    (hready : inputsReady inits ins st = false) (hnd : op ≠ Op.dataloader) :
    (Runtime.mkStandard env shapes inits).runNode ⟨op, ins, outs⟩ st = st := by
  cases op with
  | dataloader => cases hnd rfl
  | fwLinear => simp [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready]
  | bwLinear => simp [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready]
  | fwSum => simp [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready]
  | bwSum => simp [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready]
  | chunk _ _ => simp [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready]
  | allReduce => simp [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready]
  | allGather _ => simp [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready]
  | custom _ => simp [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready]

lemma outputsExist_single_insert (st : Store α) (tid : Nat) (value : Mat α) :
    outputsExist [tid] (st.insertTensor tid value) = true := by
  classical
  simp [outputsExist, Store.insertTensor, List.all_cons]

lemma runNode_dataloader_insert
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (out : Nat) (restOuts : List Nat) (st : Store α)
    (hmiss : outputsExist (out :: restOuts) st = false) :
    (Runtime.mkStandard env shapes inits).runNode ⟨Op.dataloader, [], out :: restOuts⟩ st =
      dataloaderResult env (out :: restOuts) st := by
  simp [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hmiss, dataloaderResult]

lemma runNode_fwLinear_eval
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (ins outs : List Nat) (st : Store α)
    (hready : inputsReady inits ins st = true)
    (hmiss : outputsExist outs st = false) :
    (Runtime.mkStandard env shapes inits).runNode ⟨Op.fwLinear, ins, outs⟩ st =
      fwLinearResult env shapes inits ins outs st := by
  classical
  simp [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready, hmiss, fwLinearResult]

lemma runNode_bwLinear_eval
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (ins outs : List Nat) (st : Store α)
    (hready : inputsReady inits ins st = true)
    (hmiss : outputsExist outs st = false) :
    (Runtime.mkStandard env shapes inits).runNode ⟨Op.bwLinear, ins, outs⟩ st =
      bwLinearResult env shapes inits ins outs st := by
  classical
  simp [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready, hmiss, bwLinearResult]

lemma runNode_fwSum_eval
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (ins outs : List Nat) (st : Store α)
    (hready : inputsReady inits ins st = true)
    (hmiss : outputsExist outs st = false) :
    (Runtime.mkStandard env shapes inits).runNode ⟨Op.fwSum, ins, outs⟩ st =
      fwSumResult env shapes inits ins outs st := by
  classical
  simp [Runtime.runNode, Runtime.mkStandard, standardOps, evalStandard, hready, hmiss, fwSumResult]

lemma runNode_bwSum_eval
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (ins outs : List Nat) (st : Store α)
    (hready : inputsReady inits ins st = true)
    (hmiss : outputsExist outs st = false) :
    (Runtime.mkStandard env shapes inits).runNode ⟨Op.bwSum, ins, outs⟩ st =
      bwSumResult env shapes inits ins outs st := by
  classical
  unfold Runtime.runNode Runtime.mkStandard standardOps
  simp [evalStandard, hready, hmiss, bwSumResult]
  rfl

lemma runNode_chunk_eval
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (dim idx : Nat) (ins outs : List Nat) (st : Store α)
    (hready : inputsReady inits ins st = true)
    (hmiss : outputsExist outs st = false) :
    (Runtime.mkStandard env shapes inits).runNode ⟨Op.chunk dim idx, ins, outs⟩ st =
      chunkResult env shapes inits dim idx ins outs st := by
  classical
  unfold Runtime.runNode Runtime.mkStandard standardOps
  simp [evalStandard, hready, hmiss, chunkResult]

lemma runNode_allGather_eval
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (dim : Nat) (ins outs : List Nat) (st : Store α)
    (hready : inputsReady inits ins st = true)
    (hmiss : outputsExist outs st = false) :
    (Runtime.mkStandard env shapes inits).runNode ⟨Op.allGather dim, ins, outs⟩ st =
      allGatherResult env shapes inits dim ins outs st := by
  classical
  unfold Runtime.runNode Runtime.mkStandard standardOps
  simp [evalStandard, hready, hmiss, allGatherResult]

lemma runNode_allReduce_eval
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (ins outs : List Nat) (st : Store α)
    (hready : inputsReady inits ins st = true)
    (hmiss : outputsExist outs st = false) :
    (Runtime.mkStandard env shapes inits).runNode ⟨Op.allReduce, ins, outs⟩ st =
      allReduceResult env shapes inits ins outs st := by
  classical
  unfold Runtime.runNode Runtime.mkStandard standardOps
  simp [evalStandard, hready, hmiss, allReduceResult]

lemma nodeProgress_dataloader
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (out : Nat) (restOuts : List Nat) (st : Store α)
    (hmiss : outputsExist (out :: restOuts) st = false) :
    NodeProgress env shapes inits ⟨Op.dataloader, [], out :: restOuts⟩ st := by
  classical
  refine ⟨?_, hmiss, ?_⟩
  · simpa using (inputsReady_nil (inits := inits) (st := st))
  · have := runNode_dataloader_insert (env := env) (shapes := shapes) (inits := inits)
        (out := out) (restOuts := restOuts) (st := st) hmiss
    simpa [nodeProgressResult, dataloaderResult] using this

lemma nodeProgress_chunk
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (dim idx : Nat) (ins outs : List Nat) (st : Store α)
    (hready : inputsReady inits ins st = true)
    (hmiss : outputsExist outs st = false) :
    NodeProgress env shapes inits ⟨Op.chunk dim idx, ins, outs⟩ st := by
  classical
  refine ⟨hready, hmiss, ?_⟩
  simpa [nodeProgressResult] using
    runNode_chunk_eval (env := env) (shapes := shapes) (inits := inits)
      (dim := dim) (idx := idx) (ins := ins) (outs := outs) (st := st) hready hmiss

lemma nodeProgress_allGather
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (dim : Nat) (ins outs : List Nat) (st : Store α)
    (hready : inputsReady inits ins st = true)
    (hmiss : outputsExist outs st = false) :
    NodeProgress env shapes inits ⟨Op.allGather dim, ins, outs⟩ st := by
  classical
  refine ⟨hready, hmiss, ?_⟩
  simpa [nodeProgressResult] using
    runNode_allGather_eval (env := env) (shapes := shapes) (inits := inits)
      (dim := dim) (ins := ins) (outs := outs) (st := st) hready hmiss

lemma nodeProgress_allReduce
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (ins outs : List Nat) (st : Store α)
    (hready : inputsReady inits ins st = true)
    (hmiss : outputsExist outs st = false) :
    NodeProgress env shapes inits ⟨Op.allReduce, ins, outs⟩ st := by
  classical
  refine ⟨hready, hmiss, ?_⟩
  simpa [nodeProgressResult] using
    runNode_allReduce_eval (env := env) (shapes := shapes) (inits := inits)
      (ins := ins) (outs := outs) (st := st) hready hmiss

lemma nodeProgress_fwLinear
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (ins outs : List Nat) (st : Store α)
    (hready : inputsReady inits ins st = true)
    (hmiss : outputsExist outs st = false) :
    NodeProgress env shapes inits ⟨Op.fwLinear, ins, outs⟩ st := by
  classical
  refine ⟨hready, hmiss, ?_⟩
  simpa [nodeProgressResult] using
    runNode_fwLinear_eval (env := env) (shapes := shapes) (inits := inits)
      (ins := ins) (outs := outs) (st := st) hready hmiss

lemma nodeProgress_bwLinear
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (ins outs : List Nat) (st : Store α)
    (hready : inputsReady inits ins st = true)
    (hmiss : outputsExist outs st = false) :
    NodeProgress env shapes inits ⟨Op.bwLinear, ins, outs⟩ st := by
  classical
  refine ⟨hready, hmiss, ?_⟩
  simpa [nodeProgressResult] using
    runNode_bwLinear_eval (env := env) (shapes := shapes) (inits := inits)
      (ins := ins) (outs := outs) (st := st) hready hmiss

lemma nodeProgress_fwSum
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (ins outs : List Nat) (st : Store α)
    (hready : inputsReady inits ins st = true)
    (hmiss : outputsExist outs st = false) :
    NodeProgress env shapes inits ⟨Op.fwSum, ins, outs⟩ st := by
  classical
  refine ⟨hready, hmiss, ?_⟩
  simpa [nodeProgressResult] using
    runNode_fwSum_eval (env := env) (shapes := shapes) (inits := inits)
      (ins := ins) (outs := outs) (st := st) hready hmiss

lemma nodeProgress_bwSum
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (ins outs : List Nat) (st : Store α)
    (hready : inputsReady inits ins st = true)
    (hmiss : outputsExist outs st = false) :
    NodeProgress env shapes inits ⟨Op.bwSum, ins, outs⟩ st := by
  classical
  refine ⟨hready, hmiss, ?_⟩
  simpa [nodeProgressResult] using
    runNode_bwSum_eval (env := env) (shapes := shapes) (inits := inits)
      (ins := ins) (outs := outs) (st := st) hready hmiss

section NodeProgressOutputPresence

variable [Semiring α]

lemma dataloaderResult_contains
    (env : Env α) (outs : List Nat) (st : Store α) (tid : Nat)
    (hout : outs = [tid]) :
    (dataloaderResult env outs st).contains tid = true := by
  classical
  subst hout
  unfold dataloaderResult
  simp [contains_insertTensor_self]

lemma fwLinearResult_contains
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (ins outs : List Nat) (st : Store α) (tid : Nat)
    (hout : outs = [tid]) :
    (fwLinearResult env shapes inits ins outs st).contains tid = true := by
  classical
  subst hout
  unfold fwLinearResult
  cases hfetchX : fetchTensor env shapes inits (ins.getD 0 0) st with
  | mk x st₁ =>
      cases hfetchW : fetchTensor env shapes inits (ins.getD 1 0) st₁ with
        | mk w st₂ =>
          simp [hfetchX, hfetchW, List.getD_cons_zero, contains_insertTensor_self]

lemma fwSumResult_contains
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (ins outs : List Nat) (st : Store α) (tid : Nat)
    (hout : outs = [tid]) :
    (fwSumResult env shapes inits ins outs st).contains tid = true := by
  classical
  subst hout
  unfold fwSumResult
  cases fetchTensor env shapes inits (ins.getD 0 0) st with
  | mk _ st₁ =>
  simp [List.getD_cons_zero, contains_insertTensor_self]

lemma bwSumResult_contains
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (ins outs : List Nat) (st : Store α) (tid : Nat)
    (hout : outs = [tid]) :
    (bwSumResult env shapes inits ins outs st).contains tid = true := by
  classical
  subst hout
  unfold bwSumResult
  cases fetchTensor env shapes inits (ins.getD 0 0) st with
  | mk _ st₁ =>
      cases fetchTensor env shapes inits (ins.getD 1 0) st₁ with
        | mk _ st₂ =>
          simp [List.getD_cons_zero, contains_insertTensor_self]

lemma chunkResult_contains
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (dim idx : Nat) (ins outs : List Nat) (st : Store α) (tid : Nat)
    (hout : outs = [tid]) :
    (chunkResult env shapes inits dim idx ins outs st).contains tid = true := by
  classical
  subst hout
  unfold chunkResult
  cases fetchTensor env shapes inits (ins.getD 0 0) st with
  | mk _ st₁ =>
  simp [List.getD_cons_zero, contains_insertTensor_self]

lemma allGatherResult_contains
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (dim : Nat) (ins outs : List Nat) (st : Store α) (tid : Nat)
    (hout : outs = [tid]) :
    (allGatherResult env shapes inits dim ins outs st).contains tid = true := by
  classical
  subst hout
  unfold allGatherResult
  cases fetchMany env shapes inits ins st with
  | mk _ st₁ =>
  simp [contains_insertTensor_self, List.getD_cons_zero]

lemma allReduceResult_contains
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (ins outs : List Nat) (st : Store α) (tid : Nat)
    (hout : outs = [tid]) :
    (allReduceResult env shapes inits ins outs st).contains tid = true := by
  classical
  subst hout
  unfold allReduceResult
  cases fetchMany env shapes inits ins st with
  | mk _ st₁ =>
  simp [contains_insertTensor_self, List.getD_cons_zero]

lemma bwLinearResult_contains_fst
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (ins outs : List Nat) (st : Store α) (tid₀ tid₁ : Nat)
    (hout : outs = [tid₀, tid₁]) :
    (bwLinearResult env shapes inits ins outs st).contains tid₀ = true := by
  classical
  subst hout
  unfold bwLinearResult
  cases fetchTensor env shapes inits (ins.getD 0 0) st with
  | mk _ st₁ =>
      cases fetchTensor env shapes inits (ins.getD 1 0) st₁ with
      | mk _ st₂ =>
          cases fetchTensor env shapes inits (ins.getD 2 0) st₂ with
            | mk _ st₃ =>
              simp [List.getD_cons_zero, List.getD_cons_succ, contains_insertTensor_self]

lemma bwLinearResult_contains_snd
    (env : Env α) (shapes : ShapeMap) (inits : InitMap)
    (ins outs : List Nat) (st : Store α) (tid₀ tid₁ : Nat)
    (hout : outs = [tid₀, tid₁]) :
    (bwLinearResult env shapes inits ins outs st).contains tid₁ = true := by
  classical
  subst hout
  unfold bwLinearResult
  cases fetchTensor env shapes inits (ins.getD 0 0) st with
  | mk _ st₁ =>
      cases fetchTensor env shapes inits (ins.getD 1 0) st₁ with
      | mk _ st₂ =>
          cases fetchTensor env shapes inits (ins.getD 2 0) st₂ with
              | mk _ st₃ =>
                simp [List.getD_cons_zero, List.getD_cons_succ, contains_insertTensor_self]

lemma nodeProgress_dataloader_output_present
    {ins outs : List Nat} {st : Store α} {env : Env α}
    {shapes : ShapeMap} {inits : InitMap} {tid : Nat}
    (h : NodeProgress env shapes inits ⟨Op.dataloader, ins, outs⟩ st)
    (hout : outs = [tid]) :
    ((Runtime.mkStandard env shapes inits).runNode ⟨Op.dataloader, ins, outs⟩ st).contains tid = true := by
  classical
  have hnp :
      (nodeProgressResult env shapes inits ⟨Op.dataloader, ins, outs⟩ st).contains tid = true := by
    simpa [nodeProgressResult, hout] using
      dataloaderResult_contains (env := env) (outs := outs) (st := st) (tid := tid) (hout := hout)
  have hcontains := congrArg (fun store => store.contains tid) h.result
  simpa only [hcontains] using hnp

lemma nodeProgress_fwLinear_output_present
    {ins outs : List Nat} {st : Store α} {env : Env α}
    {shapes : ShapeMap} {inits : InitMap} {tid : Nat}
    (h : NodeProgress env shapes inits ⟨Op.fwLinear, ins, outs⟩ st)
    (hout : outs = [tid]) :
    ((Runtime.mkStandard env shapes inits).runNode ⟨Op.fwLinear, ins, outs⟩ st).contains tid = true := by
  classical
  have hnp :
      (nodeProgressResult env shapes inits ⟨Op.fwLinear, ins, outs⟩ st).contains tid = true := by
    simpa [nodeProgressResult, hout]
      using fwLinearResult_contains (env := env) (shapes := shapes) (inits := inits)
        (ins := ins) (outs := outs) (st := st) (tid := tid) (hout := hout)
  have hcontains := congrArg (fun store => store.contains tid) h.result
  simpa only [hcontains] using hnp

lemma nodeProgress_fwSum_output_present
    {ins outs : List Nat} {st : Store α} {env : Env α}
    {shapes : ShapeMap} {inits : InitMap} {tid : Nat}
    (h : NodeProgress env shapes inits ⟨Op.fwSum, ins, outs⟩ st)
    (hout : outs = [tid]) :
    ((Runtime.mkStandard env shapes inits).runNode ⟨Op.fwSum, ins, outs⟩ st).contains tid = true := by
  classical
  have hnp :
      (nodeProgressResult env shapes inits ⟨Op.fwSum, ins, outs⟩ st).contains tid = true := by
    simpa [nodeProgressResult, hout]
      using fwSumResult_contains (env := env) (shapes := shapes) (inits := inits)
        (ins := ins) (outs := outs) (st := st) (tid := tid) (hout := hout)
  have hcontains := congrArg (fun store => store.contains tid) h.result
  simpa only [hcontains] using hnp

lemma nodeProgress_bwSum_output_present
    {ins outs : List Nat} {st : Store α} {env : Env α}
    {shapes : ShapeMap} {inits : InitMap} {tid : Nat}
    (h : NodeProgress env shapes inits ⟨Op.bwSum, ins, outs⟩ st)
    (hout : outs = [tid]) :
    ((Runtime.mkStandard env shapes inits).runNode ⟨Op.bwSum, ins, outs⟩ st).contains tid = true := by
  classical
  have hnp :
      (nodeProgressResult env shapes inits ⟨Op.bwSum, ins, outs⟩ st).contains tid = true := by
    simpa [nodeProgressResult, hout]
      using bwSumResult_contains (env := env) (shapes := shapes) (inits := inits)
        (ins := ins) (outs := outs) (st := st) (tid := tid) (hout := hout)
  have hcontains := congrArg (fun store => store.contains tid) h.result
  simpa only [hcontains] using hnp

lemma nodeProgress_chunk_output_present
    {ins outs : List Nat} {st : Store α} {env : Env α}
    {shapes : ShapeMap} {inits : InitMap} {tid : Nat} {dim idx : Nat}
    (h : NodeProgress env shapes inits ⟨Op.chunk dim idx, ins, outs⟩ st)
    (hout : outs = [tid]) :
    ((Runtime.mkStandard env shapes inits).runNode ⟨Op.chunk dim idx, ins, outs⟩ st).contains tid = true := by
  classical
  have hnp :
      (nodeProgressResult env shapes inits ⟨Op.chunk dim idx, ins, outs⟩ st).contains tid = true := by
    simpa [nodeProgressResult, hout]
      using chunkResult_contains (env := env) (shapes := shapes) (inits := inits)
        (dim := dim) (idx := idx) (ins := ins) (outs := outs) (st := st) (tid := tid) (hout := hout)
  have hcontains := congrArg (fun store => store.contains tid) h.result
  simpa only [hcontains] using hnp

lemma nodeProgress_allGather_output_present
    {ins outs : List Nat} {st : Store α} {env : Env α}
    {shapes : ShapeMap} {inits : InitMap} {tid : Nat} {dim : Nat}
    (h : NodeProgress env shapes inits ⟨Op.allGather dim, ins, outs⟩ st)
    (hout : outs = [tid]) :
    ((Runtime.mkStandard env shapes inits).runNode ⟨Op.allGather dim, ins, outs⟩ st).contains tid = true := by
  classical
  have hnp :
      (nodeProgressResult env shapes inits ⟨Op.allGather dim, ins, outs⟩ st).contains tid = true := by
    simpa [nodeProgressResult, hout]
      using allGatherResult_contains (env := env) (shapes := shapes) (inits := inits)
        (dim := dim) (ins := ins) (outs := outs) (st := st) (tid := tid) (hout := hout)
  have hcontains := congrArg (fun store => store.contains tid) h.result
  simpa only [hcontains] using hnp

lemma nodeProgress_allReduce_output_present
    {ins outs : List Nat} {st : Store α} {env : Env α}
    {shapes : ShapeMap} {inits : InitMap} {tid : Nat}
    (h : NodeProgress env shapes inits ⟨Op.allReduce, ins, outs⟩ st)
    (hout : outs = [tid]) :
    ((Runtime.mkStandard env shapes inits).runNode ⟨Op.allReduce, ins, outs⟩ st).contains tid = true := by
  classical
  have hnp :
      (nodeProgressResult env shapes inits ⟨Op.allReduce, ins, outs⟩ st).contains tid = true := by
    simpa [nodeProgressResult, hout]
      using allReduceResult_contains (env := env) (shapes := shapes) (inits := inits)
        (ins := ins) (outs := outs) (st := st) (tid := tid) (hout := hout)
  have hcontains := congrArg (fun store => store.contains tid) h.result
  simpa only [hcontains] using hnp

lemma nodeProgress_bwLinear_first_output_present
    {ins outs : List Nat} {st : Store α} {env : Env α}
    {shapes : ShapeMap} {inits : InitMap} {tid₀ tid₁ : Nat}
    (h : NodeProgress env shapes inits ⟨Op.bwLinear, ins, outs⟩ st)
    (hout : outs = [tid₀, tid₁]) :
    ((Runtime.mkStandard env shapes inits).runNode ⟨Op.bwLinear, ins, outs⟩ st).contains tid₀ = true := by
  classical
  have hnp :
      (nodeProgressResult env shapes inits ⟨Op.bwLinear, ins, outs⟩ st).contains tid₀ = true := by
    simpa [nodeProgressResult, hout]
      using bwLinearResult_contains_fst (env := env) (shapes := shapes) (inits := inits)
        (ins := ins) (outs := outs) (st := st) (tid₀ := tid₀) (tid₁ := tid₁) (hout := hout)
  have hcontains := congrArg (fun store => store.contains tid₀) h.result
  simpa only [hcontains] using hnp

lemma nodeProgress_bwLinear_second_output_present
    {ins outs : List Nat} {st : Store α} {env : Env α}
    {shapes : ShapeMap} {inits : InitMap} {tid₀ tid₁ : Nat}
    (h : NodeProgress env shapes inits ⟨Op.bwLinear, ins, outs⟩ st)
    (hout : outs = [tid₀, tid₁]) :
    ((Runtime.mkStandard env shapes inits).runNode ⟨Op.bwLinear, ins, outs⟩ st).contains tid₁ = true := by
  classical
  have hnp :
      (nodeProgressResult env shapes inits ⟨Op.bwLinear, ins, outs⟩ st).contains tid₁ = true := by
    simpa [nodeProgressResult, hout]
      using bwLinearResult_contains_snd (env := env) (shapes := shapes) (inits := inits)
        (ins := ins) (outs := outs) (st := st) (tid₀ := tid₀) (tid₁ := tid₁) (hout := hout)
  have hcontains := congrArg (fun store => store.contains tid₁) h.result
  simpa only [hcontains] using hnp

end NodeProgressOutputPresence

end TrainVerify
