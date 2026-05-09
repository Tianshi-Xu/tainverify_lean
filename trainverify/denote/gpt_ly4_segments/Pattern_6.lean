/- Auto-generated pattern proof file.
   Pattern: 6
   Hash: 50d559b40c026d8e
   Goals: 6, 7, 32, 58, 83
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_6_goalIds : List Nat := [6, 7, 32, 58, 83]
inductive pattern_6_target : Prop → Prop
  | goal_6 : pattern_6_target goal_6_stmt
  | goal_7 : pattern_6_target goal_7_stmt
  | goal_32 : pattern_6_target goal_32_stmt
  | goal_58 : pattern_6_target goal_58_stmt
  | goal_83 : pattern_6_target goal_83_stmt

def pattern_6_stmt : Prop :=
  ∀ {target : Prop}, pattern_6_target target → target

set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

/-! ## Helper lemmas

Pointwise valAt characterizations of `chunkPrimDimN` along dim 1 for the
shape used in this pattern (`x : [1, 8, 32]` sharded into 4 pieces
`[1, 2, 32]`). These are the building blocks for the `fw_linear`
distribution helper used by `prove_pattern_6`. -/

private lemma chunk1_x_1_8_32_shape (x : Tensor) (r : Nat)
    (hx : x.shape = [1, 8, 32]) (hr : r < 4) :
    (chunkPrimDimN 1 4 r x).shape = [1, 2, 32] := by
  rw [chunkPrimDimN_shape 1 4 r _ _ hx (by omega)]
  simp [List.set, List.getD]

private lemma chunk1_x_1_8_32_valAt (x : Tensor) (r : Nat)
    (hx : x.shape = [1, 8, 32]) (hr : r < 4)
    (jLocal : Nat) (k : Nat) (hjLocal : jLocal < 2) (hk : k < 32) :
    valAt (chunkPrimDimN 1 4 r x) (jLocal * 32 + k) =
      valAt x ((r * 2 + jLocal) * 32 + k) := by
  have hchunk_shape : (chunkPrimDimN 1 4 r x).shape = [1, 2, 32] :=
    chunk1_x_1_8_32_shape x r hx hr
  have hflat_lt : jLocal * 32 + k < prodShape (chunkPrimDimN 1 4 r x).shape := by
    rw [hchunk_shape]; simp [prodShape]; omega
  rw [valAt_of_lt _ _ hflat_lt]
  unfold chunkPrimDimN Tensor.mkShape
  simp only [hx, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl, List.getD,
    show (4 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 0 by omega,
    show (32 : Nat) ≠ 0 by omega, show (8 : Nat) ≠ 0 by omega, ite_false]
  have hr' : r % 4 = r := Nat.mod_eq_of_lt hr
  have h_lt : jLocal * 32 + k < 64 := by omega
  have h_div : (jLocal * 32 + k) / 64 = 0 := Nat.div_eq_of_lt h_lt
  have h_mod : (jLocal * 32 + k) % 64 = jLocal * 32 + k := Nat.mod_eq_of_lt h_lt
  have h_div32 : (jLocal * 32 + k) / 32 = jLocal := by
    have heq : jLocal * 32 + k = k + 32 * jLocal := by ring
    rw [heq, Nat.add_mul_div_left _ _ (by norm_num : (0:Nat) < 32),
        Nat.div_eq_of_lt hk, Nat.zero_add]
  have h_mod32 : (jLocal * 32 + k) % 32 = k := by
    have heq : jLocal * 32 + k = k + 32 * jLocal := by ring
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
  have hjm : jLocal % 2 = jLocal := Nat.mod_eq_of_lt hjLocal
  have hidx : (jLocal * 32 + k) / (8 / 4 * (1 * 32)) * (8 * (1 * 32)) +
      (r % 4 * (8 / 4) +
        (jLocal * 32 + k) % (8 / 4 * (1 * 32)) / (1 * 32)) * (1 * 32) +
        (jLocal * 32 + k) % (8 / 4 * (1 * 32)) % (1 * 32) =
      (r * 2 + jLocal) * 32 + k := by
    simp only [show (8 / 4 * (1 * 32) : Nat) = 64 by norm_num,
      show (8 * (1 * 32) : Nat) = 256 by norm_num,
      show (1 * 32 : Nat) = 32 by norm_num,
      show (8 / 4 : Nat) = 2 by norm_num,
      h_div, h_mod, h_div32, h_mod32, hr', hjm]
    ring
  rw [show (8 / 4 * (1 * 32) : Nat) = 64 by norm_num] at *
  simp only [show (64 : Nat) ≠ 0 by omega, ite_false]
  rw [hidx]

/-! ### Bridging lemma: `fw_linear` distributes over dim-1 `allGatherPrimDimN`.

For `x : [1,8,32]` sharded along dim 1 into 4 pieces of shape `[1,2,32]`, and a
weight `w : [32,32]`, the linear application commutes with the gather:
  `fw_linear x w = allGatherPrimDimN 1 4 0 [fw_linear (chunk r x) w | r ∈ 0..3]`.

This is the key algebraic fact behind `prove_pattern_6` for goal_6. The proof
proceeds by `Tensor.ext` and `fw_linear_valAt_mul_add` plus the helper
`chunk1_x_1_8_32_valAt`. Marked `sorry` (TODO_SORRY) for now -- supplying the
proof completes the goal_6 case in the main theorem below. -/
private theorem fw_linear_split_dim1_4_1_8_32 (x w : Tensor)
    (hx : x.shape = [1, 8, 32]) (hw : w.shape = [32, 32]) :
    fw_linear x w = allGatherPrimDimN 1 4 0
      [fw_linear (chunkPrimDimN 1 4 0 x) w,
       fw_linear (chunkPrimDimN 1 4 1 x) w,
       fw_linear (chunkPrimDimN 1 4 2 x) w,
       fw_linear (chunkPrimDimN 1 4 3 x) w] := by
  sorry  -- TODO_SORRY_bridging_lemma_dim1_fw_linear

/-! ### Per-graph evaluation lemmas

These lemmas give a clean characterization of the relevant tensors in the
single-machine and parallel-machine graphs, by stripping non-writing suffixes
of the graph and reducing the cons step using `applyNode_fw_linear_out`. -/

private theorem sm_eval_572 (initSM : Store) :
    denoteGraph sm initSM 572 =
      fw_linear (denoteGraph sm initSM 918) (denoteGraph sm initSM 571) := by
  -- 572 is produced by node at index 6 in `sm.nodes`.
  have hsub : (denoteGraph sm initSM) 572 =
      (denoteGraph { sm with nodes := sm.nodes.take 7 } initSM) 572 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 572
      (sm.nodes.take 7) (sm.nodes.drop 7)
      (List.take_append_drop 7 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 7 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 6 ++
        [{ rank := 0, op := "OpName.FW_linear", ins := [918, 571], outs := [572] }] } := rfl
  rw [htake, denoteGraph_nodes_append]
  rw [denoteGraph_cons_eq sm
      { rank := 0, op := "OpName.FW_linear", ins := [918, 571], outs := [572] } []]
  change (applyNode sm (denoteGraph { sm with nodes := sm.nodes.take 6 } initSM)
      { rank := 0, op := "OpName.FW_linear", ins := [918, 571], outs := [572] }) 572 = _
  rw [applyNode_fw_linear_out]
  have h918 : denoteGraph { sm with nodes := sm.nodes.take 6 } initSM 918 =
      denoteGraph sm initSM 918 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 918
      (sm.nodes.take 6) (sm.nodes.drop 6)
      (List.take_append_drop 6 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have h571 : denoteGraph { sm with nodes := sm.nodes.take 6 } initSM 571 =
      denoteGraph sm initSM 571 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes sm initSM 571
      (sm.nodes.take 6) (sm.nodes.drop 6)
      (List.take_append_drop 6 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [h918, h571]

private theorem pm_eval_1177 (initPM : Store) :
    denoteGraph pm initPM 1177 =
      fw_linear (denoteGraph pm initPM 1173) (denoteGraph pm initPM 571) := by
  -- 1177 is produced by node at index 41 in `pm.nodes`.
  have hsub : (denoteGraph pm initPM) 1177 =
      (denoteGraph { pm with nodes := pm.nodes.take 42 } initPM) 1177 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1177
      (pm.nodes.take 42) (pm.nodes.drop 42)
      (List.take_append_drop 42 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 42 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 41 ++
        [{ rank := 0, op := "OpName.FW_linear", ins := [1173, 571], outs := [1177] }] } := rfl
  rw [htake, denoteGraph_nodes_append]
  rw [denoteGraph_cons_eq pm
      { rank := 0, op := "OpName.FW_linear", ins := [1173, 571], outs := [1177] } []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 41 } initPM)
      { rank := 0, op := "OpName.FW_linear", ins := [1173, 571], outs := [1177] }) 1177 = _
  rw [applyNode_fw_linear_out]
  have h1173 : denoteGraph { pm with nodes := pm.nodes.take 41 } initPM 1173 =
      denoteGraph pm initPM 1173 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1173
      (pm.nodes.take 41) (pm.nodes.drop 41)
      (List.take_append_drop 41 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have h571 : denoteGraph { pm with nodes := pm.nodes.take 41 } initPM 571 =
      denoteGraph pm initPM 571 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 571
      (pm.nodes.take 41) (pm.nodes.drop 41)
      (List.take_append_drop 41 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [h1173, h571]

private theorem pm_eval_1178 (initPM : Store) :
    denoteGraph pm initPM 1178 =
      fw_linear (denoteGraph pm initPM 1174) (denoteGraph pm initPM 571) := by
  have hsub : (denoteGraph pm initPM) 1178 =
      (denoteGraph { pm with nodes := pm.nodes.take 44 } initPM) 1178 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1178
      (pm.nodes.take 44) (pm.nodes.drop 44)
      (List.take_append_drop 44 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 44 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 43 ++
        [{ rank := 1, op := "OpName.FW_linear", ins := [1174, 571], outs := [1178] }] } := rfl
  rw [htake, denoteGraph_nodes_append]
  rw [denoteGraph_cons_eq pm
      { rank := 1, op := "OpName.FW_linear", ins := [1174, 571], outs := [1178] } []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 43 } initPM)
      { rank := 1, op := "OpName.FW_linear", ins := [1174, 571], outs := [1178] }) 1178 = _
  rw [applyNode_fw_linear_out]
  have h1174 : denoteGraph { pm with nodes := pm.nodes.take 43 } initPM 1174 =
      denoteGraph pm initPM 1174 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1174
      (pm.nodes.take 43) (pm.nodes.drop 43)
      (List.take_append_drop 43 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have h571 : denoteGraph { pm with nodes := pm.nodes.take 43 } initPM 571 =
      denoteGraph pm initPM 571 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 571
      (pm.nodes.take 43) (pm.nodes.drop 43)
      (List.take_append_drop 43 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [h1174, h571]

private theorem pm_eval_1179 (initPM : Store) :
    denoteGraph pm initPM 1179 =
      fw_linear (denoteGraph pm initPM 1175) (denoteGraph pm initPM 571) := by
  have hsub : (denoteGraph pm initPM) 1179 =
      (denoteGraph { pm with nodes := pm.nodes.take 46 } initPM) 1179 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1179
      (pm.nodes.take 46) (pm.nodes.drop 46)
      (List.take_append_drop 46 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 46 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 45 ++
        [{ rank := 2, op := "OpName.FW_linear", ins := [1175, 571], outs := [1179] }] } := rfl
  rw [htake, denoteGraph_nodes_append]
  rw [denoteGraph_cons_eq pm
      { rank := 2, op := "OpName.FW_linear", ins := [1175, 571], outs := [1179] } []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 45 } initPM)
      { rank := 2, op := "OpName.FW_linear", ins := [1175, 571], outs := [1179] }) 1179 = _
  rw [applyNode_fw_linear_out]
  have h1175 : denoteGraph { pm with nodes := pm.nodes.take 45 } initPM 1175 =
      denoteGraph pm initPM 1175 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1175
      (pm.nodes.take 45) (pm.nodes.drop 45)
      (List.take_append_drop 45 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have h571 : denoteGraph { pm with nodes := pm.nodes.take 45 } initPM 571 =
      denoteGraph pm initPM 571 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 571
      (pm.nodes.take 45) (pm.nodes.drop 45)
      (List.take_append_drop 45 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [h1175, h571]

private theorem pm_eval_1180 (initPM : Store) :
    denoteGraph pm initPM 1180 =
      fw_linear (denoteGraph pm initPM 1176) (denoteGraph pm initPM 571) := by
  -- 1180 is at idx 48 in pm.nodes.
  have hsub : (denoteGraph pm initPM) 1180 =
      (denoteGraph { pm with nodes := pm.nodes.take 49 } initPM) 1180 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1180
      (pm.nodes.take 49) (pm.nodes.drop 49)
      (List.take_append_drop 49 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 49 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 48 ++
        [{ rank := 3, op := "OpName.FW_linear", ins := [1176, 571], outs := [1180] }] } := rfl
  rw [htake, denoteGraph_nodes_append]
  rw [denoteGraph_cons_eq pm
      { rank := 3, op := "OpName.FW_linear", ins := [1176, 571], outs := [1180] } []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 48 } initPM)
      { rank := 3, op := "OpName.FW_linear", ins := [1176, 571], outs := [1180] }) 1180 = _
  rw [applyNode_fw_linear_out]
  have h1176 : denoteGraph { pm with nodes := pm.nodes.take 48 } initPM 1176 =
      denoteGraph pm initPM 1176 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1176
      (pm.nodes.take 48) (pm.nodes.drop 48)
      (List.take_append_drop 48 _).symm
      (by set_option maxRecDepth 20000 in decide)
  have h571 : denoteGraph { pm with nodes := pm.nodes.take 48 } initPM 571 =
      denoteGraph pm initPM 571 := by
    symm
    exact denoteGraph_tid_eq_of_suffix_no_writes pm initPM 571
      (pm.nodes.take 48) (pm.nodes.drop 48)
      (List.take_append_drop 48 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [h1176, h571]

/-! ### Goal_6 case

Combines `sm_eval_572`, `pm_eval_117{7,8,9}`, `pm_eval_1180` with the bridging
lemma `fw_linear_split_dim1_4_1_8_32` and the prereq `goal_261` (provided as
hypothesis via `InitGoalsHold` ... actually the public `goal_6_stmt` does NOT
inject prereqs; thus we additionally need the equality `SM 918 = allGather PM
[1173..1176] dim 1`. That equality is the content of `goal_261_stmt`, which is
proven elsewhere.)

Currently the SM/PM evaluation framework is in place. Tying them to the
`goal_6_stmt` requires a real proof of `goal_261_stmt` (not yet available in
this branch -- `Pattern_129.lean` is a `sorry` stub). Hence `prove_pattern_6`
remains a `sorry` for now; it will be unblocked once `Pattern_129` is proven
and the bridging lemma above is supplied. -/

theorem prove_pattern_6 : pattern_6_stmt := by
  intro target h
  cases h <;> sorry
  -- TODO_SORRY_main_proof: Each goal case requires
  --   1. SM-side eval (sm_eval_572 etc., done above for goal_6),
  --   2. PM-side eval per rank (pm_eval_117{7,8,9}, pm_eval_1180 above for goal_6),
  --   3. The dim-1 bridging lemma (`fw_linear_split_dim1_4_1_8_32`, sorry),
  --   4. A prereq saying SM 918 = allGather of PM [1173..1176] dim 1 (= goal_261_stmt),
  --      which is currently itself a sorry-stub via Pattern_129.lean.
  -- Goals 7/32/58/83 need analogous analyses (different tensor ids, same shape pattern).

end TrainVerify.Denote.GeneratedPatterns
