/- Full Pattern_22-idiom forward-chain proofs for goal_2 (token embedding, dim-2 gather).

   See RELAY_FWD_2_8_REPORT.md for the status of goal_3..goal_8 (BLOCKED: the
   position-embedding pm subgraph for goal_3 uses *plain* `FW_embedding` row-shards
   summed by `AllReducePrim`, which does NOT equal the full position embedding —
   it is missing the per-rank vocab offset. goal_3 is therefore mathematically false,
   and goals 4..8 chain through it, so they cannot be proven without stubs.)

   This file is self-contained: it adds the real `fw_embedding` dim-2 gather bridge
   and proves `prove_goal_2_full : goal_2_stmt` with no incomplete proofs and no axiom stubs.
-/
import denote.gpt2_small_ly12_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

set_option maxRecDepth 32768

/-! ## Gather `valAt` helpers (shard 192 → full 768) -/

/-- dim-2 all-gather of four `[1,1024,192]` shards: lookup at `p*768 + r*192 + j`
    is rank-`r` piece at `p*192 + j`. -/
private theorem agD2_192_valAt
    (x0 x1 x2 x3 : Tensor) (r p j : Nat)
    (hx0 : x0.shape = [1, 1024, 192]) (hx1 : x1.shape = [1, 1024, 192])
    (hx2 : x2.shape = [1, 1024, 192]) (hx3 : x3.shape = [1, 1024, 192])
    (hr : r < 4) (hp : p < 1024) (hj : j < 192) :
    valAt (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3]) (p * 768 + r * 192 + j) =
      valAt ([x0, x1, x2, x3].getD r (zeroTensor [1, 1024, 192])) (p * 192 + j) := by
  have hidx_lt : p * 768 + r * 192 + j < 786432 := by
    have hp1 : p ≤ 1023 := by omega
    have hr3 : r ≤ 3 := by omega
    have hp768 : p * 768 ≤ 1023 * 768 := Nat.mul_le_mul_right 768 hp1
    have hr192 : r * 192 ≤ 3 * 192 := Nat.mul_le_mul_right 192 hr3
    omega
  have hhead : (([x0, x1, x2, x3] : List Tensor).head?.map (fun t => t.shape)).getD []
      = [1, 1024, 192] := by simp [hx0]
  have hgather_shape : (allGatherPrimDimN 2 4 0 [x0, x1, x2, x3]).shape = [1, 1024, 768] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hhead]; simp [List.set, List.getD]
  rw [valAt_of_lt _ _ (by rw [hgather_shape]; simpa [prodShape] using hidx_lt)]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (192 : Nat) ≠ 0 by omega, show (768 : Nat) ≠ 0 by omega,
    show (1 : Nat) ≠ 0 by omega, ite_false]
  simp only [show (192 : Nat) * 4 * 1 = 768 by norm_num,
    show (192 : Nat) * 1 = 192 by norm_num]
  set idx := p * 768 + r * 192 + j with hidx_def
  have hq : idx / 768 = p := by subst idx; omega
  have hjFull_div : idx % 768 / 1 / 192 = r := by subst idx; omega
  have hjFull_mod : idx % 768 / 1 % 192 = j := by subst idx; omega
  have hmod1 : idx % 768 % 1 = 0 := by subst idx; omega
  rw [hq, hjFull_div, hjFull_mod, hmod1]
  have hloc : p * 192 + j * 1 + 0 = p * 192 + j := by ring
  rw [hloc]

/-- dim-1 all-gather of four `[50257,192]` weight shards: lookup at `row*768 + r*192 + j`
    is rank-`r` shard at `row*192 + j`, for *any* `row` (handles out-of-range via 0). -/
private theorem agD1_192_valAt
    (w0 w1 w2 w3 : Tensor) (r row j : Nat)
    (hw0 : w0.shape = [50257, 192]) (hw1 : w1.shape = [50257, 192])
    (hw2 : w2.shape = [50257, 192]) (hw3 : w3.shape = [50257, 192])
    (hr : r < 4) (hj : j < 192) :
    valAt (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3]) (row * 768 + r * 192 + j) =
      valAt ([w0, w1, w2, w3].getD r (zeroTensor [50257, 192])) (row * 192 + j) := by
  have hhead : (([w0, w1, w2, w3] : List Tensor).head?.map (fun t => t.shape)).getD []
      = [50257, 192] := by simp [hw0]
  have hgather_shape : (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3]).shape = [50257, 768] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hhead]; simp [List.set, List.getD]
  have hpiece_shape : ([w0, w1, w2, w3].getD r (zeroTensor [50257, 192])).shape = [50257, 192] := by
    have hr4 : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hr4 with rfl | rfl | rfl | rfl
    · exact hw0
    · exact hw1
    · exact hw2
    · exact hw3
  by_cases hrow : row < 50257
  · -- in range
    have hidx_lt : row * 768 + r * 192 + j < 38597376 := by
      have hrow1 : row ≤ 50256 := by omega
      have hr3 : r ≤ 3 := by omega
      have hrow768 : row * 768 ≤ 50256 * 768 := Nat.mul_le_mul_right 768 hrow1
      have hr192 : r * 192 ≤ 3 * 192 := Nat.mul_le_mul_right 192 hr3
      omega
    rw [valAt_of_lt _ _ (by rw [hgather_shape]; simpa [prodShape] using hidx_lt)]
    unfold allGatherPrimDimN Tensor.mkShape
    simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, List.drop, List.foldl,
      show (192 : Nat) ≠ 0 by omega, show (768 : Nat) ≠ 0 by omega,
      show (50257 : Nat) ≠ 0 by omega, show (1 : Nat) ≠ 0 by omega, ite_false]
    simp only [show (192 : Nat) * 4 * 1 = 768 by norm_num,
      show (192 : Nat) * 1 = 192 by norm_num]
    set idx := row * 768 + r * 192 + j with hidx_def
    have hq : idx / 768 = row := by subst idx; omega
    have hjFull_div : idx % 768 / 1 / 192 = r := by subst idx; omega
    have hjFull_mod : idx % 768 / 1 % 192 = j := by subst idx; omega
    have hmod1 : idx % 768 % 1 = 0 := by subst idx; omega
    rw [hq, hjFull_div, hjFull_mod, hmod1]
    have hloc : row * 192 + j * 1 + 0 = row * 192 + j := by ring
    rw [hloc]
  · -- out of range: both sides are 0
    have hrow' : 50257 ≤ row := by omega
    have hL : ¬ (row * 768 + r * 192 + j < prodShape
        (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3]).shape) := by
      rw [hgather_shape]
      have : 50257 * 768 ≤ row * 768 := Nat.mul_le_mul_right 768 hrow'
      simp only [prodShape, List.foldl]; omega
    have hR : ¬ (row * 192 + j < prodShape
        ([w0, w1, w2, w3].getD r (zeroTensor [50257, 192])).shape) := by
      rw [hpiece_shape]
      have : 50257 * 192 ≤ row * 192 := Nat.mul_le_mul_right 192 hrow'
      simp only [prodShape, List.foldl]; omega
    rw [valAt, valAt]
    rw [dif_neg hL, dif_neg hR]

/-! ## `fw_embedding` dim-2 gather bridge -/

/-- Column-parallel token embedding: gathering the weight along dim 1 (hidden)
    then embedding equals embedding each weight shard then gathering the outputs
    along dim 2.  ids `[1,1024]`, each weight shard `[50257,192]`. -/
private theorem fw_embedding_dim2_bridge
    (ids w0 w1 w2 w3 : Tensor)
    (hids : ids.shape = [1, 1024])
    (hw0 : w0.shape = [50257, 192]) (hw1 : w1.shape = [50257, 192])
    (hw2 : w2.shape = [50257, 192]) (hw3 : w3.shape = [50257, 192]) :
    fw_embedding ids (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3]) =
      allGatherPrimDimN 2 4 0
        [fw_embedding ids w0, fw_embedding ids w1, fw_embedding ids w2, fw_embedding ids w3] := by
  have hwhead : (([w0, w1, w2, w3] : List Tensor).head?.map (fun t => t.shape)).getD []
      = [50257, 192] := by simp [hw0]
  have hfull_shape : (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3]).shape = [50257, 768] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hwhead]; simp [List.set, List.getD]
  have hfull_last : lastD (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3]).shape = 768 := by
    rw [hfull_shape]; rfl
  have he_shape : ∀ {w : Tensor}, w.shape = [50257, 192] →
      (fw_embedding ids w).shape = [1, 1024, 192] := by
    intro w hw
    rw [fw_embedding_shape, hids, hw]; rfl
  have he0 := he_shape hw0
  have he1 := he_shape hw1
  have he2 := he_shape hw2
  have he3 := he_shape hw3
  have hehead : (([fw_embedding ids w0, fw_embedding ids w1, fw_embedding ids w2,
      fw_embedding ids w3] : List Tensor).head?.map (fun t => t.shape)).getD [] = [1, 1024, 192] := by
    simp [he0]
  have hlhs_shape : (fw_embedding ids (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3])).shape
      = [1, 1024, 768] := by
    rw [fw_embedding_shape, hids, hfull_last]; rfl
  have hrhs_shape : (allGatherPrimDimN 2 4 0
      [fw_embedding ids w0, fw_embedding ids w1, fw_embedding ids w2, fw_embedding ids w3]).shape
      = [1, 1024, 768] := by
    rw [allGatherPrimDimN_shape 2 4 _ _ hehead]; simp [List.set, List.getD]
  apply Tensor.ext (by rw [hlhs_shape, hrhs_shape])
  intro idx hidx
  have hidx_lt : idx < 786432 := by simpa [hlhs_shape, prodShape] using hidx
  set p := idx / 768 with hp_def
  set rr := idx % 768 / 192 with hrr_def
  set j := idx % 768 % 192 with hj_def
  have hp_lt : p < 1024 := by subst p; omega
  have hrr_lt : rr < 4 := by subst rr; omega
  have hj_lt : j < 192 := by subst j; omega
  have hsplit : idx = p * 768 + rr * 192 + j := by subst p rr j; omega
  -- RHS via dim-2 gather helper
  have hRHS : valAt (allGatherPrimDimN 2 4 0
        [fw_embedding ids w0, fw_embedding ids w1, fw_embedding ids w2, fw_embedding ids w3]) idx =
      valAt ([fw_embedding ids w0, fw_embedding ids w1, fw_embedding ids w2,
          fw_embedding ids w3].getD rr (zeroTensor [1, 1024, 192])) (p * 192 + j) := by
    rw [hsplit]
    exact agD2_192_valAt _ _ _ _ rr p j he0 he1 he2 he3 hrr_lt hp_lt hj_lt
  -- LHS via fw_embedding + dim-1 gather helper
  have hidx_dom : idx < prodShape (ids.shape ++ [lastD
      (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3]).shape]) := by
    rw [hids, hfull_last]; simpa [prodShape] using hidx_lt
  have hLHS : valAt (fw_embedding ids (allGatherPrimDimN 1 4 0 [w0, w1, w2, w3])) idx =
      valAt ([w0, w1, w2, w3].getD rr (zeroTensor [50257, 192]))
        ((scalarToNat (valAt ids p)) * 192 + j) := by
    rw [fw_embedding_valAt, dif_pos hidx_dom, hfull_last]
    have hdiv : idx / 768 = p := by rw [hp_def]
    have hmod : idx % 768 = rr * 192 + j := by subst rr j; omega
    rw [hdiv, hmod]
    have harr : scalarToNat (valAt ids p) * 768 + (rr * 192 + j)
        = scalarToNat (valAt ids p) * 768 + rr * 192 + j := by ring
    rw [harr]
    exact agD1_192_valAt _ _ _ _ rr (scalarToNat (valAt ids p)) j hw0 hw1 hw2 hw3 hrr_lt hj_lt
  rw [hLHS, hRHS]
  -- both sides reduce to `valAt w_rr (scalarToNat (valAt ids p) * 192 + j)`
  have hpj_lt : p * 192 + j < 196608 := by
    have : p ≤ 1023 := by omega
    have : p * 192 ≤ 1023 * 192 := Nat.mul_le_mul_right 192 (by omega)
    omega
  have hrr_cases : rr = 0 ∨ rr = 1 ∨ rr = 2 ∨ rr = 3 := by omega
  have hkey : ∀ {w : Tensor}, w.shape = [50257, 192] →
      valAt (fw_embedding ids w) (p * 192 + j)
        = valAt w (scalarToNat (valAt ids p) * 192 + j) := by
    intro w hw
    rw [fw_embedding_valAt]
    have hdom : p * 192 + j < prodShape (ids.shape ++ [lastD w.shape]) := by
      rw [hids, hw]; simpa [prodShape] using hpj_lt
    rw [dif_pos hdom, hw]
    have hlw : lastD ([50257, 192] : Shape) = 192 := rfl
    rw [hlw]
    have hdv : (p * 192 + j) / 192 = p := by omega
    have hmd : (p * 192 + j) % 192 = j := by omega
    rw [hdv, hmd]
  rcases hrr_cases with h | h | h | h <;> rw [h] <;>
    simp only [List.getD_cons_zero, List.getD_cons_succ]
  · exact (hkey hw0).symm
  · exact (hkey hw1).symm
  · exact (hkey hw2).symm
  · exact (hkey hw3).symm

/-! ## goal_2 producing nodes, evaluation lemmas, and final proof -/

-- sm producing node (sm.nodes idx 0): FW_embedding ins [ids=2034, w=1603] -> 1604
@[reducible] private def g2_sg : NodeDecl :=
  { rank := 0, op := "OpName.FW_embedding", ins := [2034, 1603], outs := [1604] }
-- pm producing nodes (pm.nodes idx 0,2,4,6)
@[reducible] private def g2_pg0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_embedding", ins := [2034, 3057], outs := [3061] }
@[reducible] private def g2_pg1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_embedding", ins := [2034, 3058], outs := [3062] }
@[reducible] private def g2_pg2 : NodeDecl :=
  { rank := 2, op := "OpName.FW_embedding", ins := [2034, 3059], outs := [3063] }
@[reducible] private def g2_pg3 : NodeDecl :=
  { rank := 3, op := "OpName.FW_embedding", ins := [2034, 3060], outs := [3064] }

set_option maxHeartbeats 16000000 in
private theorem sm_eval_1604 (initSM : Store) :
    denoteGraph sm initSM 1604 = fw_embedding (initSM 2034) (initSM 1603) := by
  have hsub : denoteGraph sm initSM 1604 =
      denoteGraph { sm with nodes := sm.nodes.take 1 } initSM 1604 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 1604
      (sm.nodes.take 1) (sm.nodes.drop 1)
      (List.take_append_drop 1 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ sm with nodes := sm.nodes.take 1 } : GraphDecl) =
      { sm with nodes := sm.nodes.take 0 ++ [g2_sg] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ sm with nodes := [g2_sg] } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := g2_sg :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq sm g2_sg []]
  have hnil : denoteGraph { sm with nodes := sm.nodes.take 0 } initSM = initSM := by
    show denoteGraph { sm with nodes := [] } initSM = initSM
    simp
  change (applyNode sm (denoteGraph { sm with nodes := sm.nodes.take 0 } initSM) g2_sg) 1604 = _
  rw [hnil, applyNode_fw_embedding_out]

-- Generic pm embedding piece evaluation at producer index 0 (peel + restore inits).
set_option maxHeartbeats 16000000 in
private theorem pm_eval_3061 (initPM : Store) :
    denoteGraph pm initPM 3061 = fw_embedding (initPM 2034) (initPM 3057) := by
  have hsub : denoteGraph pm initPM 3061 =
      denoteGraph { pm with nodes := pm.nodes.take 1 } initPM 3061 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3061
      (pm.nodes.take 1) (pm.nodes.drop 1)
      (List.take_append_drop 1 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 1 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 0 ++ [g2_pg0] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g2_pg0] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := g2_pg0 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g2_pg0 []]
  have hnil : denoteGraph { pm with nodes := pm.nodes.take 0 } initPM = initPM := by
    show denoteGraph { pm with nodes := [] } initPM = initPM
    simp
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 0 } initPM) g2_pg0) 3061 = _
  rw [hnil, applyNode_fw_embedding_out]

set_option maxHeartbeats 16000000 in
private theorem pm_eval_3062 (initPM : Store) :
    denoteGraph pm initPM 3062 = fw_embedding (initPM 2034) (initPM 3058) := by
  have hsub : denoteGraph pm initPM 3062 =
      denoteGraph { pm with nodes := pm.nodes.take 3 } initPM 3062 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3062
      (pm.nodes.take 3) (pm.nodes.drop 3)
      (List.take_append_drop 3 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 3 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 2 ++ [g2_pg1] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g2_pg1] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := g2_pg1 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g2_pg1 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 2 } initPM) g2_pg1) 3062 = _
  rw [applyNode_fw_embedding_out]
  have hin0 : denoteGraph { pm with nodes := pm.nodes.take 2 } initPM 2034 = initPM 2034 := by
    rw [denoteGraph_tid_eq_of_suffix_no_writes { pm with nodes := pm.nodes.take 2 } initPM 2034
      [] (pm.nodes.take 2) rfl (by set_option maxRecDepth 20000 in decide)]
    simp
  have hin1 : denoteGraph { pm with nodes := pm.nodes.take 2 } initPM 3058 = initPM 3058 := by
    rw [denoteGraph_tid_eq_of_suffix_no_writes { pm with nodes := pm.nodes.take 2 } initPM 3058
      [] (pm.nodes.take 2) rfl (by set_option maxRecDepth 20000 in decide)]
    simp
  rw [hin0, hin1]

set_option maxHeartbeats 16000000 in
private theorem pm_eval_3063 (initPM : Store) :
    denoteGraph pm initPM 3063 = fw_embedding (initPM 2034) (initPM 3059) := by
  have hsub : denoteGraph pm initPM 3063 =
      denoteGraph { pm with nodes := pm.nodes.take 5 } initPM 3063 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3063
      (pm.nodes.take 5) (pm.nodes.drop 5)
      (List.take_append_drop 5 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 5 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 4 ++ [g2_pg2] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g2_pg2] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := g2_pg2 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g2_pg2 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 4 } initPM) g2_pg2) 3063 = _
  rw [applyNode_fw_embedding_out]
  have hin0 : denoteGraph { pm with nodes := pm.nodes.take 4 } initPM 2034 = initPM 2034 := by
    rw [denoteGraph_tid_eq_of_suffix_no_writes { pm with nodes := pm.nodes.take 4 } initPM 2034
      [] (pm.nodes.take 4) rfl (by set_option maxRecDepth 20000 in decide)]
    simp
  have hin1 : denoteGraph { pm with nodes := pm.nodes.take 4 } initPM 3059 = initPM 3059 := by
    rw [denoteGraph_tid_eq_of_suffix_no_writes { pm with nodes := pm.nodes.take 4 } initPM 3059
      [] (pm.nodes.take 4) rfl (by set_option maxRecDepth 20000 in decide)]
    simp
  rw [hin0, hin1]

set_option maxHeartbeats 16000000 in
private theorem pm_eval_3064 (initPM : Store) :
    denoteGraph pm initPM 3064 = fw_embedding (initPM 2034) (initPM 3060) := by
  have hsub : denoteGraph pm initPM 3064 =
      denoteGraph { pm with nodes := pm.nodes.take 7 } initPM 3064 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 3064
      (pm.nodes.take 7) (pm.nodes.drop 7)
      (List.take_append_drop 7 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 7 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 6 ++ [g2_pg3] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [g2_pg3] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := g2_pg3 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm g2_pg3 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 6 } initPM) g2_pg3) 3064 = _
  rw [applyNode_fw_embedding_out]
  have hin0 : denoteGraph { pm with nodes := pm.nodes.take 6 } initPM 2034 = initPM 2034 := by
    rw [denoteGraph_tid_eq_of_suffix_no_writes { pm with nodes := pm.nodes.take 6 } initPM 2034
      [] (pm.nodes.take 6) rfl (by set_option maxRecDepth 20000 in decide)]
    simp
  have hin1 : denoteGraph { pm with nodes := pm.nodes.take 6 } initPM 3060 = initPM 3060 := by
    rw [denoteGraph_tid_eq_of_suffix_no_writes { pm with nodes := pm.nodes.take 6 } initPM 3060
      [] (pm.nodes.take 6) rfl (by set_option maxRecDepth 20000 in decide)]
    simp
  rw [hin0, hin1]

set_option maxHeartbeats 8000000 in
theorem prove_goal_2_full : goal_2_stmt := by
  intro initSM initPM _hSmInit _hPmInit hInitGoals
  -- pull the two init goals (token-id replication, token-weight dim-1 sharding)
  have hIds := hInitGoals initGoal_2034 (by simp [initGoals])
  have hW := hInitGoals initGoal_1603 (by simp [initGoals])
  obtain ⟨hIds_sh, hIds_psh, hIds_rec⟩ := hIds
  obtain ⟨hW_sh, hW_psh, hW_rec⟩ := hW
  -- ids: replicated singleton ⇒ initSM 2034 = initPM 2034
  simp only [initGoal_2034, List.map_cons, List.map_nil, reconstructWithDim_singleton] at hIds_rec
  change initSM 2034 = initPM 2034 at hIds_rec
  -- weight shard shapes
  have hIds_shape : (initSM 2034).shape = [1, 1024] := by
    have := hIds_sh; simpa [initGoal_2034] using this
  have hIdsPM_shape : (initPM 2034).shape = [1, 1024] := by
    rw [← hIds_rec]; exact hIds_shape
  have ⟨hw0_sh, hw1_sh, hw2_sh, hw3_sh⟩ :
      (initPM 3057).shape = [50257, 192] ∧ (initPM 3058).shape = [50257, 192] ∧
      (initPM 3059).shape = [50257, 192] ∧ (initPM 3060).shape = [50257, 192] := by
    have hs := hW_psh
    simp only [initGoal_1603, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hs
    exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩
  -- weight: dim-1 gather ⇒ initSM 1603 = allGatherPrimDimN 1 4 0 [shards]
  have hW_eq : initSM 1603 = allGatherPrimDimN 1 4 0
      [initPM 3057, initPM 3058, initPM 3059, initPM 3060] := by
    have hh := hW_rec
    simp only [initGoal_1603, List.map_cons, List.map_nil] at hh
    rw [hh, show pm.numRanks = 4 from rfl, reconstructWithDim_cons_cons_nonscalar]
    rw [hw0_sh]; intro hbad; cases hbad
  -- piece evaluations
  have hsm := sm_eval_1604 initSM
  have hp0 := pm_eval_3061 initPM
  have hp1 := pm_eval_3062 initPM
  have hp2 := pm_eval_3063 initPM
  have hp3 := pm_eval_3064 initPM
  -- output shapes
  have hp0_shape : (denoteGraph pm initPM 3061).shape = [1, 1024, 192] := by
    rw [hp0, fw_embedding_shape, hIdsPM_shape, hw0_sh]; rfl
  have hp1_shape : (denoteGraph pm initPM 3062).shape = [1, 1024, 192] := by
    rw [hp1, fw_embedding_shape, hIdsPM_shape, hw1_sh]; rfl
  have hp2_shape : (denoteGraph pm initPM 3063).shape = [1, 1024, 192] := by
    rw [hp2, fw_embedding_shape, hIdsPM_shape, hw2_sh]; rfl
  have hp3_shape : (denoteGraph pm initPM 3064).shape = [1, 1024, 192] := by
    rw [hp3, fw_embedding_shape, hIdsPM_shape, hw3_sh]; rfl
  -- sm output shape
  have h_p1 : (denoteGraph sm initSM 1604).shape = [1, 1024, 768] := by
    rw [hsm, fw_embedding_shape, hIds_shape, hW_eq]
    have hwhead : (([initPM 3057, initPM 3058, initPM 3059, initPM 3060] : List Tensor).head?.map
        (fun t => t.shape)).getD [] = [50257, 192] := by simp [hw0_sh]
    rw [show lastD (allGatherPrimDimN 1 4 0 [initPM 3057, initPM 3058, initPM 3059, initPM 3060]).shape
          = 768 by rw [allGatherPrimDimN_shape 1 4 _ _ hwhead]; rfl]
    rfl
  -- the reconstruction equation
  have h_p3 : denoteGraph sm initSM 1604 =
      reconstructWithDim 2 4 0
        [denoteGraph pm initPM 3061, denoteGraph pm initPM 3062,
         denoteGraph pm initPM 3063, denoteGraph pm initPM 3064] := by
    rw [hsm, hIds_rec, hW_eq, hp0, hp1, hp2, hp3]
    rw [reconstructWithDim_cons_cons_nonscalar]
    · exact fw_embedding_dim2_bridge (initPM 2034) (initPM 3057) (initPM 3058)
        (initPM 3059) (initPM 3060) hIdsPM_shape hw0_sh hw1_sh hw2_sh hw3_sh
    · rw [show (fw_embedding (initPM 2034) (initPM 3057)).shape = [1, 1024, 192] by
            rw [fw_embedding_shape, hIdsPM_shape, hw0_sh]; rfl]
      intro hbad; cases hbad
  change (denoteGraph sm initSM 1604).shape = [1, 1024, 768] ∧
    List.map (fun t => t.shape)
      ([({ rank := 0, tid := 3061 } : Piece), { rank := 1, tid := 3062 },
        { rank := 2, tid := 3063 }, { rank := 3, tid := 3064 }].map
        (fun p => denoteGraph pm initPM p.tid)) =
      [[1, 1024, 192], [1, 1024, 192], [1, 1024, 192], [1, 1024, 192]] ∧
    denoteGraph sm initSM 1604 =
      reconstructWithDim 2 pm.numRanks 0
        ([({ rank := 0, tid := 3061 } : Piece), { rank := 1, tid := 3062 },
          { rank := 2, tid := 3063 }, { rank := 3, tid := 3064 }].map
          (fun p => denoteGraph pm initPM p.tid))
  refine ⟨h_p1, ?_, ?_⟩
  · simp only [List.map_cons, List.map_nil]
    rw [hp0_shape, hp1_shape, hp2_shape, hp3_shape]
  · simp only [List.map_cons, List.map_nil, show pm.numRanks = 4 from rfl]
    exact h_p3

#print axioms prove_goal_2_full

end TrainVerify.Denote.GeneratedPatterns
