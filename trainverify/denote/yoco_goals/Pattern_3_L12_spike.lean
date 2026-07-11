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
  native_decide

set_option maxRecDepth 1000000 in
theorem buddy_r0_12 : ringAttnBuddies pm_goal_3 nR0_12 = [nR0_12, nR1_12] := by
  show (List.filter (fun m => decide (m.op = nR0_12.op) && decide (m.params = nR0_12.params) &&
      decide (m.ins.getD 3 0 = nR0_12.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_12.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_12, nR1_12]
  native_decide

set_option maxRecDepth 1000000 in
theorem buddy_r1_12 : ringAttnBuddies pm_goal_3 nR1_12 = [nR0_12, nR1_12] := by
  show (List.filter (fun m => decide (m.op = nR1_12.op) && decide (m.params = nR1_12.params) &&
      decide (m.ins.getD 3 0 = nR1_12.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_12.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_12, nR1_12]
  native_decide

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

end TrainVerify.Denote.GeneratedPatterns
