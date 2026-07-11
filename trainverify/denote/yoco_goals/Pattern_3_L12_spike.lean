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

-- TODO: Add remaining L12 proofs (qproj, kproj, vproj, attention commute, etc.)

end TrainVerify.Denote.GeneratedPatterns
