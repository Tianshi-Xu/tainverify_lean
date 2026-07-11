/-
  Pattern_3_L13_spike.lean — L13 zigzag-band proof.

  Structurally analogous to Pattern_3_L12_spike (imported for its op-parametric
  zigzag reconstruction primitives and the shared K/V-projection denote chain).

  L13 is a *normal* CP layer: unlike L12 (a shuffle-boundary layer) its
  pre-attention path is just `carry → rms_norm → per_head_linear`, with NO
  `fw_maybe_shuffle` machinery.  The post-attention router head is a clean
  +49 (SM) / +172 (PM) tid-shift of L12's.

  L13 input carry is SM 5387 (= L12 block output, PM r0/r1 = 9829/9830); it is
  not proven on `main`, so it is threaded as a statement-level hypothesis with a
  vacuity witness (AGENTS.md #29).
-/
import denote.yoco_goals.Pattern_3_L12_spike

set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

namespace TrainVerify.Denote.GeneratedPatterns

/-! ## L13 attention NodeDecls -/

def nSM_13 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [5391, 5392, 5393, 5394, 5395], outs := [5396],
    params := [16, 4, 64, 64, 1, 0] }

def nR0_13 : NodeDecl :=
  { rank := 0, op := "OpName.FW_attn_zigzag",
    ins := [9835, 5392, 5393, 5394, 5395], outs := [9859],
    params := [16, 4, 64, 64, 1, 0] }

def nR1_13 : NodeDecl :=
  { rank := 1, op := "OpName.FW_attn_zigzag",
    ins := [9836, 5392, 5393, 5394, 5395], outs := [9860],
    params := [16, 4, 64, 64, 1, 0] }

set_option maxRecDepth 1000000 in
theorem buddy_sm_13 : ringAttnBuddies sm_goal_3 nSM_13 = [nSM_13] := by
  show (List.filter (fun m => decide (m.op = nSM_13.op) && decide (m.params = nSM_13.params) &&
      decide (m.ins.getD 3 0 = nSM_13.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_13.ins.getD 4 0))
      sm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nSM_13]
  rw [show (List.filter (fun m => decide (m.op = nSM_13.op) && decide (m.params = nSM_13.params) &&
      decide (m.ins.getD 3 0 = nSM_13.ins.getD 3 0) && decide (m.ins.getD 4 0 = nSM_13.ins.getD 4 0))
      sm_goal_3.nodes) = [nSM_13] from by rfl]
  simp

set_option maxRecDepth 1000000 in
theorem buddy_r0_13 : ringAttnBuddies pm_goal_3 nR0_13 = [nR0_13, nR1_13] := by
  show (List.filter (fun m => decide (m.op = nR0_13.op) && decide (m.params = nR0_13.params) &&
      decide (m.ins.getD 3 0 = nR0_13.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_13.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_13, nR1_13]
  rw [show (List.filter (fun m => decide (m.op = nR0_13.op) && decide (m.params = nR0_13.params) &&
      decide (m.ins.getD 3 0 = nR0_13.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR0_13.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_13, nR1_13] from by rfl]
  apply List.mergeSort_of_pairwise; decide

set_option maxRecDepth 1000000 in
theorem buddy_r1_13 : ringAttnBuddies pm_goal_3 nR1_13 = [nR0_13, nR1_13] := by
  show (List.filter (fun m => decide (m.op = nR1_13.op) && decide (m.params = nR1_13.params) &&
      decide (m.ins.getD 3 0 = nR1_13.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_13.ins.getD 4 0))
      pm_goal_3.nodes).mergeSort (fun a b => decide (a.rank ≤ b.rank)) = [nR0_13, nR1_13]
  rw [show (List.filter (fun m => decide (m.op = nR1_13.op) && decide (m.params = nR1_13.params) &&
      decide (m.ins.getD 3 0 = nR1_13.ins.getD 3 0) && decide (m.ins.getD 4 0 = nR1_13.ins.getD 4 0))
      pm_goal_3.nodes) = [nR0_13, nR1_13] from by rfl]
  apply List.mergeSort_of_pairwise; decide

end TrainVerify.Denote.GeneratedPatterns
