import Mathlib
import LeanCopilot
import Aesop
import RulesetInit
set_option maxHeartbeats 0
set_option maxRecDepth 1024
set_option trace.aesop true
@[aesop 100% (rule_sets := [bfs])] def tacGen := LeanCopilot.tacGen
add_aesop_rules unsafe 90% [(by rfl), (by linarith), (by nlinarith), (by ring), (by positivity), (by omega), (by ring_nf), (by ring_nf at *), (by simp), (by simp_all), (by field_simp), (by field_simp [*] at *), (by norm_num), (by norm_num [*] at *), (by norm_cast), (by norm_cast at *)]
open Lean Meta LeanCopilot
def BFS : ExternalGenerator := {
  name := "BFS-Prover-API"
  host := "localhost"
  port := 23337
}
#eval registerGenerator "BFS-Prover" (.external BFS)
set_option LeanCopilot.suggest_tactics.model "BFS-Prover"
macro "bfsaesop" : tactic =>
  `(tactic| aesop? (config := { enableSimp := false, enableUnfold := false, maxGoals := 64, bfsScore := true, terminal := true }) (rule_sets := [bfs, -builtin, -default]))
syntax "prove_with" ("[" term,* "]")? : tactic
macro_rules
| `(tactic| prove_with [$args,*]) => `(tactic| sorry)
| `(tactic| prove_with)           => `(tactic| sorry)
def bfsaesopLoop : Lean.Elab.Tactic.TacticM Unit := do
  try
    Lean.Elab.Tactic.evalTactic (← `(tactic| aesop? (config := {{ enableSimp := false, enableUnfold := false, maxGoals := 64, terminal := true }}) (rule_sets := [-builtin])))
    return
  catch _ =>
    pure ()
  try
    Lean.Elab.Tactic.evalTactic (← `(tactic| aesop? (config := {{ enableSimp := false, enableUnfold := false, maxGoals := 64, terminal := true }})))
    return
  catch _ =>
    pure ()
  for _ in [0:4] do
    try
      Lean.Elab.Tactic.evalTactic (← `(tactic| bfsaesop))
      return
    catch _ =>
      pure ()
  Lean.throwError "bfsaesopLoop failed"
elab "bfsaesopLoop" : tactic =>
  bfsaesopLoop

#eval generate BFS "n : ℕ\n⊢ gcd n n = n"

example (a b : ℝ) (h₀ : a ^ 2 * b ^ 3 = 32 / 27) (h₁ : a / b ^ 3 = 27 / 4) : a + b = 8 / 3 := by
  have h₂ : a = (27/4) * b^3 := by
    bfsaesopLoop
  sorry
