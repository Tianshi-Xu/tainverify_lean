import Lean
import denote.Denote
set_option maxHeartbeats 500000
open Lean Elab Command
namespace PrefixOpacity
initialize inventory : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun modules => modules.foldl (· ++ ·) #[] }

def markLocal (names : Array Name) : CommandElabM Unit := do
  for n in names do
    liftCoreM <| Attribute.add n `irreducible Syntax.missing .local

elab "record_prefix_opacity " ids:ident+ : command => do
  let names ← ids.mapM fun id => resolveGlobalConstNoOverload id
  for n in names do
    modifyEnv fun env => inventory.addEntry env n

elab "restore_prefix_opacity" : command => do
  markLocal (inventory.getState (← getEnv))
end PrefixOpacity

namespace TrainVerify.Denote
theorem prefixFrame_trans (s0 s1 s2 : Store) (xs ys : List Tid)
    (hx : ∀ t, t ∉ xs → s1 t = s0 t)
    (hy : ∀ t, t ∉ ys → s2 t = s1 t) :
    ∀ t, t ∉ xs ++ ys → s2 t = s0 t := by
  intro t h
  have hn : t ∉ xs ∧ t ∉ ys := by simpa only [List.mem_append, not_or] using h
  exact (hy t hn.2).trans (hx t hn.1)
#print axioms prefixFrame_trans
end TrainVerify.Denote
