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

namespace PrefixNames
private def family (s : String) : Option String :=
  match s with
  | "s" => some "State" | "v" => some "Value" | "r" => some "Read"
  | "w" => some "Written" | "h" => some "Shape" | "k" => some "Skip"
  | "t" => some "Step" | "n" => some "NoWrite" | "g" => some "Guard"
  | "i" => some "InitialShape" | "e" => some "InitialRead"
  | "q" => some "Requests" | "u" => some "Run" | _ => none
private def expandName (stemPrefix : String) (n : Name) : Name := Id.run do
  let .str .anonymous text := n | return n
  let code :: parts := text.splitOn "_" | return n
  let some stem := family code | return n
  if parts.isEmpty || !parts.all (fun p => !p.isEmpty && p.toList.all Char.isDigit) then
    return n
  return Name.mkSimple (stemPrefix ++ stem ++ "_" ++ String.intercalate "_" parts)
private partial def expand (stemPrefix : String) : Syntax → Syntax
  | .ident info raw n pre =>
      let m := expandName stemPrefix n
      if m == n then .ident info raw n pre else mkIdentFrom (.ident info raw n pre) m
  | .node info kind args => .node info kind (args.map (expand stemPrefix))
  | stx => stx
syntax (name := prefixNames) "prefix_names " ident " where" ppLine (colGt command)* : command
@[command_elab prefixNames] def elabPrefixNames : CommandElab := fun stx => do
  let pref := stx[1].getId.toString
  for cmd in stx[3].getArgs do
    elabCommand (expand pref cmd)
end PrefixNames

namespace TrainVerify.Denote
theorem prefixFrame_trans (s0 s1 s2 : Store) (xs ys : List Tid)
    (hx : ∀ t, t ∉ xs → s1 t = s0 t)
    (hy : ∀ t, t ∉ ys → s2 t = s1 t) :
    ∀ t, t ∉ xs ++ ys → s2 t = s0 t := by
  intro t h
  have hn : t ∉ xs ∧ t ∉ ys := by simpa only [List.mem_append, not_or] using h
  exact (hy t hn.2).trans (hx t hn.1)
#print axioms prefixFrame_trans

-- Infer the concrete Tid from the unchanged goal; decide every full footprint.
theorem prefixRead {s0 s1 : Store} {xs : List Tid} {tid : Tid} {v : Tensor}
    (frame : ∀ t, t ∉ xs → s1 t = s0 t) (anchor : s0 tid = v)
    (h : tid ∉ xs := by decide) : s1 tid = v :=
  (frame tid h).trans anchor
#print axioms prefixRead
end TrainVerify.Denote
