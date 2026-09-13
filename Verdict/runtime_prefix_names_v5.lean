import TrainVerifyRuntimePrefixSupport
open Lean Elab Command
namespace PrefixNamesV5
-- Exact finite identifiers; the stem and flags are metadata, never aliases.
private partial def expand (stem : String) : Syntax → Syntax
  | .ident info raw n pre =>
      let m := if n == `pL then `AllToAllSourceFaithful.localStep
        else if n == `pE then `Nat.reduceEqDiff
        else if n == `zS then Name.mkSimple (stem ++ "InitShapes")
        else if n == `pT then Name.mkSimple "stepWithInputs"
        else if n == `pD then Name.mkSimple "decide_false"
        else if n == `pC then Name.mkSimple "decide_true" else n
      if m == n then .ident info raw n pre
      else mkIdentFrom (.ident info raw n pre) m
  | .node info kind args => .node info kind (args.map (expand stem))
  | stx => stx
syntax (name := prefixNamesV5) "prefix_names_v5 " ident (" +")? (" +")? (" !")? " where" ppLine (colGt command)* : command
@[command_elab prefixNamesV5] def elabPrefixNamesV5 : CommandElab := fun stx => do
  match stx with
  | .node info _ args =>
      let stem := args[1]!.getId.toString
      PrefixNames.elabPrefixNames (.node info ``PrefixNames.prefixNames
        (args.set! 6 (expand stem (args[6]!))))
  | _ => throwUnsupportedSyntax
end PrefixNamesV5
