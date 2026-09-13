import TrainVerifyRuntimePrefixSupport
open Lean Elab Command
namespace PrefixNamesV4
-- Finite syntax identifiers only; qualified Names are not dotted simple names.
private partial def expand : Syntax → Syntax
  | .ident info raw n pre =>
      let m := if n == `pL then `AllToAllSourceFaithful.localStep
        else if n == `pE then `Nat.reduceEqDiff else n
      if m == n then .ident info raw n pre
      else mkIdentFrom (.ident info raw n pre) m
  | .node info kind args => .node info kind (args.map expand)
  | stx => stx
syntax (name := prefixNamesV4) "prefix_names_v4 " ident (" +")? (" +")? (" !")? " where" ppLine (colGt command)* : command
@[command_elab prefixNamesV4] def elabPrefixNamesV4 : CommandElab := fun stx => do
  match stx with
  | .node info _ args =>
      PrefixNames.elabPrefixNames (.node info ``PrefixNames.prefixNames
        (args.set! 6 (expand (args[6]!))))
  | _ => throwUnsupportedSyntax
end PrefixNamesV4
