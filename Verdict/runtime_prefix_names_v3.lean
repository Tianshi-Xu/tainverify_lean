import TrainVerifyRuntimePrefixSupport
open Lean Elab Command
namespace PrefixNamesV3
-- One finite qualified-name alias, scoped to this command, never a keyword.
private partial def expand : Syntax → Syntax
  | .ident info raw n pre =>
      if n == Name.mkSimple "pL" then
        mkIdentFrom (.ident info raw n pre)
          (Name.str (Name.str Name.anonymous "AllToAllSourceFaithful") "localStep")
      else .ident info raw n pre
  | .node info kind args => .node info kind (args.map expand)
  | stx => stx
syntax (name := prefixNamesV3) "prefix_names_v3 " ident (" +")? (" +")? (" !")? " where" ppLine (colGt command)* : command
@[command_elab prefixNamesV3] def elabPrefixNamesV3 : CommandElab := fun stx => do
  match stx with
  | .node info _ args =>
      -- Only commands carry aliases; the stem and option flags are metadata.
      PrefixNames.elabPrefixNames (.node info ``PrefixNames.prefixNames
        (args.set! 6 (expand (args[6]!))))
  | _ => throwUnsupportedSyntax
end PrefixNamesV3
