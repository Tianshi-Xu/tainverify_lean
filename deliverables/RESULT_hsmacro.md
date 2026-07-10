# RESULT — hs_step% metaprogramming macro

## Summary

Compressed **1113** generic `RouterShapesHelpers.hs_<tid>` shape-helper
theorems in `Pattern_3.lean` from ~11 lines each to **1 line each** by
introducing a layer of 16 command-macro elaborators that splice the exact
proof template each helper needs, driven only by the numeric literals that
distinguish one helper from another.

## Metrics

| metric                        | before      | after       | delta            |
|-------------------------------|-------------|-------------|------------------|
| `Pattern_3.lean` total lines  | 40,820      | 29,885      | **−10,935 (−26.8%)** |
| hs_ generic block             | ~12,450     | ~1,400      | **≈ −11,000**    |
| `hs_*` theorems (names)       | 1116        | 1116        | 0 (all preserved)|
| build result                  | EXIT 0      | EXIT 0      | —                |
| build wall time               | ~25m13s     | 26m10s      | +3.8% (≤10% ✓)   |

Line target (~1,300 for the hs_ block) essentially met: 16 macro
definitions (~268 lines, one-time) + 1113 one-line invocations + 3
hand-written helpers.

## Approach

The theorem STATEMENT of each helper contains the fully-inferred output
shape (e.g. `.shape = [4096, 1024]`), which is **not** present in the graph
node — recovering it would require re-running full recursive shape
inference at elab time. A pure `hs_step% <graph> <tid>` term macro that
reads `pm_goal_3.nodes[m]` therefore cannot synthesise the statement.

Per the task's explicit fall-back clause ("a term-macro ... that emits the
proof term is also acceptable — still allows 1-line invocation"), and
mirroring the existing `mk_*` precedent (which likewise hardcodes affine
formulas rather than reading the graph), the delivered solution is a set of
**explicit-argument command macros**. Each helper becomes:

```
hsleaf 4680 s[4096, 1024]
hsadd  7491 4489 4490 s[4096, 1024]
hsmoe  14615 ... s[...] s[...]
```

The macro elaborator (`open Lean Elab Command Term in elab "hs<op> " ...`)
reads the numeric args + a custom `hsh` shape-list syntax
(`declare_syntax_cat hsh; syntax "s[" num,* "]" : hsh`), builds the exact
term AST the original hand-written proof used, and emits the full
`theorem hs_<tid> : ... := ...` declaration into `RouterShapesHelpers`.

### The 16 macros

`hsleaf` (leaf), `hsflt` (float leaf), `hsm2a`/`hsm2b` (multiref2),
`hsm5a`/`hsm5b` (multiref5), `hsview`, `hsadd`, `hsrms`, `hsnlin`,
`hssig`, `hschunk`, `hstkm`/`hstkp` (topk map/probs), `hsmul`, `hsmoe`.
These cover all 1113 generic helpers across the leaf/1in/id/2in/7in classes.

## Constraints — all satisfied

- **ZERO sorry, ZERO new axioms.** Kernel audit of 20 sampled helpers
  (`#print axioms`, spanning every op class + all 3 hand-written +
  deep-layer helpers hs_11622/hs_11626):
  every one reports exactly **`[propext, Classical.choice, Quot.sound]`**.
  No `sorryAx`, no `Lean.ofReduceBool`, no `native_decide`.
- **All 1116 `hs_<tid>` names preserved.** `diff` of the new invocation
  tid set vs the original theorem tid set is **IDENTICAL** (1116, no dups).
- **Backbone `HsHelpersGeneric` unchanged.** Lines 866–999 byte-identical
  to HEAD (verified by diff). Macros are consumers, not modifiers.
- **DO-NOT-TOUCH regions intact.** `DenoteUnfoldGeneric`, `sm_pm_*`,
  `mk_*` layer macros, and all other content byte-identical except a single
  trailing blank line before the final `end` (cosmetic, no proof touched).
  Only `Pattern_3.lean` was modified.
- **3 non-generic helpers hand-written:** `hs_4714` (allGather),
  `hs_9655` / `hs_9656` (maybe_shuffle) preserved verbatim.
- **Build EXIT 0**, +3.8% wall-time regression (within ≤10% budget).

## Honest notes

- The delivered macro is explicit-arg, not graph-reading, for the reason
  above (statement carries inferred shapes absent from the graph). This is
  the sanctioned fall-back, and matches how the pre-existing `mk_*` macros
  in this same file already operate.
- One scratch-only test of `hsnlin` initially failed inside a foreign test
  namespace due to `applyNode_fw_norm_linear_out` resolving to the
  parametric global (DenoteMoE.lean:806) instead of the concrete local
  (Pattern_3.lean:1250). Inside the production namespace
  `RouterShapesHelpers` the local wins (as the original hs_4708 already
  proved), so the deployed `hsnlin` helpers compile correctly — confirmed
  by the full EXIT-0 build and the clean axiom audit.
- The +3.8% build-time cost comes from per-helper fresh-AST elaboration, as
  anticipated.

## Commit

See `RELAY_hsmacro.log` for the commit SHA pushed to
`origin iroha-hs-macro`.
