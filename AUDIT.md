# Denote Op Semantics Audit — 2026-07-03 to onwards

## Purpose

Verify every `fw_XX` / `bw_XX` in `Denote.lean` is a faithful formalization of the
corresponding Python (PyTorch / nnscaler) function. This is the **数学最本质** layer:
op definitions being wrong ⇒ any downstream theorem is vacuous, even if it compiles.

## Method

For each op:
1. **Python authority**: link to PyTorch source or nnscaler custom-op definition (`llm-train/` or `nnscaler_genmodel/`)
2. **Denote formalization**: quote the Lean def
3. **Semantic mapping**: unify math notation, note any assumption gaps
4. **Verdict**:
   - ✅ VERIFIED: math def matches Python (small witness or spot-check acceptable for simple ops)
   - ⚠️ CONDITIONAL: correct only under stated preconditions (e.g., shape constraints, no broadcasting)
   - ❌ BROKEN: definition disagrees with Python
   - ❓ UNVERIFIED: not yet checked

## Legend

- L1 (evalOp binding): does the evalOp match arm bind ins to formal params correctly?
- L2 (op semantics): does the underlying `fw_XX/bw_XX` implement the Python function?
- L3 (proof clean): does `#print axioms` show only the 5-axiom kernel (no custom axioms)?

## Verdicts per model

### GPT-2 ly4 (26 non-collective ops + 4 collectives)

L1: ✅ verified all 26 use fixed-arity pattern `[x, ...]` (no `::` reordering bugs)
L3: ✅ `gpt_main_all_goals` depends only on `[propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]`
L2: (in progress below)

### Pattern_2 / 4 / 5 (yoco_goals, MoE)

L1: TODO
L2: TODO
L3: TODO

### Pattern_1 (MoE + CP)

L1: ❌ `fw_maybe_shuffle`, `fw_maybe_unshuffle`, `bw_maybe_shuffle`, `bw_maybe_unshuffle` — evalOp assumes `cu :: xs` but graph uses `[data, cu]`
L2: (impacted by L1; deferred)
L3: ❌ `prove_pattern_1` depends on `fw_maybe_unshuffle_cp2_commute` which is provably inconsistent (see `UnshuffleInconsistent.lean`). Pattern_1's proof is vacuous.

---

## Layer 1 audit (evalOp binding vs graph convention)

Total ops with non-trivial `::` pattern in `evalOp`/`tp_shape`:

- `FW_maybe_shuffle` (L3729 evalOp, L3483 tp_shape) — pattern `cu :: xs` / `_cu :: x0 :: _rest` ❌ WRONG (graph uses `[data, cu_seqlens]`, i.e., data at ins[0])
- `FW_maybe_unshuffle` (L3733 evalOp, L3485 tp_shape) — same bug ❌
- `BW_maybe_shuffle` (L3737 evalOp, L3487 tp_shape) — same bug ❌
- `BW_maybe_unshuffle` (L3741 evalOp, L3489 tp_shape) — same bug ❌

All other 68 ops use `[x]`, `[x, y]`, `[x, y, z]` etc. fixed-arity pattern → no arg-order ambiguity, L1 OK.

**Layer 1 fix**: swap the four `_cu :: x0 :: _rest` and four `cu :: xs` patterns to have data first.

**But this alone doesn't fix the semantic bug**: `fw_maybe_(un)shuffle` implementation
uses `xs.head?.shape` as `firstShape`. If we just swap the pattern, we swap the roles
of data and cu inside the body too, so `firstShape` would come from cu, still wrong.

**True fix**: swap both (a) evalOp binding AND (b) the fw_maybe_(un)shuffle Lean def
to make `data` the primary tensor and `cus` the metadata list. This is a coordinated
edit across two definitions.

---

## Layer 2 audit — GPT-2 ops (26)

Per-op checklist:

### FW_sum ✅

- **Python**: `torch.sum(x)` — reduces all elements to a scalar; here likely used to compute mean loss.
- **Denote** (`fw_sum x`): reduces along **all axes** to a single scalar output `[1]`.

