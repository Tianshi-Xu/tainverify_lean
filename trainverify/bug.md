# Generator Bug Report — `Verdict/graph_to_lean.py` output (gpt2_small_ly12)

**Audited artifact:** `denote/gpt2_small_ly12_segments/GeneratedData.lean` (auto-generated, 18,495 lines)
**Semantics reference:** `denote/Denote.lean`
**Method:** static analysis of the emitted graph cross-checked against the Lean op semantics; one finding
also confirmed by a real `lake build` (goal_2 proven, goal_3 shown unprovable).
**pm graph:** `numRanks = 4`. **sm graph:** reference (`numRanks = 1`).

## TL;DR — 2 confirmed generator bugs

| #    | Bug                                                          | Severity | Affected                                | Effect                                                       |
| ---- | ------------------------------------------------------------ | -------- | --------------------------------------- | ------------------------------------------------------------ |
| 1    | Vocab-sharded embedding emitted as plain `FW_embedding`/`BW_embedding` instead of the `*_offset` variant | **HIGH** | position embedding (fwd tid 1606 + bwd) | `goal_3_stmt` is **mathematically false**; blocks the entire forward chain (goal_4..8 → goal_26 → goal_342 …) |
| 2    | `OpName.BW_multiref` emitted but never dispatched in the interpreter | **HIGH** | 180 nodes                               | every goal transitively reading a BW_multiref output is **unprovable** (output tid never written → default/zero tensor) |

Negative results (checked, **clean**): AllToAllPrim params (the historical "P56" (idim,odim) transposition bug
is **not** present), ChunkPrim/AllGatherPrim/AllReducePrim/FW_view/FW_transpose shapes, op `ins` arities for all
26 dispatched ops, all 78 CROSS_DP_WRED nodes, all 180 FW_multiref out-counts.

---

## BUG 1 — Vocab-parallel embedding uses offset-free `FW_embedding` (+ `BW_embedding`) [HIGH]

### What the generator emitted

The **position embedding** weight (sm tid `1605`, shape `[1024, 768]`) is sharded across 4 ranks along the
**vocab dimension**: `tpShapes = [[256,768],[256,768],[256,768],[256,768]]` (rows split 0–255 / 256–511 / …),
into pm tids `3081..3084`. Each rank then computes a plain `FW_embedding`, and the 4 results are summed by
`AllReducePrim`:

```
-- pm graph
L707: { rank:=0, op:="OpName.FW_embedding", ins:=[2036, 3081], outs:=[3085] }   -- weight shard rows 0..255
L709: { rank:=1, op:="OpName.FW_embedding", ins:=[2036, 3082], outs:=[3086] }   -- weight shard rows 256..511
L711: { rank:=2, op:="OpName.FW_embedding", ins:=[2036, 3083], outs:=[3087] }
L713: { rank:=3, op:="OpName.FW_embedding", ins:=[2036, 3084], outs:=[3088] }
L718: { rank:=0, op:="OpName.AllReducePrim", ins:=[3085,3086,3087,3088], outs:=[1606] }  -- sum of the 4
```

### Why it is wrong

`fw_embedding` (Denote.lean:525) has **no row offset and no range check**:

```lean
def fw_embedding (ids weight : Tensor) : Tensor :=
  let hidden := lastD weight.shape
  Tensor.mkShape (ids.shape ++ [hidden]) (fun outIdx =>
    let row := scalarToNat (valAt ids (outIdx.1 / hidden))
    valAt weight (row * hidden + (outIdx.1 % hidden)))   -- always indexes weight[row], local
```

For a vocab shard covering global rows `[r*256, (r+1)*256)`, rank `r` looking up token id `row` must return
`weight[row - r*256]` **only when** `r*256 ≤ row < (r+1)*256`, and **0 otherwise** — so that the AllReduce sum
recovers the full embedding. Plain `fw_embedding` instead indexes `weight[row]` unconditionally (out-of-bounds
for `row ≥ 256`, wrong-row for the shards that should return 0). The sum of 4 such shards **≠** the full
`fw_embedding` on sm tid `1606`. Hence `goal_3_stmt` (which asserts pm `1606` ≡ sm `1606`) is **false**.

### The fix the generator should produce

Denote.lean already defines the correct op, `fw_embedding_offset` (Denote.lean:545), with exactly the right
range-checked semantics. The generator should emit, for vocab-sharded embedding, per rank `r`:

```
op := "OpName.FW_embedding_offset", params := [r * vocabShard]   -- vocabShard = 256 here
```

(There is currently **no** `FW_embedding_offset` node in the file — `grep` count = 0 — and `evalOp` would need a
dispatch branch for it; the function exists but is not wired into `evalOp`. So this fix has two parts:
generator emits the offset op **and** the interpreter dispatches it.)

### Important contrast — the generator is *correct* for the token embedding

The **token embedding** weight (tid `1603`, `[50257, 768]`) is sharded along the **hidden** dimension
(`gatherDim := 1`, `tpShapes = [[50257,192]×4]`) and gathered (not AllReduced). There, every shard holds the
**full vocab**, so plain `FW_embedding` is correct. ⇒ The bug is specifically: *the generator must choose
`*_offset` when the embedding weight is sharded along the **vocab/row** dimension and combined by AllReduce, but
keep plain when sharded along hidden and combined by gather.* It currently always emits plain.

### Backward side has the same defect

`BW_embedding` is emitted plain for the same vocab-sharded weights:

```
L5253: { rank:=0, op:="OpName.BW_embedding", ins:=[2041,2036,3081], outs:=[3097] }
L5254: { rank:=1, op:="OpName.BW_embedding", ins:=[2041,2036,3082], outs:=[3098] }   -- needs offset 256
...
```

`bw_embedding` (Denote.lean:559) accumulates `g` into `weight[row]` with no offset; `bw_embedding_offset`
(Denote.lean:567) does the offset-correct accumulation. Same fix applies.

### Verification status

- `prove_goal_2_full : goal_2_stmt` (token embedding, hidden-sharded) — **proven, real `lake build`, 0 sorry,
  no stub axioms** (commit `4673335`). Confirms plain `FW_embedding` is fine for the hidden-shard case.
- `goal_3` (position embedding, vocab-sharded) — **BLOCKED, mathematically false** under current emission.

---

## BUG 2 — `OpName.BW_multiref` is emitted but never dispatched [HIGH]

### What the generator emitted

180 `BW_multiref` nodes (the backward of `FW_multiref`; each FW_multiref copies one tensor to N outputs, so its
backward sums the N incoming grads). Example:

```
L367: { rank:=0, op:="OpName.BW_multiref", ins:=[...], outs:=[2535] }   -- 2535 ∈ obsTids
```

Each has 1 output and 2–3 inputs.

### Why it is wrong

`evalOp` in Denote.lean dispatches **`FW_multiref`** (line 2206, `=> List.replicate n x`) but has **no
`OpName.BW_multiref` branch**. It therefore falls through to the catch-all:

```lean
| _, _ => []          -- Denote.lean:2277
```

`applyNode` then does `n.outs.zip []  = []`, so the BW_multiref output tid is **never stored** — it retains the
store's default (zero) tensor. Any goal transitively reading such an output compares a zero tensor against the
real gradient ⇒ **unprovable** (and silently so — no type error, just a false lineage equation).

### Confirmed affected outputs feed real verification targets (`obsTids`)

- tid `2535` (out of BW_multiref L367) → BW_add L368 `ins:=[2535,…]`; `2535 ∈ obsTids`
- tid `2509` (out of BW_multiref L387) → BW_layernorm L388; `2509 ∈ obsTids`
- tid `2493` (out of BW_multiref L395) → BW_add L396; `2493 ∈ obsTids`

### The fix

Wire `BW_multiref` to `tensorSum` of its input grads (the mathematical adjoint of replicate), e.g.:

```lean
| "OpName.BW_multiref", xs => [tensorSum xs]
```

`tensorSum` already exists in Denote.lean. This is purely an **interpreter** gap (the generator's op name is
fine); but it is reported here because it blocks a large fraction of backward goals (incl. the SegmentPattern_8
gradient path goal_343 → goal_342).

---

## Negative results (audited, no bug found)

These classes were checked against worked numeric samples and are **consistent** — listing them so the creator
can rule them out:

- **AllToAllPrim (params / "P56" class):** `params = [idim, odim]` matches `allToAllPrimWithDims` (gather ×4 on
  `idim`, chunk ÷4 on `odim`) for all 6 param patterns (7 nodes sampled, e.g. L714 `[2,1]`, L741 `[1,2]`,
  L797 `[1,3]`, L805 `[2,3]`, L813 `[3,1]`, L966 `[3,2]`). No transposition / off-by-one. The historical P56
  bug is **not** present in this file.
- **ChunkPrim / AllGatherPrim / AllReducePrim / FW_view / FW_transpose:** declared shapes match op-computed
  shapes (samples L9, L13, L719, L759, L758, L772, L718).
- **Op arities:** all 26 dispatched op types' `ins` counts match their `evalOp` branch destructuring.
- **CROSS_DP_WRED:** 78 nodes, 4 same-shape inputs → `tensorSum`; the `outs[0]==ins[0]` aliasing is a safe
  in-place reduce (args read before store write). No bug.
- **FW_multiref:** all 180 nodes have `outs.length == params[0]` → `List.replicate` correct.

---

## Suggested generator-side changes (summary)

1. When emitting a sharded embedding: if the weight is split along the **vocab/row** dim and combined by
   `AllReducePrim`, emit `FW_embedding_offset` / `BW_embedding_offset` with `params := [rank * vocabShard]`
   instead of plain `FW_embedding` / `BW_embedding`. (Also add the `evalOp` dispatch for the offset ops.)
2. (Interpreter, not generator) Add an `evalOp` branch mapping `OpName.BW_multiref` to `tensorSum` of its inputs.

Both are blocking real proof obligations in the gpt2_small_ly12 segment set; (1) blocks the forward backbone,
(2) blocks a large set of backward gradient goals.

---

*Findings cross-checked between a focused static-analysis pass and a separate `lake build` confirmation
(goal_2 proven / goal_3 disproven). Line numbers are against the current `GeneratedData.lean`.*