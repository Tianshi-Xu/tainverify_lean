# TrainVerify Generic Proof Compiler

This directory now contains a fail-closed proof-planning and certificate-composition path in addition to the legacy bridge renderer.

## Public entry points

```bash
python3 trainverify/bridge_emitter/plan.py <GOAL> --root <REPO> --json
python3 trainverify/bridge_emitter/emit2.py <GOAL> --out <OUTPUT.lean>
```

Target selection remains controlled by the existing `BRIDGE_DENOTE_DIR`, `BRIDGE_GEN_FILE`, and `BRIDGE_GEN_DIR` environment variables.

## Planning contract

`plan.py --json` has three exit classes:

- `0`: a typed dependency plan exists and a registered full-topology composer can emit theorem source (`status=composable`, `certificate_source_complete=true`). The read-only planner reports `kernel_checked=false` and `proof_complete=false`; only `emit2.py` followed by a successful Lean run may establish those stronger claims.
- `1`: the graph is structurally unsupported, or it can be planned but no complete composer rule exists (`status=unsupported`).
- `2`: invocation or runtime failure (`status=error`, diagnostic code `cli.runtime`).

When `--json` is present, argument/usage failures are also emitted as JSON with
diagnostic code `cli.usage`; stderr remains empty.

A successful dependency DAG alone is not reported as a completed proof.

Node records are field-order independent but schema-closed: the parser consumes
the complete `nodes` list and rejects unknown, duplicate, missing, or residual
record text rather than silently dropping a node.

The JSON report includes:

- the declared target relation (`gather` or `replicated`);
- deterministic certificate steps and dependencies;
- each step's typed rule kind and relation effect;
- exact target steps;
- a stable first-failure diagnostic with side, node index, operator, and output tid;
- full-composition status and rule id.

## Typed rule registry

`proof_compiler.py` migrates the renderer's implemented vocabulary into immutable `RuleSpec` records containing:

- operator name;
- pointwise, collective, multi-output, or special kind;
- input/output/parameter cardinality;
- denotation function;
- applicable `applyNode` lemmas;
- output projections;
- exact/allowed input and parameter cardinalities derived from the Lean lemma signatures;
- rank sensitivity;
- relation effect (`preserve`, `collective`, `project`, or `special`).

The planner rejects unknown operators and signature mismatches before producer indexing, so secondary graph effects cannot hide the first real unsupported node.

## Graph-wide certificate DAG

The planner starts from the public SM output and every rank-local PM output. It follows producer dependencies back to `InitShapes`, emits a deterministic topological certificate DAG, and fails closed on:

- unknown rules;
- rule signature mismatches;
- non-equivalent duplicate producers;
- missing producers or undeclared external inputs;
- cycles;
- malformed lineage piece/shape declarations.
- non-positive/out-of-range graph ranks, or lineage ranks that are not a strictly
  increasing in-range subset (rank-local targets need not cover every graph rank);
- duplicate `InitShapes` tensor IDs (Lean shape lookup is first-match);
- lineage rank-to-final-ordered-writer mismatches;
- out-of-range gather dimensions or piece shapes that do not reconstruct the SM target shape.

Each node must also have distinct output tensor IDs. List collectives consume
exactly `GraphDecl.numRanks` inputs; singleton collectives consume exactly one.
Dimension-bearing collectives must have known ordered input shapes, in-range
dimensions, compatible piece shapes, and divisible chunk extents. Every final
SM/PM target writer must also have an inferred shape exactly equal to its
lineage declaration; unknown target shapes fail closed. Shape inference is
operator-specific: notably `FW_sum` yields `[1]`, while `FW_add` validates
right-aligned broadcast compatibility and uses the per-dimension maximum.
Every output-producing supported node must have a registered inference result;
an unknown intermediate shape cannot be washed through a later reduction.
`FW_multiref` additionally requires `params[0] >= outs.length`, matching its
Lean well-formedness theorem.
Parameterized offset embeddings are rejected until they have a separate typed
rule with the `fw_embedding_offset` denotation and matching apply lemma.

Equivalent rank-insensitive rewrites are accepted only when operator, inputs, outputs, and parameters are identical. In-place collectives are accepted only when they consume the overwritten tid.

`denoteGraph` is an ordered fold. Every read therefore binds to the latest
writer strictly before that node; the planner never repairs a graph by moving a
future producer earlier. Cycle diagnosis may inspect a future writer only when
there is no earlier writer or declared input.

## Registered full-topology composition rule

`composer.py` currently registers one complete generic rule:

```text
embedding-hidden-alltoall-two
```

It recognizes:

- one SM `FW_embedding`;
- two rank-local PM `FW_embedding` nodes over equal hidden-dimension weight shards;
- two rank-local `AllToAllPrim` nodes with `(idim=1, odim=0)`;
- a dimension-0 reconstructed public output;
- no computed prerequisite boundary.

All tensor ids and dimensions are derived from `GoalIR`. The generated theorem uses the generic `fw_embedding_hidden_shards_allToAll_two` library theorem and does not import or invoke the handwritten `Pattern_5.prove_goal_5` proof.

The matcher also verifies literal graph rank headers (`SM=1`, `PM=2`), rank
membership, distinct tensor roles, and the exact token/weight `InitGoal`
lineages consumed by the generated proof, including full-init membership,
piece order, ranks, shapes, gather dimension, and positivity side conditions.

`emit2.py` writes source bytes to a sealed Linux memfd and runs Lean through the
inherited `/proc/self/fd/<fd>` path, so the checked bytes cannot be changed and
restored during checking. It copies only those sealed bytes into an anonymous
`O_TMPFILE` inode on the destination filesystem, creates a cryptographically
random anchor from that held inode with `linkat`, then verifies the anchor inode
immediately inside the direct dirfd `renameat2` wrapper. The requested final path
is not resolved through a symlink. It opens the published destination and
rechecks the same inode and bytes before returning success. Cleanup only unlinks
a residue whose inode still equals the invocation-owned inode; unrelated
replacement entries are preserved.

The checker and Python process image are in the trusted computing base. Arbitrary
same-process monkeypatch/code injection can replace any syscall wrapper and is
outside this filesystem race contract; the checker receives only the sealed FD
path, never the publication anchor name. The destination directory is held under
an advisory `flock`, so cooperating compiler publishers serialize. Linux has no
primitive that atomically replaces an existing directory entry conditionally on
a held source inode; therefore untrusted same-UID processes that ignore the lock
and mutate the destination directory are also outside the publication threat
model. This boundary is explicit rather than disguised as an inode-bound rename.
`--no-compile` remains the explicit
source-only exception and does not claim kernel checking.

The current YOCO Goal 5 is the first real accepted instance. Its generated certificate is Lean-checked and deterministic.

## Current limitation

This is not yet a fully general model proof compiler. YOCO Goals 1–4 currently stop at the first unregistered operator (`FW_float` in the current authority), before any source mutation or Lean generation. Additional progress must add generic operator/relation rules and composition families, not per-Goal or per-layer proof files.

YOCO-3B remains held out. A valid clean-room acceptance run requires:

```text
model-specific handwritten Lean = 0
source edits after invocation = 0
unsupported/false obligations = first real node
full theorem = Lean checked
rerun = byte-for-byte deterministic
```

Do not weaken statements, introduce computed-boundary hypotheses, guess ownership from shape, or model value-sensitive collectives as identity to increase apparent coverage.
