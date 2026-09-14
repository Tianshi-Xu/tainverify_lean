# Architecture and proof boundaries

TrainVerify relates a single-model graph (**SM**) to a distributed execution
graph (**PM**). A useful result must say which source graphs, layout authority,
mathematical evaluator, caller contracts, and axiom policy it covers. A
generated theorem name or successful process is not enough.

See [Development](../DEVELOPMENT.md) for commands and prerequisites, and the
[landing page](../README.md) for the current scope. The following routes
coexist; they are not aliases for one shared Python planner.

## Original SMT route

[Verdict/verdict](../Verdict/verdict/) contains graph abstractions, lineage
alignment, stage cutting, and `StageParallelVerifier`.
[nnscaler_backend](../Verdict/nnscaler_backend/) loads the execution graphs;
[z3_backend](../Verdict/z3_backend/) supplies symbolic reasoning for the
original SMT verifier. An SMT result is not a Lean kernel receipt.

The [Verdict/main.py](../Verdict/main.py) entry performs **graph inspection**:
it requires explicit SM/PM capture files plus private cache/log directories,
calls `get_graph()` to load both graphs, and prints SM operations and shapes.
It does not call the verifier's `launch()` verification pipeline. Import/help
are dependency-lazy; executable loading still needs the prepared nnScaler/Z3
backend environment and can write rank-cell caches. Trusted local pickle
inputs can execute arbitrary code. Exit 0 is an inspection result, not an
SMT proof, Lean receipt, capture-provenance check, or whole-model acceptance.
See [the inspection commands](../DEVELOPMENT.md#graph-inspection-of-trusted-local-captures).
The Lean exporter lives separately in
[graph_to_lean.py](../Verdict/graph_to_lean.py).

## Graph-authority bridge compiler

```text
SM/PM graph declarations + explicit model/topology authority
  -> model authority and target projections
  -> typed rule/certificate planners and shared proof/relation DAGs
  -> closed segments and shared-prefix composition
  -> emit2 generation, exact-source kernel/contract/publication gates
```

[model_compiler.py](../trainverify/bridge_emitter/model_compiler.py) already
organizes model-level shared DAGs.
[proof_compiler.py](../trainverify/bridge_emitter/proof_compiler.py) and
[relation_compiler.py](../trainverify/bridge_emitter/relation_compiler.py)
provide typed rules, certificates, registries, and planning.
[emit2.py](../trainverify/bridge_emitter/emit2.py) consumes this route; it is
not a missing planner that needs replacing with a third compiler.

[Parallel authority](PARALLEL_CONFIG_AUTHORITY.md) binds source-derived
configuration, ordered groups, graph scope, and rank coordinates to model
authority. It does not prove that a capture came from that configuration.
Absent collective metadata differs from an explicitly empty table; a valid
group layout unsupported by a backend must remain a localized rejection.

Historical graph/native receipts include generated `native_decide` and their
recorded additional axioms. They must not be relabelled kernel3. Some
mathematical dependencies still live under model directories; neither a
registry nor a Whole artifact establishes model-independent support for all
graphs. The [branch-consolidation record](BRANCH_CONSOLIDATION_2026-09-14.md)
also identifies a still-unresolved legacy export heuristic that infers
replication from piece counts/shapes. Equal shapes alone do not prove equal
values; that finding must not be conflated with accepted runtime replica facts.

## Source-bound runtime route

```text
original source fullrefs + writer calls + ordered schedule
  -> runtime world definitions
  -> bound input/parameter/seed authority
  -> source reads, Store prefixes, continuation/frame and value facts
  -> ordered frontier attachment and canonical bundle publication
  -> intentional public-unproved boundary
```

[runtime_source_authority.py](../trainverify/runtime_source_authority.py)
identifies a tensor by world, runtime rank, microbatch, source TID, and
version; writer identity also binds the original operation/call.
A raw TID or same-shaped tensor is not an adequate source identity.
[runtime_lineage.py](../Verdict/runtime_lineage.py) traces and consumes typed
pieces, endpoints, and unit relations; inferred relations are not
automatically caller assumptions.

The public control flow is
[graph_to_lean](../Verdict/graph_to_lean.py) ->
[runtime_world](../Verdict/runtime_world.py) ->
[runtime_input_feed.bind](../Verdict/runtime_input_feed.py) ->
[runtime_initial_relations.attach](../Verdict/runtime_initial_relations.py) ->
world publication. Input, batch, parameter, and seed records bind real
initial sources; observed outputs must not become premises for the values
being proved.

The current canonical attachment order is sequence aliases, QKV
projection/layout, post-transpose, K AllToAll(2 -> 1), ordered Q/K score
matmul, then PM score AllToAll(1 -> 3). Both following divisions are
**inventory-only**, not consumed value stages. Complete V per-DP replica
equalities and both residual carries survive the score frontier; replication
is not represented using a fabricated gather axis.

These facts are conditional on the original common full SM/PM runs and
initial-parameter hypotheses. A conditional theorem is not a witness that
those runs succeed. Remaining saved-primal/activation dependencies and
whole-model/public closure are not established by existing backward readers
or local dX/dW results.

`RuntimeLineageBlocked` is the intentional current public boundary, not an
exception to suppress. [canonical_run](canonical-run.md) can report
bookkeeping `passed=true` only after the real generation/publication path and
its exact expected exception; the underlying compiler exit remains 1.
The observer's kernel/public/refinement flags remain false. Independent
acceptance binds the actual emitted bytes to external proof evidence.

## Common mathematics and authority

[Denote.lean](../trainverify/denote/Denote.lean) defines tensors, stores,
graph declarations, and mathematical execution; `Scalar` is Lean's real
numbers (`Real`). This is not an IEEE-floating-point Torch/CUDA model.
[SourceScopedEval](../trainverify/denote/SourceScopedEval.lean) and
[SourceScopedPrefix](../trainverify/denote/SourceScopedPrefix.lean) support
source-scoped execution and continuation/frame reasoning.
Distributed faithful, group-scoped, and source-scoped evaluators make
different assumptions about the information available across ranks.

Shared mathematics and authority principles do not make those evaluators,
registries, or acceptance policies interchangeable. Preserve full rank/group
ordering, global and every-local shape, actual operand values, parameter
ownership, and all retained facts. dX and dW require distinct relations;
weights themselves may be sharded. Graph slices must preserve InitGoal
bridge writers rather than turn computed values into unconstrained leaves.

The latest runtime canonical checkpoint uses only `propext`,
`Classical.choice`, and `Quot.sound` (**kernel3**). This is a route-specific
acceptance boundary, not a claim that all historical files use kernel3, that
the entire corpus is free of unfinished proofs, or that a current full build
has been rerun. Do not introduce value-lossy identity models, axioms, or extra
output hypotheses to make an unsupported operation appear proved.

## External artifacts and the meaning of evidence

The [2026-09-14 handoff](HANDOFF_2026-09-14.md) reports the attached score
checkpoint as 131 modules / 2,498,512 source bytes, with 549 full Expr and
527 joint Expr comparisons. These are recorded conditional acceptance
results, not measurements made by reading this repository. The aggregate
source gate remains strictly less than 2,500,000 bytes.

Git source alone does not contain everything needed to reproduce that
acceptance. Trusted saved captures, rank code, batch/seed/parameter receipts,
exact generated sources, predecessor objects and transitive dependencies,
kernel logs, full contract records, and independent reviews require explicit
handoff. Accepted artifacts and historical failures are immutable inputs.

[Artifact tools](artifact-tools.md) resolve old logical paths through
operator-owned layouts without changing original expected hashes.
[Frontier replay](../trainverify/frontier_replay.py) stops at a local hook;
canonical observation follows the full generation path.
[Reference preparation](canonical-contract-prepare.md) is source-only;
[artifact_contracts](../trainverify/artifact_contracts.py) observes and
compares explicit full target manifests, including private declarations.
These tools have distinct jobs; none substitutes for another gate.

Keep generation, exact source/object/import binding, kernel/axiom acceptance,
full theorem-contract preservation, public admission, execution inhabitation,
and implementation refinement separate. Historical receipts preserve what
was checked and what failed. New results need private outputs and honest
unverified items, not rewritten receipts or a green flag borrowed from a
different route.
