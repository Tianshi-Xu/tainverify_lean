# Contributing to TrainVerify

Read [Architecture](docs/ARCHITECTURE.md), [Development](DEVELOPMENT.md), and the
relevant dated [workstream checkpoint](WORKSTREAMS.md) before changing a route.
Historical handoffs and tactic notes are evidence, not current instructions.

1. **Authority first.** Check the actual upstream callable, ordered operands,
   full source identity, rank/group membership, shape, and value semantics.
   Resolve an upstream mismatch before proving downstream claims. Never infer
   value replication from shape equality or launder an unknown source into an
   initial input. Slices must retain writers referenced by InitGoal bridges,
   not just nodes reachable through graph edges.
2. **Preserve contracts and coverage.** Keep mathematical statements, caller
   contracts, original target denominators, false findings, and negative
   controls intact. No added output/value hypotheses, weakened conclusions,
   `sorry`/`admit`, pretend identity semantics, or new `native_decide`/native
   axioms to make a proof pass. Do not raise source caps or hide unsupported
   cases behind a successful flag.
3. **Respect each trust route.** The source-bound runtime gate is kernel3
   (`propext`, `Classical.choice`, `Quot.sound`). Historical graph/native
   acceptance has its own recorded policy; do not relabel it as kernel3 or
   expand either policy during cleanup. Inspect exact theorem contracts and
   axiom footprints. Rendering, kernel acceptance, public completion, and
   Torch refinement are separate claims.
4. **Keep domain distinctions.** dX and dW need their own gradient relations;
   root dX is not full gradient coverage. Weights can be sharded. Preserve
   rank order, global and every-local shape, source versions, all replica
   values, and the distinction between shard reconstruction and replication.
5. **Use rolling TDD.** Start with a focused failing check and real existing
   typed fixtures, then a small helper and one consumer group at a time.
   Before a behavior-preserving refactor, retain old renderer bytes and
   rejections. Do not replace real acceptance with guessed JSON or mocks.
6. **Bind evidence to exact bytes.** Compare complete generated sources,
   metadata, contracts, and retained facts. Reuse authenticated unchanged
   predecessor objects; obtain incremental kernel evidence for changed
   sources and their affected closure. Do not claim a new kernel run for
   identical bytes. Preserve stdout/stderr, exit status, failures, and
   unexercised cases; never count a missing prerequisite or skip as PASS.
7. **Own files and outputs explicitly.** Agree on one writer per shared file.
   Parallel workers need assigned paths and private output/cache directories.
   Accepted snapshots, captures, receipts, and objects are immutable inputs.
   Do not edit frozen controllers or rewrite expected pins to accept new data.
8. **No destructive cleanup.** Do not delete model corpora, archived facts,
   genuine negative controls, or evidence dependencies. No broad resets,
   forceful worktree cleanup, or unrelated reversions. Keep changes bounded,
   reuse existing helpers within their contracts, and do not merge distinct
   planners, registries, or proof routes merely to reduce files.
