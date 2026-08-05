# Proof compiler Lean kernel slice

This slice turns a validated Python certificate IR into a Lean theorem over the
repository's concrete `Tensor`, `denoteGraph`, and operator denotations.

It is deliberately narrower than the Python relation-inference layer. Unsupported
semantics fail before source publication.

## Reproducible command

From the repository root:

```bash
python3 trainverify/scripts/proof_compile_lean.py \
  --job trainverify/tests/fixtures/proof_compiler_kernel/job.json \
  --library trainverify/tests/fixtures/proof_compiler_kernel/library.json \
  --output /path/that/does/not/exist/GeneratedCertificate.lean \
  --namespace GeneratedFixture \
  --check \
  --lean-root trainverify
```

The command performs, in order:

1. strict JSON decoding and Python certificate synthesis;
2. final certificate-DAG and authority-context validation;
3. fail-closed Lean source emission;
4. `lake env lean` kernel checking on a temporary file;
5. inode/size/content revalidation after the kernel process;
6. atomic no-replace hardlink publication and directory `fsync` only after acceptance.

The output directory must be owned by the current user and must not be group- or
world-writable. Existing files and symlinks, including broken symlinks, are rejected.
A publication-stage failure rolls back the linked output.

Success emits canonical JSON with `status="kernel_certificate"`. Invalid JSON,
unsupported semantics, a missing/forged theorem, kernel rejection, or an existing
output path returns exit code `2` and publishes no artifact.

## Kernel semantics

`denote/ProofCompilerRelation.lean` defines:

- `Relation.equal`: exactly one PM value, equal to the SM value;
- `Relation.replicated`: exactly `numRanks` PM values and every value equals SM;
- `Relation.contiguousShard dim parts`: exact declared-part cardinality (including
  sub-communicators with `parts ≤ numRanks`) and SM equals the existing concrete
  `allGatherPrimDimN` reconstruction;
- `RuleHolds`: a rule theorem over a fixed value-level operator semantics;
- `CertifiedRelation`: a relation claim carrying its Lean proof;
- `applyRule`: certificate-DAG composition checked by Lean's type system.

The current semantic family is `kernel_semantics={"kind":"unary_map"}`. It requires
one premise, unary singleton-output SM/PM nodes, empty attrs, the same installed
Lean denotation on SM and PM, and an installed theorem of the exact `RuleHolds`
type. The included `FW_contiguous` theorem uses the faithful repository definition
`fw_contiguous = tensorId`.

Generated theorems refer to actual `denoteGraph` values at the certificate TIDs.
The emitted SM graph has one rank and the PM graph uses authority `num_ranks`.
A forged theorem symbol therefore fails Lean elaboration rather than being accepted
because a string matched.

## Authority boundary

Seed relations are explicit hypotheses of the generated theorem. This is honest:
the kernel checks all rule composition downstream of the seed, but the external
artifact hash/value/ownership witness still needs a generated authority theorem or
verified side-condition certificate. `targetManifestSha256` is recorded in the
module but SHA-256 recomputation is currently performed by the strict Python layer,
not proved inside Lean.

Accordingly, `status="kernel_certificate"` means:

- the emitted conditional theorem was accepted by Lean;
- every emitted rule step has a real value-level theorem;
- it does **not** yet mean the external seed authority itself was proved in Lean.

## Fail-closed unsupported scope

The emitter currently rejects:

- `zigzag`, `expert_partition`, `partial_reduction`, and `permuted_ownership`;
- nonempty semantic attrs / unmapped `NodeDecl.params`;
- non-unary or multi-output rules;
- different SM and PM Lean denotations;
- multiple observables in one generated theorem.

These are not mapped to `False` or guessed from names. They remain unsupported until
faithful value semantics and side-condition certificates are implemented.

## Trust audit

The Lean regression fixture checks equal, replicated, shard, rule composition,
and an unseen-TID one-node graph. `#print axioms` reports only the accepted kernel
baseline:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorry`, `sorryAx`, user axiom, or `native_decide` in this slice.
