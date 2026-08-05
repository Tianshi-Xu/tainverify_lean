# Generic proof-compiler IR (schema version 1)

This document specifies the first reusable vertical slice of the one-command
proof compiler. It replaces model-specific tensor/node names with a typed graph
and relation IR. It does **not** yet claim a kernel-checked network theorem; the
next stage consumes the emitted certificate DAG in Lean.

## Command

```bash
python3 trainverify/scripts/proof_compile.py \
  --job graph-job.json \
  --library semantic-library.json
```

The command writes one deterministic, key-sorted JSON object to stdout. Exit status
is `0` for a certificate and `2` for a structured failure. It never modifies the
repository. Input decoding rejects duplicate object keys and non-finite numbers;
output uses strict RFC JSON (`NaN`/Infinity are disabled).

## Job

A job contains:

- `schema_version`: exactly `1`;
- `num_ranks`: positive integer;
- `target_manifest_sha256`: SHA-256 of the key-sorted compact JSON encoding of
  the authority-provided `observables` list;
- `sm_nodes`: topologically ordered logical nodes of the single-model graph;
- `pm_nodes`: exactly one node per logical ID and rank;
- `input_relations`: relations for actual graph inputs only;
- `observables`: requested SM/PM tensor mappings and optional expected relation.

Every node has `logical_id`, `rank`, `op`, `ins`, and `outs`, plus an optional
`attrs` object containing all semantic operator parameters. Logical IDs align
SM nodes with their rank-local PM realizations. The compiler rejects duplicate
producers, duplicate SM logical IDs, missing/extra PM groups, incomplete rank
groups, arity mismatch, non-topological relation dependencies, and PM inputs
that do not consume the tensors named by their inferred premises. Rules declare
exact `sm_attrs` and `pm_attrs` payloads (default `{}`); unknown node fields and
attribute mismatches fail closed rather than being ignored.

## Typed relations

Relations are closed variants, not arbitrary labels:

- `{"kind":"equal"}`
- `{"kind":"replicated"}`
- `{"kind":"contiguous_shard","dim":D,"parts":P}`
- `{"kind":"zigzag","dim":D,"parts":P,"block_size":B}`
- `{"kind":"expert_partition","dim":D,"parts":P}`
- `{"kind":"partial_reduction","op":"sum|mean","parts":P}`
- `{"kind":"permuted_ownership","permutation":[...]}`

A seed of every relation kind carries a closed, content-addressed authority,
value-mapping, and ownership witness. Replicated seeds additionally prove the
same value across the exact complete rank set. Equal shapes and `FW_multiref`
identity fan-out are explicitly insufficient. Rule applications may preserve an input relation with
`{"from_input":i}` or prove a typed transition by naming an explicit output
`relation` and Lean theorem.
All relation variants validate tensor cardinality, unique/in-range ranks, and
their declared `parts` or permutation against seeds, rule outputs, and goals.

## Semantic library

The library contains:

- `denotations`: one faithful Lean definition per operator;
- `rules`: uniquely named relation rules with exact typed input relations,
  output transfers, and a Lean theorem name.

Lean names are required to be nonempty qualified symbols, but are still
unresolved references until the later Lean checker stage. No rule is selected
by substring or model name. Zero matches produces
`missing_relation_rule`; multiple exact matches produces `certificate_bug`.

## Certificate DAG

Each inferred relation is one DAG node:

- seed nodes record authority/value/ownership provenance;
- rule-application nodes record SM/PM graph facts, the selected theorem,
  relation premises, output tensor mapping, and output relation;
- observables reference a DAG node ID.

The certificate envelope records `num_ranks`, `target_manifest_sha256`, and the
original `target_observables`. Independent validation still requires these as
trusted authority context; it never infers rank count from mutable PM mappings
or accepts the certificate's self-reported target binding as its own trust root.

IDs and all premise/observable references are checked for uniqueness, schema,
payload coherence, and topological closure before success is returned. Empty
goal sets are rejected, and the compiler recomputes `target_manifest_sha256` so
removing or changing an observable invalidates the authority binding.
Rule-application nodes are also resolved again against the installed semantic
library: rule name, theorem symbol, SM/PM operators and attrs, premise relations,
denotations, and output transfer must all match exactly.

## Structured failures

The slice currently emits the requirement categories:

- `unsupported_operator`
- `missing_relation_rule`
- `missing_input_contract`
- `ambiguous_authority`
- `false_goal`
- `certificate_bug`

Failures identify the first graph node/tensor and include the inferred relation,
expected relation, rule candidates, or minimized tensor-mapping counterexample
where applicable.

## Remaining trust boundary

Python output is untrusted. A complete proof-compiler result still requires:

1. Lean declarations for the closed relation variants;
2. a generic Lean checker/composer for every certificate node;
3. theorem-name resolution against the installed rule library;
4. authority hash verification and side-condition certificates;
5. clean-cache kernel build, axiom/sorry/header audit;
6. an unseen-architecture clean-room acceptance run.

Until those land, `status=certificate` means “closed, validated certificate IR”,
not “kernel theorem proved”.
