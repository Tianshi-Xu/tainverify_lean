# One-command proof compiler requirements

## Goal

TrainVerify must become a proof compiler for supported distributed networks.
Given a single-model graph (SM), a parallel/distributed graph (PM), authority metadata, and an installed semantic rule library, one command must either:

1. emit and kernel-check a complete faithful-equivalence proof; or
2. fail closed with the first unsupported or false obligation localized.

Success must not depend on handwritten tensor IDs, node indices, layer numbers, or model-specific proof files.

## Supported-input contract

A network is supported when:

- every graph operator has a faithful `evalOp` denotation;
- every distribution/ownership transformation used by the graph has a registered relation rule;
- required input well-formedness facts are expressible as explicit caller contracts;
- process-group scope, rank ownership, shapes, and authority provenance are available in the input artifacts.

A new operator or layout may require extending the library. A new composition of already-supported operators and layouts must not require new Lean proof code.

## Required pipeline

The compiler must perform these stages deterministically:

1. **Authority validation**
   - verify pinned source revisions and artifact hashes;
   - parse the complete SM/PM graphs without silent fallback;
   - reject ambiguous producer, replica-group, or ownership information.

2. **Goal generation**
   - emit graph declarations, observable goals, intermediate obligations, and provenance;
   - preserve false or inexpressible authority goals as findings rather than shrinking the denominator.

3. **Relation inference**
   - infer a typed relation for every relevant tensor edge, including replication, contiguous sharding, zigzag/permuted ownership, expert partitioning, and partial reductions;
   - propagate explicit shape and value side conditions;
   - never replace a value-sensitive collective with an identity relation merely to make composition succeed.

4. **Rule selection and side-condition discharge**
   - select registered local semantic rules from operator, relation, and topology data;
   - discharge finite graph facts by generated certificates;
   - surface genuine runtime/input requirements as named statement-level contracts with satisfiability witnesses where appropriate.

5. **Certificate composition**
   - generate an explicit proof-certificate DAG whose nodes identify the authority graph facts, local rule, premises, and output relation;
   - check the DAG using generic Lean composition theorems;
   - keep generated proof text independent of model-specific numeric naming conventions.

6. **Kernel and claim audit**
   - build from a clean checkout/cache boundary;
   - reject `sorry`, `admit`, unexpected axioms, theorem-header drift, stale generated files, and provenance mismatch;
   - report faithful coverage over the original full corpus.

## Failure contract

Failure is a product result, not a generic “proof failed”. The command must distinguish:

- `unsupported_operator`: missing faithful denotation;
- `missing_relation_rule`: semantics exist but no local distribution theorem applies;
- `missing_input_contract`: the proof requires a real harness invariant;
- `ambiguous_authority`: graph/provenance/ownership data are insufficient;
- `false_goal`: a concrete semantic or layout counterexample was found;
- `certificate_bug`: generated certificate rejected by Lean;
- `kernel_or_trust_failure`: unexpected axiom, `sorry`, or statement drift.

Diagnostics must identify the first failing SM/PM nodes and tensors, the expected relation, the actual inferred relation, and the rule candidates considered. When executable finite semantics permit it, `false_goal` should include a minimized counterexample.

## Trust boundary

The trusted result is the Lean theorem checked by the pinned Lean kernel and the repository's explicitly documented baseline axioms. Python generators are untrusted producers of declarations and certificates. Their output must be fully checked; generator success is never proof success.

No route may improve automation by weakening the theorem, dropping graph obligations, hiding a collective premise, or using a value-lossy denotation on the faithful track.

## Acceptance test

The requirement is satisfied only by a clean-room test on at least one network architecture that was not used to author or tune the compiler:

1. start from a fresh checkout with no model-specific proof files;
2. provide only SM/PM authority artifacts and declared input contracts;
3. run one documented command;
4. make no source edits between invocation and result;
5. obtain either a complete kernel-checked proof or a correctly classified localized failure;
6. rerun byte-for-byte deterministically;
7. mutation-test the pipeline by corrupting one operator, ownership relation, side condition, and certificate, confirming each is rejected at the expected stage.

Repeated layers of an existing model are useful regression cases but do not count as this unseen-architecture acceptance test.

## Current gap

YOCO-MoE validates the scale and expressiveness of the denotational foundation and provides a large regression corpus. It does not yet meet this specification. The highest-priority reusable work is therefore:

1. a typed relation/rule registry;
2. graph-wide relation inference;
3. certificate synthesis and generic composition;
4. structured failure diagnosis and counterexample extraction;
5. a single clean-room driver and unseen-network acceptance suite.

Further model-specific proof expansion should be justified by how it closes one of these reusable gaps.
