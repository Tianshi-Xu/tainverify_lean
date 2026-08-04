# TrainVerify

TrainVerify checks whether a distributed training graph faithfully implements its single-model reference graph. Execution plans are translated into Lean graph declarations, interpreted by a shared denotational semantics, and proved against explicit lineage and ownership relations.

## Project direction

The target is a **proof compiler**, not a collection of model-specific proof scripts:

> Once an operator has a faithful denotation and its local relation rules are registered, an unseen supported SM/PM network pair should produce a complete kernel-checked proof in one command.

Unsupported operators, missing side conditions, and false equivalence goals must fail closed with a localized diagnostic or counterexample. See [Proof compiler requirements](docs/PROOF_COMPILER_REQUIREMENTS.md) for the acceptance criteria.

## Current status

YOCO-MoE A0.4B is the main large-scale case study. Its authority corpus contains 1,156 obligations:

- 649/649 ordinary contiguous-ownership goals are faithfully proved;
- 505/505 CP-zigzag ownership goals are faithfully proved;
- 2 top-level ordinary-gather equalities are retained as false upstream findings.

This demonstrates the semantics and proof-rule foundation, but **does not yet satisfy the one-command, arbitrary-network requirement**. Some YOCO proofs and well-formedness contracts remain model-specific.

## Repository map

- `Verdict/graph_to_lean.py`: SM/PM execution-plan to Lean graph/goal emitter.
- `trainverify/denote/`: denotational semantics, generated authority snapshots, proof rules, and checked model proofs.
- `trainverify/scripts/`: deterministic generators and coverage checks.
- `scripts/`: authority regeneration and comparison tooling.
- `docs/`: design requirements and concise audit records.

## Core verification

From the repository root:

```bash
PYTHONPATH=. uv run --with pytest pytest -q Verdict/tests scripts/tests trainverify/tests
python3 trainverify/scripts/count_yoco_faithful_coverage.py
python3 trainverify/scripts/generate_multiref_certificates.py --check
```

Build the Lean library from its package directory:

```bash
cd trainverify
lake build denote
```

The complete Lean corpus is the release gate. GitHub-hosted push/PR CI runs a
bounded kernel smoke over the core graph gears and generated multiref
certificates. A full hosted build is available through `workflow_dispatch` with
`full=true`; it is intentionally manual because a cold build of the generated
corpus exceeds two hours on the hosted runner. Local or high-capacity-runner
`lake build denote` remains mandatory before release.

The checked-in YOCO authority can be regenerated only from the pinned llm-train/nnScaler revisions and artifact hashes recorded in `denote/GeneratedYOCOMoE.manifest.json`; use the repository regeneration scripts rather than editing generated graph data by hand.

## Trust discipline

- Upstream semantic fidelity takes priority over downstream proof completion.
- Faithful coverage excludes value-lossy evaluators and false statements.
- Generated certificates expose their side conditions and are checked by Lean.
- No model-specific handwritten axiom is accepted as a substitute for a missing semantic rule.
- A green build alone is not a claim: coverage, theorem statements, provenance, and axiom footprints are audited separately.
