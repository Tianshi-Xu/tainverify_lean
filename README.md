# TrainVerify

TrainVerify studies whether a distributed training graph (PM) implements its
single-model reference (SM). This repository, **tainverify_lean**, extends the
original SMT-based TrainVerify with Lean denotational semantics, explicit
ownership relations, proof rules, and source-bound proof generation.

## What is established, and what is not

The current runtime canonical path attaches QKV projection/layout facts,
Q/K score matmul, and PM score AllToAll(1 -> 3). Both following divisions remain
**inventory-only**. Its public entry intentionally raises
`RuntimeLineageBlocked`: conditional frontier proofs are not a complete public
equivalence proof or a witness of successful whole-capture execution.

The mathematical corpus remains valuable. The reported historical
YOCO-MoE-A0.4B checkpoint has 649 ordinary and 505 zigzag faithful obligations,
with two false ordinary-gather targets retained among 1,156 obligations.
Historical GPT and YOCO Whole results also exist under their recorded
authority, statements, and trust policies. These are scoped contributions,
**not arbitrary-network one-command completion or Torch/CUDA refinement**.
Different proof routes do not have interchangeable evaluators or axiom policies.

## Start here

| Entry | Purpose |
| --- | --- |
| [Architecture](docs/ARCHITECTURE.md) | SMT, graph-authority, and runtime routes; mathematics and trust boundaries |
| [Development](DEVELOPMENT.md) | Prerequisites, real CLI entry points, focused checks, and build gates |
| [Contribution rules](AGENTS.md) | Authority-first changes and evidence discipline |
| [Artifact tooling](docs/artifact-tools.md) | Explicit layouts, pinned external inputs, replay and object checks |
| [Workstream ledger](WORKSTREAMS.md) | Dated integration checkpoints and ownership, not a quick-start script |

Code lives in [Verdict](Verdict/) (graph import, SMT and runtime export),
[bridge_emitter](trainverify/bridge_emitter/) (graph-authority compiler), and
[denote](trainverify/denote/) (Lean mathematics and model corpus).
[Scripts](scripts/) and [library scripts](trainverify/scripts/) contain focused
regressions, deterministic generators, and coverage checks.

## Verification is not one gate

Use a prepared environment and private outputs as described in
[Development](DEVELOPMENT.md). Python checks, source coverage, kernel checking,
and public acceptance answer different questions:

```bash
"$TV_PY" -m pytest scripts/tests/test_developer_entry_docs.py -q -p no:cacheprovider \
  --basetemp="$TV_CHECKS/tmp" --junitxml="$TV_CHECKS/junit.xml"
"$TV_PY" trainverify/scripts/generate_multiref_certificates.py --check
```

The [historical coverage diagnostic](DEVELOPMENT.md#historical-coverage-diagnostic)
currently rejects the checked-in corpus; it does not reproduce the historical
counts above and is not a clean-checkout success gate.

In the `trainverify/` package, bare `lake build` selects **`Trainverify`**, only
a Basic/hello stub. The actual library is **`lake build denote`**. Push/PR CI
builds a bounded Lean smoke, not that full corpus; the full library build is a
separate release gate, not proof of every system-level claim.

## Historical context

The [2026-09-14 handoff](docs/HANDOFF_2026-09-14.md) records contributions,
conditional acceptance, and open obligations. The
[branch-consolidation record](docs/BRANCH_CONSOLIDATION_2026-09-14.md) explains
retained prototypes, archives, and the unresolved legacy replication heuristic.
These records preserve historical paths and commands; do not execute them as
current setup instructions. [Proof-compiler requirements](docs/PROOF_COMPILER_REQUIREMENTS.md)
and [three-model acceptance](docs/THREE_MODEL_PROOF_COMPILER_ACCEPTANCE.md)
describe goals, not a completed product or an installation promise.
