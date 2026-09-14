# Development

Start with the [project scope](README.md), [architecture](docs/ARCHITECTURE.md),
and [contribution rules](AGENTS.md). This guide distinguishes low-cost entry
checks from proof acceptance. It is not a one-command model verifier.

## Prerequisites and private outputs

Use a prepared Python environment. The capture/backend dependency is
**`nnscaler==0.9+internal.1`**, as recorded in
[requirements-capture.txt](scripts/requirements-capture.txt). Obtain the
team-managed wheel or source and its approved Torch/CUDA dependencies from the
dependency maintainer. This is not a publicly installable wheel promise;
there is no compatibility matrix implied here. The checked-in
`nnscaler_genmodel/` directory is a historical snapshot, not the maintained
installation. Record the actual import location and source/package identity
when doing capture work; a version string alone is not provenance.

Python 3.11 is used by [CI](.github/workflows/lean_action_ci.yml); pytest is
needed for the checks below. Lean and mathlib are pinned by
[lean-toolchain](trainverify/lean-toolchain) and
[lakefile.toml](trainverify/lakefile.toml). Provision that toolchain and its
dependencies before a build; do not upgrade pins to work around a failed proof.
Report missing prerequisites rather than silently skipping affected checks.

Choose your own absolute paths; `TV_CHECKS` must be a fresh, private directory
outside the source tree and outside all accepted artifacts:

```bash
TV_ROOT=/absolute/path/to/tainverify_lean
TV_PY=/absolute/path/to/prepared/environment/bin/python
TV_CHECKS=/absolute/path/to/new-check-directory
mkdir -p "$TV_CHECKS"
cd "$TV_ROOT"
export PYTHONDONTWRITEBYTECODE=1
export PYTHONPATH="$TV_ROOT:$TV_ROOT/Verdict"
```

Keep generated Lean, caches, logs, and receipts external unless a particular
owned library build requires its package-local Lake output. Never direct new
builds at accepted object caches. Only load pickle captures from trusted,
explicitly authenticated local inputs.

## Discover the actual CLI surface

These commands request help only: no capture, compiler run, or Lean build.
They expose existing entry points rather than another umbrella planner.

```bash
"$TV_PY" -m Verdict.graph_to_lean --help
"$TV_PY" -m trainverify.bridge_emitter.emit2 --help
"$TV_PY" -m trainverify.artifact_tools --help
"$TV_PY" -m trainverify.frontier_replay --help
"$TV_PY" -m trainverify.canonical_run run --help
"$TV_PY" -m trainverify.canonical_run recheck --help
"$TV_PY" -m trainverify.canonical_contract_prepare --help
"$TV_PY" -m trainverify.artifact_contracts render --help
"$TV_PY" -m trainverify.artifact_contracts check --help
"$TV_PY" -m trainverify.artifact_contracts compare --help
```

| Entry | What a real invocation does; limits |
| --- | --- |
| `Verdict.graph_to_lean` | Imports SM/PM graph authority and emits Lean definitions/goals; requires explicit `--out` and `--module`. The opt-in runtime-world path still stops at `RuntimeLineageBlocked`. |
| `trainverify.bridge_emitter.emit2` | Uses graph-authority planners and shared DAGs. `--whole-model`, `--targets`, `--model-id`, and `--parallel-config` select existing supported contracts, not arbitrary-network support. |
| `trainverify.artifact_tools` | Resolves explicit layouts, checks pinned files/historical receipts, renders joints, and offers direct Lean checks. Integrity readback alone is not a new proof. |
| `trainverify.frontier_replay` | Replays an explicitly pinned local frontier from saved captures and stops before canonical publication. Requires a clean source commit; not a substitute for a full canonical run. |
| `trainverify.canonical_run` | `run` observes real generation through publication; `recheck` rereads existing pinned evidence without rerunning it. Bookkeeping success retains the expected public-unproved compiler exception. |
| `trainverify.canonical_contract_prepare` | Prepares independently pinned reference fragments and cumulative joints; never runs Lean and never marks the candidate admissible. |
| `trainverify.artifact_contracts` | `render`, `check`, and `compare` use explicit target manifests and complete Expr records. A comparison is not itself a kernel invocation. |

For actual inputs and no-clobber outputs, follow
[artifact tooling](docs/artifact-tools.md),
[canonical run](docs/canonical-run.md), and
[reference preparation](docs/canonical-contract-prepare.md).
The canonical-run document's old "baseline alone does not attach" warning
describes its pre-attachment checkpoint: the current source attaches score
matmul and score AA. Do not rewrite the historical record or use its old
baseline with new stage expectations.

Canonical observation requires an approved, sealed source materialization
and complete source manifest, pinned recipe/layout/stage expectations, and a
fresh external output root. It is not a command to run against a mutable
checkout with `.git` and caches. Recheck uses the original pinned source and
observer, not an arbitrarily updated implementation. Graph-authority
configuration requirements are described separately in
[parallel authority](docs/PARALLEL_CONFIG_AUTHORITY.md).

## Focused Python and source-only checks

Run the smallest relevant tests first. The developer-entry check exercises
real CLI help and local documentation navigation without optional-tool skips:

```bash
"$TV_PY" -m pytest scripts/tests/test_developer_entry_docs.py -q -p no:cacheprovider \
  --basetemp="$TV_CHECKS/tmp" --junitxml="$TV_CHECKS/junit.xml" \
  >"$TV_CHECKS/stdout.txt" 2>"$TV_CHECKS/stderr.txt"
status=$?
printf '%s\n' "$status" >"$TV_CHECKS/exit.txt"
```

Read both logs and the exit status; writing a receipt does not mean the check
passed. Use a new output directory for each attempt. Other focused tests live
in [Verdict/tests](Verdict/tests/), [scripts/tests](scripts/tests/), and
[trainverify/tests](trainverify/tests/); select those relevant to your change
instead of starting a capture or the entire historical campaign.

The deterministic certificate check is separate and source-only, also from
`TV_ROOT`:

```bash
"$TV_PY" trainverify/scripts/generate_multiref_certificates.py --check
```

It compares deterministic certificate text and does not rewrite authority.
Capture regeneration instead needs the revisions and artifact hashes in
[GeneratedYOCOMoE.manifest.json](trainverify/denote/GeneratedYOCOMoE.manifest.json);
never hand-edit generated authority or derive new expected pins from changed
inputs.

## Historical coverage diagnostic

```bash
"$TV_PY" trainverify/scripts/count_yoco_faithful_coverage.py
```

This historical-checkpoint script counts exact theorem names and source
declarations; it does not invoke the kernel. On the current checked-in corpus
it **fails with exit 1**, reporting `unexpected corpus size: 1096` against its
historical expected 1,156. The same failure occurs on the original cleanup
baseline, not just the documentation candidate.

Do not use this command as a clean-checkout success gate or treat its current
name count as a new proof-coverage assessment. The reported historical
649 ordinary / 505 zigzag / 2 false-finding checkpoint remains a historical
claim, not a result reproduced by this invocation. Resolving the script/corpus
checkpoint mismatch is separate work: do not change the expected denominator,
delete negative controls, or rewrite generated authority to obtain a green
status.

## Lean: stub, smoke, and release gate

The Lake default target **`Trainverify`** only imports
[Trainverify.Basic](trainverify/Trainverify/Basic.lean), whose example is
`hello := "world"`. Thus bare `lake build` is a **Basic/hello stub build**, not
a build of the verification library.

In an owned build environment, this is the bounded push/PR CI kernel smoke:

```bash
cd "$TV_ROOT/trainverify"
lake build denote.GraphGears denote.MultirefCertificate \
  denote.yoco_goals.MultirefCertificateRegression
```

The actual library and full corpus release gate is separate:

```bash
cd "$TV_ROOT/trainverify"
lake build denote
```

The full CI lane is manual (`workflow_dispatch`, `full=true`); push/PR smoke
is not the full release gate. These builds are resource-bearing operations,
not part of CLI-help or documentation checks. A developer-entry check does
not exercise either command and must not be reported as a Lean PASS.

For proof changes, first check the affected modules and authenticated
dependency closure, retaining exact source/object/import/axiom evidence.
Reuse unchanged accepted objects instead of rebuilding them to repair
bookkeeping. Full-library builds belong at the agreed release milestone;
even that build does not establish whole-model/public acceptance, successful
whole-capture execution, or Torch refinement.
