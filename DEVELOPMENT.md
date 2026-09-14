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
"$TV_PY" -m trainverify.scripts.count_yoco_faithful_coverage --help
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

The coverage boundary is **historical-only**: default invocation intentionally
rejects with exit 2 and actionable mode guidance, without reading sources or
printing a current percentage. Import and `--help` are safe. Choose explicitly:

```bash
# TV_REPO is a local Git repository containing the pinned historical objects.
# It may differ from TV_ROOT when TV_ROOT is an archive without .git.
TV_REPO=/absolute/path/to/local/git-repository
"$TV_PY" trainverify/scripts/count_yoco_faithful_coverage.py --historical --repo "$TV_REPO"
"$TV_PY" trainverify/scripts/count_yoco_faithful_coverage.py --inventory "$TV_ROOT/trainverify"
```

The tested historical invocation reports **HISTORICAL SOURCE-NAME CHECK** at
fixed commit `ad821ce18494d30b5517a36260faa817fb45cda1`: ordinary `649/649`, zigzag
`505/505`, and `1154/1156` exact-name matches including two nonordinary top
source discoveries in the denominator. The historical 1,156 denominator and
1,154 name expectation are unchanged. The repository is selectable, the commit
is not. Only that commit's generated source and immediate `yoco_goals/*.lean`
blobs are read with local Git `ls-tree`/`show`; no historical Python execution,
checkout, materialization, or network fetch occurs. Missing repositories or
objects fail with instructions, never fall back to current files. This is
**not fresh Lean acceptance**. Name matches cannot establish record-body,
graph, statement, evaluator, or object identity across checkpoints.

Inventory reads only `denote/GeneratedYOCOMoE.lean` below the explicit package
root (omitting the root selects the script's own `trainverify/` package, not the
caller's working directory). It emits deterministic JSON: exact sorted base
target IDs and counts for ordinary intermediate, emitted zigzag, ordinary top,
nonordinary top discoveries, and suppressed nonordinary intermediate discoveries.
`emitted_zigzag` IDs denote declarations with the `_zigzag` suffix. On the tested
current source those counts are **646, 445, 5, 0, 60**, respectively; these are
observations, not success thresholds. The suppressed set is the nonordinary
intermediate comment discoveries minus emitted zigzag IDs, not a retirement list.
Raw comments are **emitter discoveries**, **not verified counterexamples**.

Both modes are **source-only**, **not proof coverage**, and **not kernel verification**.
Inventory never reads theorem files or emits percentages or name-based acceptance
flags. It checks duplicate headers and ordinary/nonordinary consistency rather
than silently dropping IDs. This is a narrow scanner for the emitter's exact
line-oriented headers, not a general Lean parser: record bodies, statement
helpers, comment truth, and Lean syntax/kernel acceptance are not validated.
Missing/unreadable source, unknown target headers, and inconsistent classifications
fail rather than producing a partial successful inventory.

The focused CLI suite also exercises the authentic historical blobs. For an
archive-only source root, set `YOCO_HISTORICAL_REPO` explicitly; otherwise the
suite uses `TV_ROOT` as its Git repository. Missing historical objects fail the
suite, not skip it. Use a fresh external receipt directory as above:

```bash
YOCO_HISTORICAL_REPO="$TV_REPO" "$TV_PY" -m pytest \
  scripts/tests/test_yoco_coverage_cli.py scripts/tests/test_developer_entry_docs.py \
  -q -p no:cacheprovider --basetemp="$TV_CHECKS/tmp" --junitxml="$TV_CHECKS/junit.xml" \
  >"$TV_CHECKS/stdout.txt" 2>"$TV_CHECKS/stderr.txt"
status=$?
printf '%s\n' "$status" >"$TV_CHECKS/exit.txt"
```

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
