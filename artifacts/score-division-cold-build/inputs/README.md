# Score-division source-first cold rebuild

This directory reconstructs the **existing** `ScoreDivFrontierJoint`, including both division units and all six mixed rows. It is not a new capture, new theorem frontier, canonical attachment, or historical object-byte restoration.

## Portable inputs

Publish/review these together:

- `source-manifest.json`
- `minimal-missing-sources.tar.gz` (only the 143 required sources not in reachable pinned public Git)
- `restore.py`, `build.py`, `verify_contracts.py`
- `contract-manifest.json`, `expected-contracts.json`
- `audit_axiom_logs.py`, `expected-module-axioms.json`
- `official-provenance.json`

The accepted generated Lean snapshots are reused **unchanged as candidate source**, not described as newly generated. Ninety-four required sources come from public commit `97547f38242a61d89b30e1970ec8faf64d82a105`; two come from the exact historical commits recorded in the manifest. The manifest's absolute historical paths are provenance metadata only. The portable recipe never opens them.

## Clean build

On Linux x86-64, install Python 3.11 or newer, Git, curl, tar, zstd, and `/usr/bin/time`. Unpack the portable inputs in an empty directory, then run:

```sh
python3 restore.py --build
```

The recipe:

1. fetches public pinned source commits;
2. reconstructs and SHA256-checks **every** required source;
3. downloads and verifies the official Lean 4.32.2 Linux archive (digest also verified against the GitHub release asset);
4. clones Lake's exact pinned packages and obtains their official mathlib cache in a private HOME;
5. invokes direct Lean over only the 239-module task DAG, with at most four workers and one Lean thread per worker;
6. compiles the joint and a full-Expr/axiom probe using only new task objects plus the freshly provisioned official dependencies.

No project-wide `lake build` is used. Only `lake exe cache get` builds its small official cache bootstrap. No task `.olean`, historical `.elan`, or shared old `.lake/packages` tree is an input.

A per-module timeout is 1800 seconds and does not alter theorem statements or the kernel3 axiom policy. Full commands, source/dependency/object hashes, duration and `/usr/bin/time -v` measurements are persisted per module.

## Separate operations

```sh
# Reconstruct source into a second directory, without downloading dependencies:
python3 restore.py --skip-provision --source-output restored-sources
# Build already-restored sources with already-provisioned official dependencies:
python3 build.py --jobs 4 --module-timeout 1800
# Verify the complete compiled joint against the saved full contracts:
python3 verify_contracts.py
```

The builder may resume only its own hash-verified receipts and dependency objects within this private directory. Start in an empty directory to obtain a genuinely cold run. It does not use timestamps as evidence.

## Evidence

`build-receipts.jsonl` records each newly compiled task module. `contract-verification.json` and `contracts.json` record the final contract checks. `complete-import-closure.json` includes the full task, official package and standard-library source closure, independently parsed by pinned Lean's `--src-deps` using `LEAN_SRC_PATH`. `official-files.json` hashes the freshly downloaded toolchain and official package native/object files. `monitor.jsonl` records resource and object-production snapshots.

For a new portable run, require successful `build-result.json`, `contract-verification.json`, and `all-module-axioms.json`. The reviewed original run is summarized separately in `result.json` and `REPORT.md`. An inventory or dependency setup alone is not completion. No deletion or upload is authorized by this recipe.
