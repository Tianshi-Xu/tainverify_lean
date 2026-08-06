# YOCO-MoE A0.4B authority regeneration

This directory separates two workflows that must not be confused.

## Reviewed revisions

- llm-train: `9a1be1d5fd1c063d80be82797692cdc7d23cfbef`
- nnScaler: `d3d468ed23edb2f28aa8566b2dfb6ed49c5955cf`
  (`li/ep-cp`, the companion branch for llm-train's explicit CP/EP API)

The nnScaler `main` revision at review time did not accept llm-train's
`cp_size` and `require_full_plan_sequence_partition` arguments. Do not replace
the pinned companion revision with `main` without rerunning the compile tests.

## CPU smoke

`compile_cpu_smoke.py` uses the deterministic built-in `tp` policy and reduced
model defaults. It checks imports, tracing, code generation, pickle extraction,
and the expected shuffle/unshuffle wiring. Its metadata contains
`"authority": false`; these artifacts must never replace production authority.
The output directory must not already exist; the smoke is built in a private
staging directory and published without replacing any existing path.

```bash
python scripts/yoco_regen/patch_mgener_dump.py \
  /path/to/pinned-nnscaler/nnscaler/parallel.py
# Reinstall that patched source into the venv, then:
python scripts/yoco_regen/compile_cpu_smoke.py \
  --llm-train /path/to/llm-train \
  --out-dir /tmp/yoco-smoke --plans 1 2
python scripts/yoco_regen/inspect_mgener.py /tmp/yoco-smoke/pm_mgener.pkl \
  --llm-train /path/to/llm-train \
  --nnscaler /path/to/pinned-nnscaler \
  --trust-local-pickle
```

For the four-layer smoke, expected logical counts are one shuffle, five
unshuffles, and two stacks in SM. PM expands each to two rank-local nodes. The
four auxiliary unshuffles must feed the two stacks; the fifth restores hidden
state layout.

## Production authority

`generate_authority.sh` is fail-closed and requires a two-GPU node. It uses
llm-train's real `run_mode=compile` / `pas_autodist` path, full 24-layer model,
sequence length 4096, and `pcs/all2all_moe.yaml`.
Both source repositories are materialized as private, no-hardlink clones at the
reviewed commits before any code executes. Neither caller checkout is modified.
The private llm clone receives one canonical, hash-bound hardware compatibility
patch: compute capability 12.x uses the generic A100/H100 Triton autotune
candidate set instead of the B200-only candidate set. This changes launch
configuration selection only, not operator values, graph annotations, model
code, or the reviewed base revision. The patched `llm/kernel/gemm.py` digest is
bound into both rank-0 dump receipts and final provenance metadata.

```bash
export YOCO_LLM_TRAIN_REPO=/clean/pinned/llm-train
export YOCO_NNSCALER_REPO=/clean/pinned/nnscaler
export YOCO_AUTHORITY_OUT=/output/yoco-a04b-9a1be1d
bash scripts/yoco_regen/generate_authority.sh
```

The output contains:

- `sm_mgener.pkl`, `pm_mgener.pkl`
- rank-0 dump receipts binding policy, topology, pickle hash, and patched-source hash
- Verdict-compatible `sm_mgener.json`, `pm_mgener.json`
- `sm_provenance.json`, `pm_provenance.json`
- `gen_args.json` with exact revisions, topology, package versions, GPU model,
  memory, compute capability, NVIDIA driver, CUDA runtime, NCCL version, canonical
  hardware-patch identity/hash, and artifact hashes
- `.trainverify-stage-owner`, an inert random ownership marker retained for
  fail-closed cleanup auditing

After generation, run `inspect_mgener.py` on both sides before emitting Lean.
Do not infer PM changes by inspecting PM alone.

## Lean emission

```bash
python scripts/yoco_regen/emit_yoco_a04b.py \
  --authority-dir /output/yoco-a04b-9a1be1d \
  --llm-train /clean/pinned/llm-train \
  --nnscaler /clean/pinned/nnscaler \
  --expected-hardware-sha256 <digest-captured-over-trusted-ssh> \
  --snapshot-dir /output/yoco-a04b-9a1be1d-lean-refresh \
  --trust-new-authority
```

The explicit trust flag acknowledges that Python pickle is executable input and
that the artifacts were produced locally by the pinned production generator.
The expected hardware digest is a required out-of-band trust anchor. Capture
`gen_args.json.hardware_sha256` directly from the GPU host over the already
authenticated SSH session before transferring the authority directory, and
store it separately from that directory. A digest read only from the transferred
artifact is not an independent trust anchor and must not be used here.
Before unpickling, the emitter verifies ownership, non-writable permissions,
fixed revisions, world/provenance schemas, production policy, topology, and
pickle hashes. It writes every generated file into a sibling staging directory
and atomically publishes one complete snapshot only after graph emission and
manifest validation succeed.

The emitter serializes rank loading to avoid the multiprocessing/import
deadlock seen with dynamically registered private-model operators. It computes
artifact and metadata hashes at execution time and passes the pinned revisions
to `graph_to_lean.py`; no digest is copied from an older authority.

Numeric TIDs, node indices, certificates, and old false-goal classifications
must be regenerated from the new graph rather than patched by number.

Only production `pas_autodist` artifacts may be written to the repository.
Inspect both SM and PM before replacing generated Lean files.
