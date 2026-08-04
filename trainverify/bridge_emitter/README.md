# Bridge emitter

This directory contains the existing graph-to-bridge proof generator used by the GPT and YOCO case studies. It is reusable infrastructure, but it is **not** the complete one-command proof compiler specified in [`../../docs/PROOF_COMPILER_REQUIREMENTS.md`](../../docs/PROOF_COMPILER_REQUIREMENTS.md).

## Components

- `parser.py`: parse generated goal declarations into a small graph IR.
- `probe.py`: ask Lean for concrete writer-node positions.
- `emit.py` / `renderer.py`: legacy family-A generator.
- `emit2.py` / `renderer_uni.py`: broader topology-dispatch generator.
- `emit_yoco.sh`: YOCO wrapper.
- `regress.py`: regenerate existing GPT bridges and restore originals after checking.
- `wire.py`: wire verified GPT bridges into the corresponding aggregate theorem.
- `SPEC.md` and `BW_MULTI_SPEC.md`: design records for the implemented bridge families.

All tools resolve the repository from their own location; no user-specific workspace path is required.

## Honest scope

`emit2.py` dispatches among implemented topology families. “Universal” in its historical module name means broader than the original family-A renderer, not arbitrary supported networks. It does not yet provide graph-wide relation inference, generic certificate composition, structured missing-rule diagnostics, or unseen-architecture clean-room acceptance.

Do not extend it by adding model-specific numeric rewrites. New work should move topology knowledge into typed relation rules and explicit certificates.

## Smoke checks

From the repository root:

```bash
python3 -m py_compile trainverify/bridge_emitter/*.py
python3 trainverify/bridge_emitter/parser.py 5
python3 trainverify/bridge_emitter/emit2.py --help
bash -n trainverify/bridge_emitter/emit_yoco.sh
```

Generated regression state (`regress_results.json`) and Python caches are ignored.
