# Archived replication-criterion spike

This branch preserves an unmerged experiment found in the retired OpenClaw checkout.
It correctly identifies that equal SM/PM tensor shapes are insufficient to infer
`replicated := true`: rank-local tensors may have the same shape but different
values.

The implementation in this branch is **not production-ready**. Its immediate
producer whitelist includes `FW_multiref`, but multiref is an identity fan-out
and does not establish cross-rank value equality when its input was already
rank-dependent. A sound replacement must infer replication from full
value/ownership provenance (or an explicit authority contract), not shape or
immediate operator name alone.

The main branch records this requirement in
`docs/PROOF_COMPILER_REQUIREMENTS.md`. This archive exists only to preserve the
investigation and must not be merged as-is.
