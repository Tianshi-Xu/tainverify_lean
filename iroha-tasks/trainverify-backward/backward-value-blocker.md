# Backward cross-graph value closure: verified dependency blocker

Local continuation now proves the original 1293→three-alias values and the K/V sequence-to-hidden exchanges from the same run/initial contracts. See `forward-primal-continuation-status.md` for exact local kernel evidence and the separate unresolved canonical bundle-size gate. These new facts do not yet establish saved-X1317 or the attention cotangent relation below.

## What is and is not blocked

Original same-final-Store backward source reads and their score/V-path DAG compositions are executable proof artifacts. Cross-SM/PM gradient closure is **not** implied by those artifacts. The blocker found here is an unclosed forward value-proof dependency, not a demonstrated nnScaler numerical counterexample or a missing batched-matmul formula.

The existing output-linear root has actual cross-graph dX unit/consumer theorems from constant cotangents, initial parameter relations, and source shapes. It is not the attention cotangent: root dX is lowered SM1374, while first attention BW_matmul consumes SM1363. The intervening nonlinear/residual/projection/layout chain still needs value-relation propagation.

## Earliest cross-graph successor

SM BW_layernorm65 uses saved input SM1317. PM111/347/583/819 use saved inputs PM272/575/878/1181. `trainverify/denote/SourceBWLayernormDxUnit.lean:193–213` already exports `source_bw_layernorm_dx_unit_local`, but its statement independently requires:

- `hgpre`: cotangent reconstruction;
- `hxpre`: saved-input reconstruction.

Root dX consumers can supply the first. The second must come from forward value proofs, not shapes, parameter frames, output-linear saved X1318, or an assumed conclusion. Required saved-input relations are:

- `chunkPrimDimN 0 2 0 (t 1317) = allGatherPrimDimN 1 2 0 [q 272,q 575]`;
- `chunkPrimDimN 0 2 1 (t 1317) = allGatherPrimDimN 1 2 0 [q 878,q 1181]`.

All IDs above are compiler-lowered IDs, not raw nnScaler TIDs.

## Accepted forward evidence inspected

Original sources under `/home/v-zhouziyu/trainverify-audits/general-parallel-internal1/dp-prefix-cost-closure/` were read directly:

- `frontier-next-layernorm/STATUS.md`: accepted forward checkpoint `e099d160266c05b57524895b641bcd6cbed78651`.
- `frontier-next-layernorm/actual1/RuntimeWorld.lean:5416,5472`: `frontierLayernormUnitFacts_1293_0/1`, under original successful runs plus `InitialParameterValues`. They establish values for **1293**, not 1317, 1306 or 1302.
- `frontier-sequence-alias/STATUS.md`: its successor candidate is explicitly frozen/not accepted. No candidate is imported as proved authority here; its active worktree/source/output ownership is untouched.

A wider read-only inventory also inspected the earlier attention facts for SM1281/1277. Those are proof patterns, not facts for the current attention's saved probability SM1306 or V SM1302. Matching dimensions are insufficient, and the old/current probability distributions use different intermediate head/query layouts.

## First-attention payoff once prerequisites close

For DP unit0 the missing boundary conclusions are:

- attention G: `chunk0(2,0,t1363) = gather2(2,[q237,q541])`;
- saved P: `chunk0(2,0,t1306) = gather2(2,[q233,q536])`;
- V replicas for dP: `q79 = chunk0(2,0,t1302)` and `q382 = chunk0(2,0,t1302)`.

Unit1 uses G `[843,1147]`, P `[839,1142]`, V `[685,988]`. Softmax backward separately retains logits SM1305 / PM232,535,838,1141; probabilities are not saved logits.

`KRankBWMatmulQuery.lean` already supplies `TrainVerify.Denote.bw_matmul_snd_query_reduction_rank4`: G/P value reconstruction plus genuine source shapes yields the dV sum. V reconstruction is mathematically unnecessary for that second projection, but is required for dP/score. Existing original RS source/composition theorems then give the exact local chunks. Neither saved primal is replaced by a dummy in original source reads.

Next semantic action is therefore to derive the missing forward saved-X1317 facts, then compose actual root dX + original final-LN backward reads + the existing local derivative theorem. After propagating that relation through the intervening chain, apply the firstmatmul algebra to actual fullref-bound operands. No new public `hxpre`/attention-G equality premise is added to fake closure.

Full inventory and exact supporting endpoint paths are preserved privately in `.hermes/backward-kernel/backward-value-frontier.md`. This document records a dependency boundary, not whole-model/public/Torch completion.
