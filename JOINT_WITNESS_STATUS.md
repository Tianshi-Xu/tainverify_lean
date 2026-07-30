# Pattern Joint Hypothesis Witness — 状态与决策请求

> **SUPERSEDED (2026-07-28).** Historical status from commit `59a43d2b`.
> Replicated reconstruction and joint witnesses subsequently landed; do not use
> the blocker or decision request below as current state. The current top-level
> cut-tier theorem is `YocoMoE_MainSummary.yoco_moe_cut_tier_main`; current
> faithful coverage is in `trainverify/YOCO_MOE_FAITHFUL_COVERAGE.md`.

**Session:** 2026-07-14  
**Branch:** main (52b42b37 pushed)

## 已完成 ✅

### `denote/yoco_goals/JointWitnessCore.lean`（zero-sorry）
通用 vacuity-witness machinery，可复用给 P1/P2/P3/P4：

- `canonicalStore` / `zeroStore` + `shapeOf : Tid → Shape`
- `allGatherPrimDimN_of_zeroTensors`
- `allReducePrim_of_zeroTensors`
- `reconstructWithDim_of_zeroTensors`
- `goalShapeOK2` predicate + `goalShapeOK2_check` (computable Bool)
- `goalShapeOK2_of_check`（互推）
- `zeroStore2_initGoalHolds` / `zeroStore2_initGoalsHold`
- `zeroStore_shapes_hold_of_list`（配 `shapeEnvOfList`）

### `denote/yoco_goals/Pattern_1_JointWitness.lean`（skeleton）
- `shapeOfSM_P1_list` (1484 entries) + `shapeOfPM_P1_list` (2564 entries)
- `pattern_1_joint_hypothesis_witness` 主 theorem
- 4 个 `native_decide` clauses：
  - ✅ StoreShapesHold (initSM) 
  - ✅ StoreShapesHold (initPM)
  - ❌ **InitGoalsHold on `goal_1_cut_initGoals`** — fail
  - ✅ labels bound (`valAt zero < 154880`)

## 卡点：Denote reconstructWithDim 缺 replication case

**具体表现：** 38 个 `intermediateGoal_{7383,7387,7392,...,8033}` 声明形如：
```
{ ts := 7383, tsShape := [4096, 1024],
  tps := [{rank:=0, tid:=14603}, {rank:=1, tid:=14611}],
  tpShapes := [[4096, 1024], [4096, 1024]] }
```

**Denote 语义：** `reconstructWithDim gd 2 0 [full,full]` 走 allGather 分支 → 输出 `[8192, 1024]` ≠ 声明的 `[4096, 1024]`，goal 内在不可满足。

**Python 真实语义：** `FW_multiref` op 在 SM/PM 两侧都是 replication（PM 每 rank 各持完整 `[4096, 1024]` 副本），reconstruction 应为 "pick one" 而非 gather-concat。

**证据：** GeneratedYOCOMoE.lean 里
- Node 3 (SM): `FW_multiref ins=[4681] outs=[7383, 7387]`
- Node 978 (PM r0): `FW_multiref ins=[4681] outs=[14603, 14607]`
- Node 979 (PM r1): `FW_multiref ins=[4681] outs=[14611, 14615]`
两 rank 都持 4681 完整副本，再各自 multiref 出 alias。

**emitter (Verdict/graph_to_lean.py) 不是 bug：** `_infer_gather_dim` 检测不到 sharding pattern 就 default 返回 0，被动反映 Python 现状。

## 决策选项

### 选项 A'：修 emitter（推荐但风险 unclear）
在 `Verdict/graph_to_lean.py::_emit_goal_def` 里加一步：如果 `all(tp_shape == ts_shape for tp_shape in tp_shapes) and len(tps) > 1`，就只 emit `tps=[(0, tid_rank0)]`（single-shard），跳 singleton reconstruction。

**Pro:** 不改 Denote，改动局部。  
**Con:** 需要重跑 emitter 重生 `GeneratedYOCOMoE.lean`（19541 行），所有下游 pattern 证明可能 break（因为 tps 结构改了）。子鱼已证的 P1-P5 里所有引用 `intermediateGoal_XXXX.tps` 结构的 lemma 都要 audit。

### 选项 A：改 Denote reconstructWithDim（更 invasive）
加 case：`else if all_shards_identical_shape ∧ shard_shape ≠ [1] then head_shard else allGather`。

**Con:** 需要 detector 里读 shape 判断"是否 replicated"。而且改了 def 后，`reconstructWithDim_cons_cons_nonscalar` 等 lemma 的 rw pattern 都会失效，所有 pattern 证明都要修。

### 选项 C：接受 Pattern_1 vacuous，不证 joint witness
现状 `prove_pattern_1` 仍编译，只是 `pattern_1_target` 在 canonical store 下 hypothesis 无法满足（vacuously true）。documented，move on。

**Con:** 违反 vacuity 三陷阱审查（陷阱 2：stmt vacuous），会 undermine pattern_1 的实际信任价值。

---

**下一步：等子鱼 pick A' / A / C**

Files pushed to main:
- `denote/yoco_goals/JointWitnessCore.lean` (490 lines, zero-sorry)
- `denote/yoco_goals/Pattern_1_JointWitness.lean` (4128 lines skeleton, 1 sorry in the goalsShapeOK2 native_decide fail — 我可以先补一个 `sorry` 让它编过，或先保留 native_decide fail 状态)
