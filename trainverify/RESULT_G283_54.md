# Result: goal_283 + goal_54 bridges

Both bridges are proven (0 `sorry`), compile cleanly, and are wired into
`MainTheorem.lean`. Verified by `lake build denote.gpt_ly4_regen.MainTheorem`
→ *Build completed successfully*. Neither `goal_54_full` nor `goal_283_full`
appears in the residual `sorry` warning list (those warnings are for other,
not-yet-proven goals such as goal_55+).

## goal_283
- **Commit:** `6bfc9591c783bc4bdf379809cdc35219840173f1`
- **File:** `trainverify/denote/gpt_ly4_regen/Goal283Bridge.lean`
- **0 sorry:** yes
- **Axioms** (`goal_283_intermediate`): only allowed — `propext`,
  `Classical.choice`, `Quot.sound`, `Lean.ofReduceBool`, `Lean.trustCompiler`,
  and the `applyNode_*` / helper series (`applyNode_allGatherPrimDimN_out`,
  `applyNode_fw_linear_out`, `erfFn`, `expFn`, `piScalar`, `scalarToNat`,
  `sqrtFn`). No `sorryAx`.
- **Structure:** FW_multiref params=[2] **second-output** + 4×AllToAllPrim
  (idim=2, odim=1, params=[2,1]).
  - SM node 53 `FW_multiref(628)→[977,981]`, takes second out `981 = 628`.
  - PM nodes 346–349 `FW_multiref(2057+r)→[3557+8r,3559+8r]` second outs
    `3559/3567/3575/3583`; PM nodes 351/353/355/357 (non-adjacent!)
    `AllToAll(3559,3567,3575,3583, params[2,1])→2193-2196`.
  - input 628 from goal_49 (dim2-shard tps 2057–2060 `[1,8,8]`).
  - tps 2193–2196 = chunk dim1 of 628, gatherDim=1.
- **Template:** `Goal281Bridge.lean` (first-output sibling on the same
  multiref node), swapped to second output via the
  `applyNode_fw_multiref2_second_out_g283` helper and the
  AllToAll upstream second slot (nodes 351/353/355/357).
- **Prereqs:** 60 — goal_2..49 + 257,259,…,279 (odd).

## goal_54
- **Commit:** `e6b5258a274cf56330f8cdd19e5e74f8329530bc`
- **File:** `trainverify/denote/gpt_ly4_regen/Goal54Bridge.lean`
- **0 sorry:** yes
- **Axioms** (`goal_54_intermediate`): only allowed (same set as above).
  No `sorryAx`.
- **Structure:** binary FW_add over a single AllToAll reshard, gatherDim=1.
  - SM node 58 `FW_add(981,636)→637` `[1,8,32]`.
  - PM nodes 380–383 `AllToAllPrim(ins=[2169,2170,2171,2172], idim=2, odim=1,
    params=[2,1])→2197-2200` (reshards 636 dim2-shard → dim1-shard), then
    PM nodes 384–387 `FW_add(2193+r, 2197+r)→2201-2204` `[1,2,32]`.
  - direct input 981 from goal_283 (dim1-shard tps 2193–2196 `[1,2,32]`).
  - resharded input 636 from goal_53 (dim2-shard tps 2169–2172 `[1,8,8]`).
  - output multi-tps 2201–2204, gatherDim=1.
- **Template:** `Goal49Bridge.lean` / `Goal29Bridge.lean` (binary FW_add over
  single AllToAll reshard); the AllToAll direction is `dim1→dim2 (params[1,2])`
  in goal_49 vs `dim2→dim1 (params[2,1])` here.
- **Prereqs:** 66 — goal_2..53 + 257,259,…,281 (odd) + 283.
- **Dependency:** needs `goal_283` proven first (provides 981 / tps 2193–2196).

## Discipline / integrity checks
- `git diff bc19002 -- trainverify/denote/gpt_ly4_regen/Denote.lean` → empty
  (core semantics file untouched).
- Only `Goal283Bridge.lean`, `Goal54Bridge.lean` were added and
  `MainTheorem.lean` had its two `sorry` stubs replaced + two imports added.
- Not pushed (left for manual push).

## Notes / pitfalls observed
- This task was completed in the repository while a parallel worker instance
  committed the same two bridges (commits above). The committed bridges are the
  canonical versions and were independently re-verified here (rebuilt to
  *Build completed successfully*, 0 sorry, axiom-checked — no `sorryAx`).
- goal_283's AllToAll PM nodes are **non-adjacent** (351/353/355/357), with the
  goal_281 sibling occupying 350/352/354/356 interleaved on the shared
  `FW_multiref(628)→[977,981]` node.
- For the `#print axioms` check the lemmas are under namespace
  `TrainVerify.Denote.GeneratedGoals` (must qualify the name).
