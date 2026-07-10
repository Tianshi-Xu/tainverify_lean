# BASELINE metrics (pre-refactor)

- Branch: `iroha-hs-refactor` (base main @ a09fe66)
- File: `trainverify/denote/yoco_goals/Pattern_3.lean`
- Total lines: **54,496**
- `hs_<tid>` helper theorems in `RouterShapesHelpers`: **1116** (lines ~866–20779)
- Helper block physical lines: ~18,733 (16,503 body + 2,232 `set_option` prefixes)

## Build time (hot from full chain rebuild)
- `denote.yoco_goals.Pattern_3` module: **1447s** (~24.1 min)
- Full chain wall (from cold `.lake` hash-mismatch rebuild): 31:05

## Sample `#print axioms` (original helpers)
All sampled = `[propext, Classical.choice, Quot.sound]`:
- hs_4680 (leaf), hs_4681 (float/id), hs_4703 (add/2in), hs_7483 (topk/1in), hs_7491 (moe/7in) ✓
