#!/usr/bin/env python3
"""Mechanically count ownership-aware YOCO-MoE faithful coverage.

Run from the trainverify root or pass it as argv[1]. Only exact theorem names on
the faithful track count; ringAttn and cut-graph proofs are deliberately
excluded.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path


root = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else Path(__file__).resolve().parents[1]
generated = (root / "denote/GeneratedYOCOMoE.lean").read_text()
proofs = "\n".join(
    p.read_text(errors="ignore") for p in (root / "denote/yoco_goals").glob("*.lean")
)

ordinary = set(re.findall(r"^def (intermediateGoal_\d+) : LineageGoal", generated, re.M))
zigzag = set(re.findall(r"^def (intermediateGoal_\d+)_zigzag : ", generated, re.M))
top_ordinary = set(re.findall(r"^def (goal_\d+) : LineageGoal", generated, re.M))
top_false = set(re.findall(r"^-- NOT an ordinary gather: (goal_\d+) ", generated, re.M))

ordinary_proved = {
    f"intermediateGoal_{tid}"
    for tid in re.findall(r"^theorem recon_intermediateGoal_(\d+)_faithful\b", proofs, re.M)
}
zigzag_proved = {
    f"intermediateGoal_{tid}"
    for tid in re.findall(r"^theorem recon_zigzagGoal_(\d+)_faithful\b", proofs, re.M)
}

# All sound top-level goals use their generated tid in the theorem name except
# goal_5, whose theorem is named by goal number. Pin the three exact names rather
# than counting arbitrary `recon_goal_*` helpers (there are expression/tid
# restatements for 5928/5930).
top_proof_names = {
    "goal_1": "recon_goal_4673_faithful",
    "goal_2": "recon_goal_4674_faithful",
    "goal_5": "recon_goal_5_faithful",
}
top_proved = {g for g, thm in top_proof_names.items() if re.search(rf"^theorem {thm}\b", proofs, re.M)}

ordinary_total = len(ordinary) + len(top_ordinary)
ordinary_done = len(ordinary & ordinary_proved) + len(top_ordinary & top_proved)
zigzag_total = len(zigzag)
zigzag_done = len(zigzag & zigzag_proved)
false_total = len(top_false)
total = ordinary_total + zigzag_total + false_total
done = ordinary_done + zigzag_done

print(f"ordinary: {ordinary_done}/{ordinary_total}")
print("  missing:", sorted((ordinary - ordinary_proved) | (top_ordinary - top_proved)))
print(f"zigzag:   {zigzag_done}/{zigzag_total}")
print("  missing:", sorted(zigzag - zigzag_proved))
print(f"false findings: {false_total}: {sorted(top_false)}")
print(f"overall per-goal faithful: {done}/{total} = {100 * done / total:.2f}%")

assert total == 1156, f"unexpected corpus size: {total}"
assert done == 1154, f"coverage changed: {done}"
