"""Regression tests for shuffle-free cut-only boundary contracts.

The faithful full graph must not publish ordinary-gather goals for these tids,
but Pattern_1/Pattern_4 still need the same relations as explicit boundaries of
their sliced (shuffle-free) cut graphs.
"""

from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[2]
TV = ROOT / "trainverify"

P1 = {
    5893: (11609, 11610),
    5895: (11613, 11614),
    5898: (11621, 11622),
}
P4 = {
    5359: (9729, 9730),
    5408: (9901, 9902),
    5457: (10073, 10074),
    5506: (10245, 10246),
    5555: (10417, 10418),
    5604: (10589, 10590),
    5653: (10761, 10762),
    5702: (10933, 10934),
    5751: (11105, 11106),
    5800: (11277, 11278),
    5849: (11449, 11450),
    5898: (11621, 11622),
}


def _check(goal_id: int, records: dict[int, tuple[int, int]]) -> None:
    text = (TV / f"denote/yoco_goals/Goal_{goal_id}.lean").read_text()
    for ts, (r0, r1) in records.items():
        name = f"goal{goal_id}CutIntermediateGoal_{ts}"
        assert f"def {name} : LineageGoal" in text
        body = re.search(rf"def {name} : LineageGoal :=\n  (.*)", text)
        assert body, name
        assert f"ts := {ts}" in body.group(1)
        assert f"rank := 0, tid := {r0}" in body.group(1)
        assert f"rank := 1, tid := {r1}" in body.group(1)
        # The local record must be part of the cut's caller contract.
        assert text.count(name) >= 2


def test_cut_local_boundaries_present_and_global_ordinary_goals_absent():
    _check(1, P1)
    _check(4, P4)

    generated = (TV / "denote/GeneratedYOCOMoE.lean").read_text()
    for ts in set(P1) | set(P4):
        assert f"def intermediateGoal_{ts} : LineageGoal" not in generated
        assert f"def intermediateGoal_{ts}_zigzag" in generated


def test_patterns_do_not_take_an_unconstrained_zigzag_hypothesis():
    p1 = (TV / "denote/yoco_goals/Pattern_1.lean").read_text()
    p4 = (TV / "denote/yoco_goals/Pattern_4.lean").read_text()
    main = (TV / "denote/yoco_goals/YocoMoE_MainSummary.lean").read_text()
    for text in (p1, p4, main):
        assert "ZigzagCutGatherHyp" not in text
        assert "Pattern1ZigzagCutGatherHyp" not in text
