#!/usr/bin/env python3
"""Tests for the structured YOCO MoE migration metadata generator."""

from __future__ import annotations

import copy
import sys
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))

import generate_yoco_moe_migration_metadata as generator  # noqa: E402


class MigrationMetadataTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.metadata = generator.generate_metadata(
            generator.DEFAULT_GRAPH.read_bytes(), generator.DEFAULT_MANIFEST.read_bytes()
        )
        cls.entries = cls.metadata["entries"]

    def test_checked_in_artifact_is_canonical_generated_bytes(self) -> None:
        self.assertEqual(
            generator.DEFAULT_ARTIFACT.read_bytes(),
            generator.canonical_bytes(self.metadata),
        )

    def test_exact_audit_table_and_full_node_declarations(self) -> None:
        self.assertEqual(
            self.metadata["audit_table"],
            [generator._audit_dict(row) for row in generator.AUDIT_TABLE],
        )
        self.assertEqual(len(self.entries), 22)
        for entry in self.entries:
            self.assertEqual(entry["node_decls"]["sm"]["outs"], [entry["goal_tids"]["sm"]])
            self.assertEqual(
                [node["outs"][0] for node in entry["node_decls"]["pm"]],
                entry["goal_tids"]["pm"],
            )
            for node in [entry["node_decls"]["sm"], *entry["node_decls"]["pm"]]:
                self.assertEqual(node["op"], "OpName.FW_all2all_moe_gmm")
                self.assertEqual(len(node["ins"]), 5)
                self.assertEqual(len(node["outs"]), 1)
                self.assertEqual(len(node["params"]), 4)

    def test_affine_invariants_include_explicit_l24_exception(self) -> None:
        generator.validate_affine_invariants(self.entries)
        l23 = next(entry for entry in self.entries if entry["layer"] == 23)
        l24 = next(entry for entry in self.entries if entry["layer"] == 24)
        self.assertEqual(l24["node_indices"]["pm"][1] - l23["node_indices"]["pm"][1], 72)
        broken = copy.deepcopy(self.entries)
        next(entry for entry in broken if entry["layer"] == 24)["node_indices"]["pm"][1] = 1889
        with self.assertRaisesRegex(ValueError, "L24 PM rank-1"):
            generator.validate_affine_invariants(broken)

    def test_sliding_affine_group(self) -> None:
        sliding = [entry for entry in self.entries if entry["kind"] == "sliding"]
        self.assertEqual([entry["layer"] for entry in sliding], list(range(3, 13)))
        for previous, current in zip(sliding, sliding[1:]):
            self.assertEqual(current["goal_tids"]["sm"] - previous["goal_tids"]["sm"], 54)
            self.assertEqual(current["node_indices"]["sm"] - previous["node_indices"]["sm"], 39)
            self.assertEqual(
                [b - a for a, b in zip(previous["node_indices"]["pm"], current["node_indices"]["pm"])],
                [78, 78],
            )

    def test_zigzag_is_blocked_fail_closed(self) -> None:
        zigzag = [entry for entry in self.entries if entry["kind"] == "zigzag"]
        self.assertEqual([entry["layer"] for entry in zigzag], list(range(13, 25)))
        self.assertTrue(all(entry["migration"]["state"] == "blocked" for entry in zigzag))
        self.assertTrue(all(entry["migration"]["fail_closed"] is True for entry in zigzag))
        broken = copy.deepcopy(self.entries)
        next(entry for entry in broken if entry["kind"] == "zigzag")["migration"]["state"] = "ready"
        with self.assertRaisesRegex(ValueError, "blocked fail-closed"):
            generator.validate_affine_invariants(broken)


if __name__ == "__main__":
    unittest.main()
