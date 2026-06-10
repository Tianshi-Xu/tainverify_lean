#!/usr/bin/env python3
"""Unit tests for the generated Lean static auditor."""

from __future__ import annotations

from pathlib import Path
import tempfile
import unittest

import audit_generated_lean as audit


class AuditGeneratedLeanTests(unittest.TestCase):
	def _write(self, root: Path, name: str, text: str) -> Path:
		path = root / name
		path.write_text(text, encoding="utf-8")
		return path

	def test_missing_evalop_branch_is_reported(self) -> None:
		with tempfile.TemporaryDirectory() as d:
			root = Path(d)
			denote = self._write(
				root,
				"Denote.lean",
				'''
def evalOp : Unit := by
  | "OpName.FW_add", [x, y] => [x]
''',
			)
			generated = self._write(
				root,
				"GeneratedData.lean",
				'''
def sm : GraphDecl := by
  refine { numRanks := 1, nodes := ?_ }
  exact [
    { rank := 0, op := "OpName.New_missing_op", ins := [1], outs := [2] },
  ]
def smInitShapes : List (Tid × Shape) := [
  (1, [1]),
  (2, [1]),
]
''',
			)

			findings = audit.audit(
				generated,
				denote,
				check_shapes=True,
				strict_comm_params=True,
			)

		self.assertTrue(any("has no evalOp branch" in f.message for f in findings))

	def test_fw_multiref_param_must_match_output_count(self) -> None:
		with tempfile.TemporaryDirectory() as d:
			root = Path(d)
			denote = self._write(
				root,
				"Denote.lean",
				'''
def evalOp : Unit := by
  | "OpName.FW_multiref", [x] => [x]
''',
			)
			generated = self._write(
				root,
				"GeneratedData.lean",
				'''
def sm : GraphDecl := by
  refine { numRanks := 1, nodes := ?_ }
  exact [
    { rank := 0, op := "OpName.FW_multiref", ins := [1], outs := [2, 3], params := [3] },
  ]
def smInitShapes : List (Tid × Shape) := [
  (1, [1]),
  (2, [1]),
  (3, [1]),
]
''',
			)

			findings = audit.audit(
				generated,
				denote,
				check_shapes=True,
				strict_comm_params=True,
			)

		self.assertTrue(any("FW_multiref params[0]=3" in f.message for f in findings))


if __name__ == "__main__":
	unittest.main()
