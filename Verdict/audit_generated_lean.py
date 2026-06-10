#!/usr/bin/env python3
"""Static audit for generated TrainVerify Lean graph files.

This is a fast pre-proof gate. It catches structural generator/operator bugs
that otherwise show up much later as false Lean goals or silent default tensors:

- generated ops missing an `evalOp` branch in `Denote.lean`
- obvious input arity mismatches against fixed `evalOp` patterns
- missing or wrong parameters for `FW_multiref`
- embedding offset mistakes for row/vocab-sharded embedding patterns
- missing shape entries in large `GeneratedData.lean` files

It deliberately does not try to prove semantic correctness. It is a guardrail
for the recurring classes of generator and operator wiring bugs.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import re
from typing import Iterable


ROOT = Path(__file__).resolve().parent.parent
DEFAULT_DENOTE = ROOT / "trainverify" / "denote" / "Denote.lean"


NODE_RE = re.compile(
	r"\{\s*rank\s*:=\s*(?P<rank>\d+),\s*"
	r'op\s*:=\s*"(?P<op>[^"]+)",\s*'
	r"ins\s*:=\s*(?P<ins>.*?),\s*"
	r"outs\s*:=\s*(?P<outs>.*?)(?:,\s*params\s*:=\s*(?P<params>.*?))?\s*\},"
)
SHAPE_RE = re.compile(r"\(\s*(?P<tid>\d+)\s*,\s*\[(?P<shape>[^\]]*)\]\s*\)")
EVAL_BRANCH_RE = re.compile(r'^\s*\|\s*"(?P<op>[^"]+)",\s*(?P<args>.*?)\s*=>')
LIST_RE = re.compile(r"^\[\s*(?P<body>.*?)\s*\]$")
RANGE_MAP_RE = re.compile(
	r"List\.range\s+(?P<n>\d+)\)\.map\s+\(fun\s+\w+\s+=>\s+(?P<base>\d+)\s*\+\s*\w+\)"
)


@dataclass(frozen=True)
class Node:
	path: Path
	line: int
	rank: int
	op: str
	ins: tuple[int, ...]
	outs: tuple[int, ...]
	params: tuple[int, ...]


@dataclass(frozen=True)
class Finding:
	severity: str
	path: Path
	line: int
	message: str


def _parse_nat_list(expr: str) -> tuple[int, ...]:
	expr = expr.strip()
	m = LIST_RE.match(expr)
	if m:
		body = m.group("body").strip()
		if not body:
			return ()
		return tuple(int(x.strip()) for x in body.split(",") if x.strip())

	m = RANGE_MAP_RE.search(expr)
	if m:
		n = int(m.group("n"))
		base = int(m.group("base"))
		return tuple(base + i for i in range(n))

	raise ValueError(f"unsupported Nat list expression: {expr}")


def parse_nodes(path: Path) -> list[Node]:
	nodes: list[Node] = []
	for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
		m = NODE_RE.search(line)
		if not m:
			continue
		try:
			ins = _parse_nat_list(m.group("ins"))
			outs = _parse_nat_list(m.group("outs"))
			params_expr = m.group("params")
			params = _parse_nat_list(params_expr) if params_expr else ()
		except ValueError as exc:
			raise SystemExit(f"{path}:{lineno}: {exc}") from exc
		nodes.append(
			Node(
				path=path,
				line=lineno,
				rank=int(m.group("rank")),
				op=m.group("op"),
				ins=ins,
				outs=outs,
				params=params,
			)
		)
	return nodes


def parse_shapes(path: Path) -> dict[int, tuple[int, ...]]:
	shapes: dict[int, tuple[int, ...]] = {}
	for line in path.read_text(encoding="utf-8").splitlines():
		m = SHAPE_RE.search(line)
		if not m:
			continue
		body = m.group("shape").strip()
		shape = tuple(int(x.strip()) for x in body.split(",") if x.strip())
		shapes[int(m.group("tid"))] = shape
	return shapes


def parse_eval_ops(denote_path: Path) -> dict[str, set[int] | None]:
	"""Return op -> fixed input arities, or None for varargs branches."""
	ops: dict[str, set[int] | None] = {}
	for line in denote_path.read_text(encoding="utf-8").splitlines():
		m = EVAL_BRANCH_RE.match(line)
		if not m:
			continue
		op = m.group("op")
		args = m.group("args").strip()
		arity: int | None
		if args == "xs" or args.startswith("_"):
			arity = None
		elif args.startswith("[") and args.endswith("]"):
			body = args[1:-1].strip()
			arity = 0 if not body else len([x for x in body.split(",") if x.strip()])
		else:
			arity = None

		if arity is None:
			ops[op] = None
		else:
			ops.setdefault(op, set())
			if ops[op] is not None:
				ops[op].add(arity)
	return ops


def _producer_by_out(nodes: Iterable[Node]) -> dict[int, Node]:
	prod: dict[int, Node] = {}
	for node in nodes:
		for tid in node.outs:
			prod[tid] = node
	return prod


def _consumers_by_in(nodes: Iterable[Node]) -> dict[int, list[Node]]:
	cons: dict[int, list[Node]] = {}
	for node in nodes:
		for tid in node.ins:
			cons.setdefault(tid, []).append(node)
	return cons


def _expected_offset(node: Node, shapes: dict[int, tuple[int, ...]]) -> int | None:
	if not node.ins:
		return None
	weight_tid = node.ins[-1]
	shape = shapes.get(weight_tid)
	if not shape:
		return None
	return node.rank * shape[0]


def audit(
	generated_path: Path,
	denote_path: Path,
	*,
	check_shapes: bool,
	strict_comm_params: bool,
) -> list[Finding]:
	nodes = parse_nodes(generated_path)
	shapes = parse_shapes(generated_path)
	eval_ops = parse_eval_ops(denote_path)
	findings: list[Finding] = []

	def err(node: Node, msg: str) -> None:
		findings.append(Finding("ERROR", node.path, node.line, msg))

	def warn(node: Node, msg: str) -> None:
		findings.append(Finding("WARN", node.path, node.line, msg))

	generated_ops = {n.op for n in nodes}
	missing_ops = sorted(generated_ops - set(eval_ops))
	for op in missing_ops:
		first = next(n for n in nodes if n.op == op)
		err(first, f"generated op {op!r} has no evalOp branch in {denote_path}")

	for node in nodes:
		arities = eval_ops.get(node.op)
		if arities is not None and len(node.ins) not in arities:
			err(
				node,
				f"{node.op} has {len(node.ins)} inputs, but evalOp fixed arities are {sorted(arities)}",
			)

		if node.op == "OpName.FW_multiref":
			if not node.params:
				err(node, "FW_multiref is missing params := [num_outputs]")
			elif node.params[0] != len(node.outs):
				err(
					node,
					f"FW_multiref params[0]={node.params[0]} but outs.length={len(node.outs)}",
				)

		if strict_comm_params:
			if node.op == "OpName.AllToAllPrim" and len(node.params) != 2:
				err(node, "AllToAllPrim should carry params := [idim, odim]")
			if node.op in {"OpName.ChunkPrim", "OpName.AllGatherPrim"} and len(node.params) != 1:
				err(node, f"{node.op} should carry params := [dim]")

	if check_shapes:
		for node in nodes:
			for tid in node.ins + node.outs:
				if tid not in shapes:
					err(node, f"tid {tid} appears in graph but has no shape entry")

	producers = _producer_by_out(nodes)

	# Forward row/vocab-sharded embedding: all per-rank embedding outputs feed
	# the same AllReduce. These nodes need per-rank row offsets.
	allreduce_embedding_nodes: set[Node] = set()
	for node in nodes:
		if node.op != "OpName.AllReducePrim":
			continue
		embed_inputs = [producers.get(tid) for tid in node.ins]
		if not embed_inputs or any(p is None or p.op != "OpName.FW_embedding" for p in embed_inputs):
			continue
		embed_nodes = [p for p in embed_inputs if p is not None]
		if len({n.ins[0] for n in embed_nodes if len(n.ins) >= 2}) != 1:
			continue
		if len({n.ins[1] for n in embed_nodes if len(n.ins) >= 2}) != len(embed_nodes):
			continue
		for emb in embed_nodes:
			allreduce_embedding_nodes.add(emb)
			expected = _expected_offset(emb, shapes)
			if expected is None:
				warn(emb, "cannot verify embedding offset because weight shape is missing")
			elif emb.params != (expected,):
				err(
					emb,
					f"row/vocab-sharded FW_embedding should have params := [{expected}], got {list(emb.params)}",
				)

	for node in nodes:
		if node.op == "OpName.FW_embedding" and node.params and node not in allreduce_embedding_nodes:
			err(
				node,
				"FW_embedding has offset params but its output is not part of an AllReduce embedding group",
			)

	# Backward row/vocab-sharded embedding: same upstream grad and ids, different
	# weight shards across ranks. These are the BW counterparts of the forward
	# AllReduce embedding pattern.
	bw_groups: dict[tuple[int, int, tuple[int, ...] | None], list[Node]] = {}
	for node in nodes:
		if node.op == "OpName.BW_embedding" and len(node.ins) == 3:
			bw_groups.setdefault((node.ins[0], node.ins[1], shapes.get(node.ins[2])), []).append(node)

	bw_offset_nodes: set[Node] = set()
	for group in bw_groups.values():
		if len(group) <= 1:
			continue
		if len({n.rank for n in group}) != len(group):
			continue
		if len({n.ins[2] for n in group}) != len(group):
			continue
		for node in group:
			bw_offset_nodes.add(node)
			expected = _expected_offset(node, shapes)
			if expected is None:
				warn(node, "cannot verify BW_embedding offset because weight shape is missing")
			elif node.params != (expected,):
				err(
					node,
					f"row/vocab-sharded BW_embedding should have params := [{expected}], got {list(node.params)}",
				)

	for node in nodes:
		if node.op == "OpName.BW_embedding" and node.params and node not in bw_offset_nodes:
			err(
				node,
				"BW_embedding has offset params but is not in a same-(grad, ids) row-sharded group",
			)

	return findings


def main() -> int:
	parser = argparse.ArgumentParser(description=__doc__)
	parser.add_argument("generated", type=Path, help="GeneratedData.lean or a generated Goal_*.lean file")
	parser.add_argument("--denote", type=Path, default=DEFAULT_DENOTE, help="Path to Denote.lean")
	parser.add_argument(
		"--check-shapes",
		action=argparse.BooleanOptionalAction,
		default=None,
		help="Require every graph tid to have a shape entry. Defaults to true for GeneratedData.lean.",
	)
	parser.add_argument(
		"--strict-comm-params",
		action=argparse.BooleanOptionalAction,
		default=True,
		help="Require explicit params for ChunkPrim, AllGatherPrim, and AllToAllPrim.",
	)
	args = parser.parse_args()

	generated = args.generated.resolve()
	denote = args.denote.resolve()
	check_shapes = args.check_shapes
	if check_shapes is None:
		check_shapes = generated.name == "GeneratedData.lean"

	findings = audit(
		generated,
		denote,
		check_shapes=check_shapes,
		strict_comm_params=args.strict_comm_params,
	)
	for finding in findings:
		print(f"{finding.severity}: {finding.path}:{finding.line}: {finding.message}")

	errors = [f for f in findings if f.severity == "ERROR"]
	warnings = [f for f in findings if f.severity == "WARN"]
	if errors:
		print(f"\nFAILED: {len(errors)} error(s), {len(warnings)} warning(s)")
		return 1
	print(f"OK: {generated} passed static audit ({len(warnings)} warning(s))")
	return 0


if __name__ == "__main__":
	raise SystemExit(main())
