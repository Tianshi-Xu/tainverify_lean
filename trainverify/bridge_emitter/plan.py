#!/usr/bin/env python3
"""Read-only proof-plan CLI for bridge-emitter goals.

Exit codes: 0 composable source, 1 unsupported, 2 invocation/runtime error.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
from typing import NoReturn

sys.path.insert(0, os.path.dirname(__file__))

from parser import load_goal_ir
from proof_compiler import build_default_registry, compile_proof_plan
from composer import compose_full_topology
from target_config import MOD_PREFIX


def _error_payload(code: str, message: str) -> dict:
    return {
        "schema_version": 1,
        "status": "error",
        "diagnostics": [
            {
                "severity": "error",
                "code": code,
                "message": message,
            }
        ],
    }


class _PlanArgumentParser(argparse.ArgumentParser):
    def __init__(self, *args, json_errors: bool = False, **kwargs):
        self.json_errors = json_errors
        super().__init__(*args, **kwargs)

    def error(self, message: str) -> NoReturn:
        if not self.json_errors:
            super().error(message)
        payload = _error_payload("cli.usage", message)
        sys.stdout.write(
            json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n"
        )
        raise SystemExit(2)


def _human(plan) -> str:
    lines = [
        f"goal_{plan.goal_id}: {'SUPPORTED' if plan.supported else 'UNSUPPORTED'}",
        f"relation: {plan.relation.kind.value}",
        f"certificate steps: {len(plan.steps)}",
    ]
    for issue in plan.diagnostics:
        where = ""
        if issue.side is not None:
            where = f" {issue.side}"
        if issue.node_index is not None:
            where += f"[{issue.node_index}]"
        lines.append(f"ERROR {issue.code.value}{where}: {issue.message}")
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    raw_argv = list(sys.argv[1:] if argv is None else argv)
    parser = _PlanArgumentParser(
        description="Plan a deterministic Lean certificate DAG",
        json_errors="--json" in raw_argv,
    )
    parser.add_argument("goal", type=int)
    parser.add_argument("--root", default=os.path.dirname(os.path.dirname(os.path.dirname(__file__))))
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args(raw_argv)

    try:
        ir = load_goal_ir(args.goal, os.path.abspath(args.root))
        plan = compile_proof_plan(ir, build_default_registry())
        composition = (
            compose_full_topology(ir, MOD_PREFIX) if plan.supported else None
        )
    except Exception as exc:
        payload = _error_payload("cli.runtime", f"{type(exc).__name__}: {exc}")
        if args.as_json:
            sys.stdout.write(json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n")
        else:
            sys.stderr.write(f"ERROR cli.runtime: {payload['diagnostics'][0]['message']}\n")
        return 2

    certificate_source_complete = composition is not None and composition.supported
    if args.as_json:
        payload = plan.to_dict()
        payload["planning_status"] = payload["status"]
        payload["certificate_source_complete"] = certificate_source_complete
        payload["kernel_checked"] = False
        payload["proof_complete"] = False
        if composition is not None:
            payload["composition"] = {
                "status": "supported" if composition.supported else "unsupported",
                "rule_id": composition.rule_id,
                "diagnostics": [
                    {
                        "code": issue.code.value,
                        "message": issue.message,
                        "node_index": issue.node_index,
                    }
                    for issue in composition.diagnostics
                ],
            }
        else:
            payload["composition"] = None
        payload["status"] = (
            "composable" if certificate_source_complete else "unsupported"
        )
        sys.stdout.write(json.dumps(payload, sort_keys=True, separators=(",", ":")) + "\n")
    else:
        sys.stdout.write(_human(plan))
        if composition is not None:
            if composition.supported:
                sys.stdout.write(f"composition: {composition.rule_id}\n")
            else:
                issue = composition.diagnostics[0]
                sys.stdout.write(f"ERROR {issue.code.value}: {issue.message}\n")
    return 0 if certificate_source_complete else 1


if __name__ == "__main__":
    raise SystemExit(main())
