#!/usr/bin/env python3
"""Explicit historical source-name checking or current emitter inventory.

Neither mode invokes Lean or establishes proof coverage/kernel verification.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

HISTORICAL_COMMIT = "ad821ce18494d30b5517a36260faa817fb45cda1"
HISTORICAL_TOTAL = 1156
HISTORICAL_NAMES = 1154


def inventory(source: Path) -> dict:
    """Scan the emitter's line-oriented target headers, not general Lean syntax.

    Bodies, statement helpers, comments' mathematical claims and proof files
    are not validated. Unknown target headers and lossy classifications fail.
    """
    try:
        text = source.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        raise ValueError(f"cannot read inventory source {source}: {exc}") from exc

    groups = {key: set() for key in (
        "ordinary_intermediate", "emitted_zigzag", "ordinary_top",
        "nonordinary_top_discoveries", "nonordinary_intermediate",
    )}

    def reject(reason):
        raise ValueError(f"invalid generated source {source}: {reason}")

    for number, line in enumerate(text.splitlines(), 1):
        key = None
        if line.lstrip().startswith("-- NOT an ordinary gather:"):
            match = re.fullmatch(
                r"-- NOT an ordinary gather: ((intermediateGoal|goal)_([0-9]+)) \(ts = ([0-9]+)\)\.", line
            )
            if not match:
                reject(f"unsupported discovery header at line {number}")
            name, kind, tid, ts = match.groups()
            if kind == "intermediateGoal" and tid != ts:
                reject(f"discovery tid mismatch at line {number}: {name} / {ts}")
            key = "nonordinary_intermediate" if kind == "intermediateGoal" else "nonordinary_top_discoveries"
        elif re.match(r"\s*def\s+(?:intermediateGoal_|goal_)", line):
            ordinary = re.fullmatch(r"def ((intermediateGoal|goal)_[0-9]+) : LineageGoal :=", line)
            zigzag = re.fullmatch(
                r"def (intermediateGoal_[0-9]+)_zigzag : TrainVerify\.Denote\.GeneratedPatterns\.ZigzagLineageGoal :=", line
            )
            if ordinary:
                name, kind = ordinary.groups()
                key = "ordinary_intermediate" if kind == "intermediateGoal" else "ordinary_top"
            elif zigzag:
                name = zigzag.group(1)
                key = "emitted_zigzag"
            elif not re.fullmatch(r"def (?:intermediateGoal|goal)_[0-9]+_stmt : Prop :=", line):
                reject(f"unsupported target header at line {number}")
        if key is not None:
            if name in groups[key]:
                reject(f"duplicate {key}: {name} at line {number}")
            groups[key].add(name)

    ordinary = groups["ordinary_intermediate"]
    zigzag = groups["emitted_zigzag"]
    discoveries = groups.pop("nonordinary_intermediate")
    overlap = (ordinary & (discoveries | zigzag)) | (groups["ordinary_top"] & groups["nonordinary_top_discoveries"])
    if overlap:
        reject(f"inconsistent ordinary/nonordinary classifications: {sorted(overlap)}")
    if zigzag - discoveries:
        reject(f"zigzag without nonordinary discovery: {sorted(zigzag - discoveries)}")
    groups["suppressed_nonordinary_intermediate_discoveries"] = discoveries - zigzag
    if not any(groups.values()):
        reject("no emitter target discoveries found")
    return {
        "mode": "inventory",
        "scope": "source-only; not proof coverage; not kernel verification",
        "source": str(source),
        "limitations": "emitter discoveries, not verified counterexamples; line-oriented target headers only, not a general Lean parser or record-body validation",
        "id_convention": "base target IDs; emitted_zigzag declarations append _zigzag",
        "categories": {key: {"count": len(ids), "ids": sorted(ids)} for key, ids in groups.items()},
        "total_discoveries": sum(map(len, groups.values())),
    }


def historical_sources(repo: Path) -> tuple[str, str]:
    """Read only pinned Git blobs; never use checkout, Python from Git, or a shell."""
    generated_path = "trainverify/denote/GeneratedYOCOMoE.lean"
    proof_dir = "trainverify/denote/yoco_goals"
    # Ignore caller Git redirections/replacements/config injection. Disable lazy
    # promisor fetch as well as every transport; missing objects must fail locally.
    env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    env.update(GIT_NO_REPLACE_OBJECTS="1", GIT_NO_LAZY_FETCH="1", GIT_TERMINAL_PROMPT="0", GIT_ALLOW_PROTOCOL="")
    deadline = time.monotonic() + 90
    byte_count = 0

    def git(*args):
        nonlocal byte_count
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            raise ValueError("Git source read exceeded 90 seconds")
        result = subprocess.run(
            ["git", "-c", "protocol.allow=never", "-C", str(repo.resolve()), *args],
            env=env, capture_output=True, timeout=min(30, remaining), check=False,
        )
        if result.returncode:
            raise ValueError(result.stderr.decode("utf-8", errors="replace").strip()[:1000])
        byte_count += len(result.stdout)
        if byte_count > 64 * 1024 * 1024:
            raise ValueError("Git source read exceeded 64 MiB")
        return result.stdout

    try:
        tree = git("ls-tree", "-rz", "--full-tree", HISTORICAL_COMMIT, "--", generated_path, proof_dir)
        paths = []
        for entry in tree.decode("utf-8").split("\0"):
            if not entry:
                continue
            metadata, path = entry.split("\t", 1)
            mode, kind, _oid = metadata.split()
            if path != generated_path and not (Path(path).parent.as_posix() == proof_dir and path.endswith(".lean")):
                continue
            if kind != "blob" or mode not in ("100644", "100755"):
                raise ValueError(f"expected regular source blob: {path}")
            paths.append(path)
        if generated_path not in paths or len(paths) < 2 or len(paths) > 4096:
            raise ValueError("missing generated/proof blobs or excessive source-file count")
        sources = {
            path: git("show", "--no-ext-diff", "--no-textconv", f"{HISTORICAL_COMMIT}:{path}")
            for path in sorted(paths)
        }
        generated = sources.pop(generated_path).decode("utf-8")
        # Preserve the old proof-file decoding policy and immediate *.lean scope.
        proofs = "\n".join(blob.decode("utf-8", errors="ignore") for blob in sources.values())
        return generated, proofs
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        raise ValueError(
            f"historical blobs unavailable at {HISTORICAL_COMMIT} in {repo}: {exc}; "
            "use --historical --repo PATH with a local repository containing the complete pinned commit; "
            "or use --inventory for live source-only accounting (no fallback or network fetch)"
        ) from exc


def historical_name_report(generated: str, proofs: str) -> str:
    """Original checkpoint's exact-name set arithmetic, not proof acceptance."""
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
    # The historical goal_5 theorem uses the goal number, the other two use tids.
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
    total = ordinary_total + zigzag_total + len(top_false)
    done = ordinary_done + zigzag_done
    # Explicit checks also survive python -O; the historical constants never move.
    if total != HISTORICAL_TOTAL:
        raise ValueError(f"unexpected corpus size: {total}; historical expected {HISTORICAL_TOTAL}")
    if done != HISTORICAL_NAMES:
        raise ValueError(f"coverage changed: {done}; historical expected {HISTORICAL_NAMES} source-name matches")
    return "\n".join([
        "HISTORICAL SOURCE-NAME CHECK",
        f"commit: {HISTORICAL_COMMIT}",
        "scope: source-name matching only; not fresh Lean acceptance; not proof coverage or kernel verification",
        f"ordinary: {ordinary_done}/{ordinary_total}",
        f"  missing: {sorted((ordinary - ordinary_proved) | (top_ordinary - top_proved))}",
        f"zigzag: {zigzag_done}/{zigzag_total}",
        f"  missing: {sorted(zigzag - zigzag_proved)}",
        f"historical nonordinary top discoveries: {len(top_false)}: {sorted(top_false)}",
        "comments are emitter discoveries, not verified counterexamples from this scan",
        f"source-name matches: {done}/{total}",
    ])


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--historical", action="store_true", help="pinned historical source-name check")
    modes.add_argument("--inventory", action="store_true", help="current source-only emitter inventory (JSON)")
    parser.add_argument("source_root", nargs="?", type=Path, help="inventory package root containing denote/; default: script's package")
    parser.add_argument("--repo", type=Path, help="local Git repository containing the fixed historical commit")
    args = parser.parse_args(argv)
    if not (args.historical or args.inventory):
        parser.error("coverage is historical-only; choose --historical --repo PATH or --inventory [source_root]")
    if args.inventory:
        if args.repo is not None:
            parser.error("--repo is only valid with --historical")
        root = args.source_root if args.source_root is not None else Path(__file__).resolve().parents[1]
        try:
            report = inventory(root.resolve() / "denote/GeneratedYOCOMoE.lean")
        except ValueError as exc:
            parser.error(str(exc))
        print(json.dumps(report, indent=2, sort_keys=True))
        return 0
    if args.repo is None:
        parser.error("--historical requires --repo PATH containing the pinned Git commit")
    if args.source_root is not None:
        parser.error("source_root is only valid with --inventory; historical mode never reads live sources")
    try:
        print(historical_name_report(*historical_sources(args.repo)))
    except ValueError as exc:
        print(f"{parser.prog}: error: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
