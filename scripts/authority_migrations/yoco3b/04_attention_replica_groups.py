#!/usr/bin/env python3
"""Add complete fail-closed CP2 buddy metadata to legacy YOCO-3B authority."""
from __future__ import annotations
import argparse, hashlib, os, re, tempfile
from pathlib import Path

INPUT_SHA256 = "3fe2cd76ca48a616960478ed0861dbfe0713b93ca5a1caebeaa4246d7f1f6b38"
OUTPUT_SHA256 = "145300e8f502bb9a12a99fa5fba2fa9850b1f3d766fe9be434c35c898a9f3198"
SUPPORTED = {
    "FW_maybe_shuffle", "FW_maybe_unshuffle",
    "FW_attn_zigzag", "FW_attn_sliding_window",
}
EXPECTED_COUNTS = {
    "FW_maybe_shuffle": (1, 2),
    "FW_maybe_unshuffle": (1, 2),
    "FW_attn_zigzag": (0, 20),
    "FW_attn_sliding_window": (30, 60),
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def definition(source: str, name: str) -> tuple[int, int, str]:
    match = re.search(rf"(?m)^def\s+{re.escape(name)}\s*:\s*GraphDecl\s*:=\s*by\n", source)
    if match is None:
        raise RuntimeError(f"missing graph definition {name}")
    nxt = re.search(r"(?m)^def\s+", source[match.end():])
    end = len(source) if nxt is None else match.end() + nxt.start()
    return match.start(), end, source[match.start():end]


def parse_nodes(block: str):
    node_re = re.compile(
        r'\{\s*rank\s*:=\s*(\d+),\s*op\s*:=\s*"OpName\.([^"\n]+)"'
        r'[^\n]*?ins\s*:=\s*\[([0-9,\s]*)\][^\n]*?outs\s*:=\s*\[([0-9,\s]*)\]'
        r'(?:[^\n]*?params\s*:=\s*\[([0-9,\s]*)\])?[^\n]*?\}'
    )
    result = []
    for match in node_re.finditer(block):
        op = match.group(2)
        if op not in SUPPORTED:
            continue
        rank = int(match.group(1))
        ins = tuple(map(int, re.findall(r"\d+", match.group(3))))
        outs = tuple(map(int, re.findall(r"\d+", match.group(4))))
        params = tuple(map(int, re.findall(r"\d+", match.group(5) or "")))
        if len(outs) != 1:
            raise RuntimeError(f"{op} must have one primary output")
        result.append((rank, op, ins, outs[0], params))
    return result


def logical_key(rank: int, op: str, ins: tuple[int, ...], params: tuple[int, ...], sm: bool):
    if op in {"FW_maybe_shuffle", "FW_maybe_unshuffle"}:
        expected = (1, 0) if sm else (2, rank)
        if len(ins) != 2 or params != expected:
            raise RuntimeError(f"{op} collective parameters/signature disagree")
        return op, ins[1]
    if len(ins) != 5 or len(params) != 6:
        raise RuntimeError(f"{op} attention signature disagrees")
    # cuQ/cuKV and literal attention parameters identify the logical call;
    # rank-local Q/K/V are deliberately not used as a grouping oracle.
    return op, ins[3], ins[4], params


def validate_and_transform(source: str) -> tuple[str, int]:
    _, _, sm_block = definition(source, "sm")
    pm_start, pm_end, pm_block = definition(source, "pm")
    if "replicaGroups" in sm_block or "replicaGroups" in pm_block:
        if sha256(source.encode()) != OUTPUT_SHA256:
            raise RuntimeError("partial or foreign replicaGroups authority")
        return source, 0
    sm_nodes, pm_nodes = parse_nodes(sm_block), parse_nodes(pm_block)
    for op, (sm_count, pm_count) in EXPECTED_COUNTS.items():
        actual = (sum(n[1] == op for n in sm_nodes), sum(n[1] == op for n in pm_nodes))
        if actual != (sm_count, pm_count):
            raise RuntimeError(f"{op} cardinality mismatch: {actual}")
    groups_data = []
    for op, (sm_count, pm_count) in EXPECTED_COUNTS.items():
        sms = [n for n in sm_nodes if n[1] == op]
        pm0 = [n for n in pm_nodes if n[1] == op and n[0] == 0]
        pm1 = [n for n in pm_nodes if n[1] == op and n[0] == 1]
        if len(pm0) != pm_count // 2 or len(pm1) != pm_count // 2:
            raise RuntimeError(f"{op} PM rank cardinality mismatch")
        if len(sms) != sm_count or any(n[0] != 0 for n in sms):
            raise RuntimeError(f"{op} SM rank cardinality mismatch")
        for ordinal, (node0, node1) in enumerate(zip(pm0, pm1)):
            key0 = logical_key(node0[0], op, node0[2], node0[4], False)
            key1 = logical_key(node1[0], op, node1[2], node1[4], False)
            if key0 != key1:
                raise RuntimeError(f"{op} rank-pair logical signatures disagree at ordinal {ordinal}")
            local_indices = (0,) if op in {
                "FW_maybe_shuffle", "FW_maybe_unshuffle", "FW_attn_zigzag"
            } else (0, 1, 2)
            if (any(node1[2][index] != node0[2][index] + 1 for index in local_indices)
                    or node1[3] != node0[3] + 1):
                raise RuntimeError(f"{op} rank-local TID pairing disagrees at ordinal {ordinal}")
            if sms:
                sm_node = sms[ordinal]
                sm_key = logical_key(sm_node[0], op, sm_node[2], sm_node[4], True)
                if sm_key != key0:
                    raise RuntimeError(f"{op} SM/PM logical signatures disagree at ordinal {ordinal}")
                cid = sm_node[3]
            else:
                cid = node0[3]
            groups_data.append((cid, op, node0[3], node1[3]))
    groups = []
    for cid, op, out0, out1 in sorted(groups_data):
        groups.append(
            "{ logical := { cid := " + str(cid) + ", mb := 0, irname := \"" + op
            + "\" }, members := [{ rank := 0, primaryOutTid := " + str(out0)
            + " }, { rank := 1, primaryOutTid := " + str(out1) + " }] }"
        )
    marker = "  refine { numRanks := 2, nodes := ?_ }"
    if pm_block.count(marker) != 1:
        raise RuntimeError("PM GraphDecl constructor is not exact legacy form")
    replacement = "  refine { numRanks := 2, nodes := ?_, replicaGroups := [" + ", ".join(groups) + "] }"
    migrated = pm_block.replace(marker, replacement, 1)
    return source[:pm_start] + migrated + source[pm_end:], len(groups)


def write_atomic(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(data); stream.flush(); os.fsync(stream.fileno())
        os.replace(temporary, path)
    except BaseException:
        try: os.unlink(temporary)
        except FileNotFoundError: pass
        raise


def main() -> None:
    parser = argparse.ArgumentParser(); parser.add_argument("input", type=Path); parser.add_argument("output", type=Path)
    args = parser.parse_args(); data = args.input.read_bytes(); digest = sha256(data)
    if digest not in {INPUT_SHA256, OUTPUT_SHA256}:
        raise RuntimeError(f"unexpected input SHA-256: {digest}")
    transformed, changed = validate_and_transform(data.decode("utf-8")); result = transformed.encode()
    if sha256(result) != OUTPUT_SHA256:
        raise RuntimeError(f"unexpected output SHA-256: {sha256(result)}")
    expected_groups = sum(max(sm_count, pm_count // 2) for sm_count, pm_count in EXPECTED_COUNTS.values())
    if digest == INPUT_SHA256 and changed != expected_groups:
        raise RuntimeError(f"unexpected group count: {changed}")
    if digest == OUTPUT_SHA256 and changed:
        raise RuntimeError("already-migrated input unexpectedly changed")
    write_atomic(args.output, result)
    print(f"replica_groups input={digest} output={sha256(result)} changed={changed}")


if __name__ == "__main__": main()
