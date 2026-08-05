#!/usr/bin/env python3
"""Inject a rank-safe, fail-closed ModuleCodeGen dump plus provenance receipt."""
from __future__ import annotations

import argparse
import re
from pathlib import Path

MARKER = "[TRAINVERIFY_DUMP]"
ANCHOR = re.compile(r"^(?P<indent>\s*)(?P<var>mgener\w*)\s*=\s*ModuleCodeGen\([^\n]*\)\s*$", re.MULTILINE)


def patch_source(src: str) -> str:
    if MARKER in src:
        return src
    match = ANCHOR.search(src)
    if not match:
        raise RuntimeError("ModuleCodeGen anchor not found; refusing to patch")
    indent, var = match.group("indent"), match.group("var")
    injected = [
        indent + "# [TRAINVERIFY_DUMP] rank-safe authority capture",
        indent + "import dill as _tv_dill, hashlib as _tv_hashlib, json as _tv_json",
        indent + "import os as _tv_os, sys as _tv_sys",
        indent + "_tv_dst = _tv_os.environ.get('MGENER_DUMP_PATH')",
        indent + "_tv_rank = int(_tv_os.environ.get('LOCAL_RANK', '0'))",
        indent + "if _tv_dst and _tv_rank == 0:",
        indent + "    _tv_inner_policy = getattr(pas_policy, 'keywords', {}).get('policy', pas_policy)",
        indent + "    _tv_policy = _tv_inner_policy if isinstance(_tv_inner_policy, str) else getattr(_tv_inner_policy, '__module__', '') + '.' + getattr(_tv_inner_policy, '__qualname__', type(_tv_inner_policy).__name__)",
        indent + "    _tv_config_policy = compute_config.pas_config.get('__pas_name')",
        indent + "    if _tv_config_policy and str(_tv_config_policy) != str(_tv_policy):",
        indent + "        raise RuntimeError('policy identity disagreement: ' + str(_tv_config_policy) + ' != ' + str(_tv_policy))",
        indent + "    _tv_expected = _tv_os.environ.get('TRAINVERIFY_EXPECTED_POLICY')",
        indent + "    if _tv_expected and not str(_tv_policy).endswith(_tv_expected):",
        indent + "        raise RuntimeError('unexpected policy for authority dump: ' + str(_tv_policy))",
        indent + "    _tv_sys.setrecursionlimit(100000)",
        indent + "    _tv_tmp = _tv_dst + '.tmp.' + str(_tv_os.getpid())",
        indent + "    _tv_receipt = _tv_dst + '.receipt.json'",
        indent + "    _tv_receipt_tmp = _tv_receipt + '.tmp.' + str(_tv_os.getpid())",
        indent + "    try:",
        indent + "        with open(_tv_tmp, 'wb') as _tv_fp:",
        indent + f"            _tv_dill.dump({var}, _tv_fp)",
        indent + "            _tv_fp.flush()",
        indent + "            _tv_os.fsync(_tv_fp.fileno())",
        indent + "        _tv_os.replace(_tv_tmp, _tv_dst)",
        indent + "        _tv_os.chmod(_tv_dst, 0o444)",
        indent + "        with open(_tv_dst, 'rb') as _tv_fp:",
        indent + "            _tv_pkl_hash = _tv_hashlib.sha256(_tv_fp.read()).hexdigest()",
        indent + "        with open(__file__, 'rb') as _tv_fp:",
        indent + "            _tv_source_hash = _tv_hashlib.sha256(_tv_fp.read()).hexdigest()",
        indent + "        _tv_record = {",
        indent + "            'policy': str(_tv_policy),",
        indent + "            'plan_ngpus': int(compute_config.plan_ngpus),",
        indent + "            'runtime_ngpus': int(compute_config.runtime_ngpus),",
        indent + "            'pkl_sha256': _tv_pkl_hash,",
        indent + "            'patched_parallel_py_sha256': _tv_source_hash,",
        indent + "        }",
        indent + "        with open(_tv_receipt_tmp, 'w', encoding='utf-8') as _tv_fp:",
        indent + "            _tv_json.dump(_tv_record, _tv_fp, sort_keys=True)",
        indent + "            _tv_fp.write('\\n')",
        indent + "            _tv_fp.flush()",
        indent + "            _tv_os.fsync(_tv_fp.fileno())",
        indent + "        _tv_os.replace(_tv_receipt_tmp, _tv_receipt)",
        indent + "        _tv_os.chmod(_tv_receipt, 0o444)",
        indent + "    finally:",
        indent + "        for _tv_leftover in (_tv_tmp, _tv_receipt_tmp):",
        indent + "            if _tv_os.path.exists(_tv_leftover):",
        indent + "                _tv_os.unlink(_tv_leftover)",
        indent + "    print('[TRAINVERIFY_DUMP] wrote ' + _tv_dst, flush=True)",
        "",
    ]
    return src[:match.end()] + "\n" + "\n".join(injected) + src[match.end():]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("parallel_py", type=Path)
    args = parser.parse_args()
    path = args.parallel_py.resolve()
    source = path.read_text(encoding="utf-8")
    patched = patch_source(source)
    if patched == source:
        print(f"already patched: {path}")
        return
    tmp = path.with_suffix(path.suffix + ".tmp")
    try:
        tmp.write_text(patched, encoding="utf-8")
        tmp.replace(path)
    finally:
        tmp.unlink(missing_ok=True)
    print(f"patched: {path}")


if __name__ == "__main__":
    main()
