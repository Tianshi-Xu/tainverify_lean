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
        indent + "import os as _tv_os, re as _tv_re, sys as _tv_sys, types as _tv_types",
        indent + "_tv_dst = _tv_os.environ.get('MGENER_DUMP_PATH')",
        indent + "_tv_rank = int(_tv_os.environ.get('LOCAL_RANK', '0'))",
        indent + "if _tv_dst and _tv_rank == 0:",
        indent + "    _tv_llm_hash = _tv_os.environ.get('TRAINVERIFY_PATCHED_LLM_GEMM_SHA256', '')",
        indent + "    if len(_tv_llm_hash) != 64 or any(_tv_c not in '0123456789abcdef' for _tv_c in _tv_llm_hash):",
        indent + "        raise RuntimeError('missing or invalid patched llm GEMM source hash')",
        indent + "    _tv_comm_hash = _tv_os.environ.get('TRAINVERIFY_COMM_PROFILE_SHA256', '')",
        indent + "    if len(_tv_comm_hash) != 64 or any(_tv_c not in '0123456789abcdef' for _tv_c in _tv_comm_hash):",
        indent + "        raise RuntimeError('missing or invalid communication profile hash')",
        indent + "    _tv_comp_hash = _tv_os.environ.get('TRAINVERIFY_COMP_PROFILE_SHA256', '')",
        indent + "    if len(_tv_comp_hash) != 64 or any(_tv_c not in '0123456789abcdef' for _tv_c in _tv_comp_hash):",
        indent + "        raise RuntimeError('missing or invalid computation profile hash')",
        indent + "    _tv_dp_solver_hash = _tv_os.environ.get('TRAINVERIFY_DP_SOLVER_SHA256', '')",
        indent + "    if len(_tv_dp_solver_hash) != 64 or any(_tv_c not in '0123456789abcdef' for _tv_c in _tv_dp_solver_hash):",
        indent + "        raise RuntimeError('missing or invalid dp solver extension hash')",
        indent + "    _tv_inner_policy = getattr(pas_policy, 'keywords', {}).get('policy', pas_policy)",
        indent + "    _tv_policy = _tv_inner_policy if isinstance(_tv_inner_policy, str) else getattr(_tv_inner_policy, '__module__', '') + '.' + getattr(_tv_inner_policy, '__qualname__', type(_tv_inner_policy).__name__)",
        indent + "    _tv_config_policy = compute_config.pas_config.get('__pas_name')",
        indent + "    if _tv_config_policy and str(_tv_config_policy) != str(_tv_policy):",
        indent + "        raise RuntimeError('policy identity disagreement: ' + str(_tv_config_policy) + ' != ' + str(_tv_policy))",
        indent + "    _tv_expected = _tv_os.environ.get('TRAINVERIFY_EXPECTED_POLICY')",
        indent + "    if _tv_expected and not str(_tv_policy).endswith(_tv_expected):",
        indent + "        raise RuntimeError('unexpected policy for authority dump: ' + str(_tv_policy))",
        indent + "    _tv_sys.setrecursionlimit(100000)",
        indent + "    _tv_llm_root = _tv_os.environ.get('TRAINVERIFY_LLM_SOURCE_ROOT', '')",
        indent + "    if not _tv_os.path.isabs(_tv_llm_root):",
        indent + "        raise RuntimeError('missing absolute authenticated LLM source root')",
        indent + "    _tv_seen = set()",
        indent + "    _tv_counts = [0, 0]",
        indent + "    def _tv_filename(_tv_name):",
        indent + "        if _tv_name.startswith(_tv_llm_root + '/'):",
        indent + "            return '/trainverify/llm/' + _tv_name[len(_tv_llm_root) + 1:]",
        indent + "        _tv_match = _tv_re.fullmatch(r'/proc/[0-9]+/fd/[0-9]+/nnscaler/(.+)', _tv_name)",
        indent + "        return '/trainverify/nnscaler/' + _tv_match.group(1) if _tv_match else _tv_name",
        indent + "    def _tv_normalize(_tv_obj):",

        indent + "        if isinstance(_tv_obj, (str, bytes, int, float, bool, type(None), type, complex)):",
        indent + "            return",
        indent + "        _tv_identity = id(_tv_obj)",
        indent + "        if _tv_identity in _tv_seen:",
        indent + "            return",
        indent + "        _tv_seen.add(_tv_identity)",
        indent + "        if isinstance(_tv_obj, _tv_types.FunctionType):",
        indent + "            _tv_old_name = _tv_obj.__code__.co_filename",
        indent + "            _tv_new_name = _tv_filename(_tv_old_name)",
        indent + "            if _tv_new_name != _tv_old_name:",
        indent + "                _tv_obj.__code__ = _tv_obj.__code__.replace(co_filename=_tv_new_name)",
        indent + "                _tv_counts[1] += 1",
        indent + "            _tv_values = list(_tv_obj.__defaults__ or ()) + list((_tv_obj.__kwdefaults__ or {}).values())",
        indent + "            _tv_values += [_tv_cell.cell_contents for _tv_cell in (_tv_obj.__closure__ or ())]",
        indent + "        elif isinstance(_tv_obj, dict):",
        indent + "            _tv_values = list(_tv_obj.values())",
        indent + "        elif isinstance(_tv_obj, (list, tuple, set, frozenset)):",
        indent + "            _tv_values = list(_tv_obj)",
        indent + "        elif hasattr(_tv_obj, '__dict__'):",
        indent + "            _tv_data = vars(_tv_obj)",
        indent + "            _tv_comment = _tv_data.get('_comment')",
        indent + "            if isinstance(_tv_comment, str) and _tv_comment.startswith('File \\\"' + _tv_llm_root + '/'):",
        indent + "                _tv_data['_comment'] = 'File \\\"/trainverify/llm/' + _tv_comment[len('File \\\"' + _tv_llm_root + '/'): ]",
        indent + "                _tv_counts[0] += 1",
        indent + "            _tv_values = list(_tv_data.values())",
        indent + "        else:",
        indent + "            return",
        indent + "        for _tv_value in _tv_values:",
        indent + "            _tv_normalize(_tv_value)",
        indent + f"    _tv_normalize({var})",
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
        indent + "            _tv_pkl_bytes = _tv_fp.read()",
        indent + "        if _tv_llm_root.encode() in _tv_pkl_bytes or _tv_re.search(rb'/proc/[0-9]+/fd/[0-9]+/nnscaler/', _tv_pkl_bytes):",
        indent + "            raise RuntimeError('dynamic provenance path survived canonicalization')",
        indent + "        _tv_pkl_hash = _tv_hashlib.sha256(_tv_pkl_bytes).hexdigest()",
        indent + "        _tv_loader = globals().get('__loader__')",
        indent + "        if _tv_loader is None or not hasattr(_tv_loader, 'get_data'):",
        indent + "            raise RuntimeError('parallel.py loader cannot provide authenticated source bytes')",
        indent + "        _tv_source = _tv_loader.get_data(__file__)",
        indent + "        _tv_source_hash = _tv_hashlib.sha256(_tv_source).hexdigest()",
        indent + "        _tv_record = {",
        indent + "            'policy': str(_tv_policy),",
        indent + "            'plan_ngpus': int(compute_config.plan_ngpus),",
        indent + "            'runtime_ngpus': int(compute_config.runtime_ngpus),",
        indent + "            'pkl_sha256': _tv_pkl_hash,",
        indent + "            'patched_parallel_py_sha256': _tv_source_hash,",
        indent + "            'patched_llm_gemm_py_sha256': _tv_llm_hash,",
        indent + "            'comm_profile_sha256': _tv_comm_hash,",
        indent + "            'comp_profile_sha256': _tv_comp_hash,",
        indent + "            'dp_solver_extension_sha256': _tv_dp_solver_hash,",
        indent + "            'canonicalized_comment_count': _tv_counts[0],",
        indent + "            'canonicalized_code_count': _tv_counts[1],",
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
