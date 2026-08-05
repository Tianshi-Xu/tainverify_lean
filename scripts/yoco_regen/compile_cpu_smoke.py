#!/usr/bin/env python3
"""Compile current YOCO-MoE A0.4B SM/PM smoke artifacts on CPU.

This validates tracing/codegen and graph shape only. It deliberately uses the
built-in deterministic TP policy, not production pas_autodist, and therefore
must never be promoted to authority artifacts.
"""
from __future__ import annotations
import argparse
import copy
import json
import os
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.yoco_regen.atomic_publish import rename_noreplace
from scripts.yoco_regen.safe_cleanup import create_owned_stage, cleanup_owned_stage

STUBS = Path(__file__).resolve().parent / 'stubs'

def configure_imports(llm_train: Path) -> None:
    os.environ['YOCO_LLM_TRAIN_REPO'] = str(llm_train)
    sys.path[:0] = [str(STUBS), str(llm_train / 'llm')]
    import triton_shim  # noqa: F401

def build_model_args(plan_ngpus: int, seq_len: int, layers: int | None):
    from config import model_args
    from parallelism import resolve_parallel_sizes
    runtime_args = copy.deepcopy(model_args['YOCO-MoE-A0.4B'])
    runtime_args.max_seq_len = seq_len
    if layers is not None:
        if layers <= 0 or layers % 2:
            raise ValueError('--layers must be a positive even number')
        runtime_args.n_layers = layers
        runtime_args.yoco_cross_layers = layers // 2
    configured_cp_size = runtime_args.cp_size
    resolve_parallel_sizes(runtime_args, plan_ngpus)
    codegen_args = copy.deepcopy(runtime_args)
    if not runtime_args.dp_sharded and configured_cp_size == 0:
        codegen_args.cp_size = 0
    return runtime_args, codegen_args

def dummy_args(seq_len: int):
    import torch
    return {
        'tokens': torch.arange(seq_len, dtype=torch.long) % 1000,
        'context': {
            'positions': torch.arange(seq_len, dtype=torch.long),
            'cu_seqlens_q': torch.tensor([0, seq_len], dtype=torch.int32),
            'cu_seqlens_k': torch.tensor([0, seq_len], dtype=torch.int32),
            'max_seqlen_q': seq_len,
            'max_seqlen_k': seq_len,
        },
        'last_hidden_only': True,
    }

def compile_one(llm_train: Path, out_dir: Path, plan_ngpus: int, seq_len: int, layers: int | None):
    import dill
    import nnscaler
    from arch.model import Model
    from nnscaler.parallel import ComputeConfig, parallelize
    runtime_args, codegen_args = build_model_args(plan_ngpus, seq_len, layers)
    target = out_dir / ('sm_mgener.pkl' if plan_ngpus == 1 else 'pm_mgener.pkl')
    gen_dir = out_dir / f'.nnscaler_tp{plan_ngpus}'
    if target.exists():
        raise FileExistsError(target)
    os.environ['MGENER_DUMP_PATH'] = str(target)
    config = ComputeConfig(
        plan_ngpus=plan_ngpus,
        runtime_ngpus=plan_ngpus,
        constant_folding=True,
        trace_strategy='cpu',
        use_zero=0,
        use_end2end=False,
        pas_config={
            '_pas_name': 'tp', '_gbs': 1, '_tp_size': plan_ngpus,
            '_pp_size': 1, '_dp_size': 1, 'update_freq': 1,
            'use_fp16': False, 'use_bf16': False,
            'mem_constraint': 200,
        },
        user_config={
            'cp_size': runtime_args.cp_size,
            'ep_size': runtime_args.ep_size,
            'data_lane_size': plan_ngpus // runtime_args.cp_size,
            'authority': False,
        },
    )
    parallelize(Model(codegen_args), dummy_args(seq_len), 'tp', config,
                gen_savedir=gen_dir, reuse='override', load_module=False)
    if not target.is_file() or target.stat().st_size == 0:
        raise RuntimeError(f'missing dump: {target}')
    sys.setrecursionlimit(100000)
    with target.open('rb') as handle:
        mgener = dill.load(handle)
    world = {
        'model_name': 'yocomoea04b', 'num_dp': 1, 'num_tp': plan_ngpus,
        'num_pp': 1, 'num_mb': 1, 'gbs': 1,
        'num_layers': codegen_args.n_layers // 2, 'num_heads': codegen_args.head,
        'hidden_size': codegen_args.d_model, 'seqlen': seq_len,
        'n_activated_experts': codegen_args.moe_top_k,
        'n_routed_experts': codegen_args.moe_expert_num,
    }
    metadata = {
        'schema_version': 1, 'authority': False, 'policy': 'tp-smoke',
        'plan_ngpus': plan_ngpus, 'runtime_ngpus': plan_ngpus,
        'runtime_cp_size': runtime_args.cp_size,
        'runtime_ep_size': runtime_args.ep_size,
        'codegen_cp_size': codegen_args.cp_size,
        'model': 'YOCO-MoE-A0.4B', 'max_seq_len': seq_len,
        'n_layers': codegen_args.n_layers,
        'yoco_cross_layers': codegen_args.yoco_cross_layers,
        'devices': list(mgener.devices), 'nnscaler_version': nnscaler.__version__,
    }
    prefix = 'sm' if plan_ngpus == 1 else 'pm'
    (out_dir / f'{prefix}_mgener.json').write_text(
        json.dumps(world, indent=2, sort_keys=True) + '\n', encoding='utf-8')
    (out_dir / f'{prefix}_provenance.json').write_text(
        json.dumps(metadata, indent=2, sort_keys=True) + '\n', encoding='utf-8')

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--llm-train', type=Path, required=True)
    parser.add_argument('--out-dir', type=Path, required=True)
    parser.add_argument('--seq-len', type=int, default=128)
    parser.add_argument('--layers', type=int, default=4,
                        help='positive even count; use 24 for full-model smoke')
    parser.add_argument('--plans', type=int, nargs='+', default=[1, 2])
    args = parser.parse_args()
    llm_train = args.llm_train.resolve(); out_dir = args.out_dir.absolute()
    if not (llm_train / 'llm' / 'arch' / 'model.py').is_file():
        raise SystemExit(f'not an llm-train checkout: {llm_train}')
    if out_dir.exists():
        raise SystemExit(f'output directory already exists: {out_dir}')
    out_dir.parent.mkdir(parents=True, exist_ok=True)
    stage, marker, stage_dev, stage_ino = create_owned_stage(
        out_dir.parent, f'.{out_dir.name}.smoke-')
    try:
        configure_imports(llm_train)
        for plan in args.plans:
            if plan not in (1, 2):
                raise SystemExit('smoke supports plans 1 and 2 only')
            compile_one(llm_train, stage, plan, args.seq_len, args.layers)
        for gen_dir in stage.glob('.nnscaler_tp*'):
            shutil.rmtree(gen_dir)
        rename_noreplace(stage, out_dir)
    except BaseException:
        cleanup_owned_stage(stage, marker, stage_dev, stage_ino)
        raise

if __name__ == '__main__':
    main()
