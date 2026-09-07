"""Observe genuine nnScaler codegen objects without changing graph computation."""
from contextlib import contextmanager


@contextmanager
def capture_codegen(parallel_module):
    """Single-process capture hook; always call/restore the original constructor."""
    original = parallel_module.ModuleCodeGen
    captured = []

    def observe(*args, **kwargs):
        result = original(*args, **kwargs)
        captured.append(result)
        return result

    parallel_module.ModuleCodeGen = observe
    try:
        yield captured
    finally:
        parallel_module.ModuleCodeGen = original


def main():
    """Capture the repository's deterministic GPT model, not llm-train YOCO.

    JSON supplies `model` (genmodel.model.gpt.Config), `compute` (the installed
    nnScaler ComputeConfig), `policy`, `batch_size`, and `seed`. Native nnScaler
    validates compute settings. No synthetic graph or cost-profile substitution.
    Run from the repo root: python -m scripts.gpt_capture --config ... --out ...
    """
    import argparse
    import importlib
    import json
    import sys
    from dataclasses import asdict
    from pathlib import Path

    parser = argparse.ArgumentParser(description=main.__doc__)
    parser.add_argument('--config', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    payload = json.loads(args.config.read_text())
    if payload['policy'] not in ('tp', 'dp'):
        raise ValueError('capture World supports only builtin tp/dp policies; pipeline placement is not inferred')
    import dill as pickle  # nnScaler annotations include local modifier closures.
    import torch
    import nnscaler
    from genmodel.model.gpt import Config, GPT, dummy_data
    parallel = importlib.import_module('nnscaler.parallel')
    cfg = Config(**payload['model'])
    cc = parallel.ComputeConfig(**payload['compute'])
    if not torch.cuda.is_available():
        raise RuntimeError('This capture entry requires a real CUDA forward/backward')
    torch.cuda.set_device(0)
    torch.manual_seed(payload['seed'])
    model = GPT(cfg).cuda()
    input_ids, position_ids = dummy_data(payload['batch_size'], cfg)
    inputs = {'input_ids': input_ids, 'position_ids': position_ids}
    loss = model(**inputs)
    loss.backward()
    if not torch.isfinite(loss).all() or not all(
        p.grad is not None and torch.isfinite(p.grad).all() for p in model.parameters()
    ):
        raise RuntimeError('non-finite output/gradient or missing parameter gradient')
    reference_loss = loss.item()
    model.zero_grad(set_to_none=True)
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    sys.setrecursionlimit(100000)
    with capture_codegen(parallel) as captured:
        parallel.parallelize(model, inputs, payload['policy'], cc,
                             gen_savedir=out / 'code', reuse='override', load_module=False)
    if len(captured) != 1:
        raise RuntimeError(f'expected one real ModuleCodeGen, got {len(captured)}')
    mg = captured[0]
    with (out / 'capture.pkl').open('xb') as stream:
        pickle.dump(mg, stream, protocol=pickle.HIGHEST_PROTOCOL)
    # Verdict accepts an explicit World sidecar; no rank inference from filenames.
    world = dict(model_name='gpt', num_dp=cc.runtime_ngpus // cc.plan_ngpus,
                 num_tp=cc.plan_ngpus, num_pp=1, num_mb=1,
                 gbs=payload['batch_size'] * (cc.runtime_ngpus // cc.plan_ngpus),
                 num_layers=cfg.layers, num_heads=cfg.heads,
                 hidden_size=cfg.hidden, seqlen=cfg.seqlen)
    (out / 'capture.json').write_text(json.dumps(world, indent=2) + '\n')
    receipt = dict(model=asdict(cfg), compute=asdict(cc), policy=payload['policy'],
                   seed=payload['seed'], batch_size=payload['batch_size'],
                   model_source='genmodel.model.gpt.GPT',
                   nnscaler_source=nnscaler.__file__, nnscaler_version=nnscaler.__version__,
                   torch_version=torch.__version__,
                   gpu=torch.cuda.get_device_name(0), devices=list(mg.devices),
                   runtime_ngpus=mg.runtime_ndevs, cuda_forward_backward=True,
                   reference_loss=reference_loss, distributed_runtime_checked=False,
                   capture=str(out / 'capture.pkl'))
    (out / 'capture.receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt), flush=True)


if __name__ == '__main__':
    main()
