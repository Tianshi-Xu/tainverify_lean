"""New CPU GPT batch witness; does not replay or certify a CUDA capture.

Run: CUDA_VISIBLE_DEVICES='' PYTHONDONTWRITEBYTECODE=1 python -m
scripts.gpt_batch_authority --receipt ... --reference-receipt ... --snapshot ...
--config ... --out ... . The config explicitly lists unit/rank/sample assignment.
"""
import argparse
import ast
from copy import deepcopy
import inspect
import json
from pathlib import Path
import sys
import textwrap

from trainverify.batch_source_authority import build_batch_record, validate_batch_record


def run_witness(receipt, reference_receipt, snapshot, config):
    """Execute all unit models and a concatenated global model with copied weights."""
    import torch
    from genmodel.model.gpt import Config, GPT
    torch.set_num_threads(1)
    torch.manual_seed(receipt['seed'])
    cfg = Config(**receipt['model'])
    model = GPT(cfg).cpu().double()
    source = inspect.getsource(GPT.forward)
    body = ast.parse(textwrap.dedent(source)).body[0].body
    expected = ast.parse('loss = torch.sum(logits)\nreturn loss').body
    if [ast.dump(x) for x in body[-2:]] != [ast.dump(x) for x in expected]:
        raise ValueError('unsupported: GPT objective is not the source sum(logits) return')
    # Integer coordinates are generated on CPU: this is a NEW 17-shift witness,
    # not recovery of the historical CUDA RNG stream or distributed inputs.
    base = torch.randint(cfg.num_embeddings, (receipt['batch_size'], cfg.seqlen))
    units = [dict(input_ids=(base + 17*u['unit']) % cfg.num_embeddings,
                  position_ids=torch.arange(cfg.seqlen).repeat(receipt['batch_size'], 1))
             for u in config['units']]
    global_inputs = {k: torch.cat([u[k] for u in units], dim=0) for k in units[0]}
    # The very tensors serialized here are passed below, without regeneration.
    record = build_batch_record(config, units, global_inputs, snapshot)
    validation = validate_batch_record(record, snapshot, receipt, reference_receipt)
    global_model = deepcopy(model)
    global_loss = global_model(**global_inputs)
    global_loss.backward()
    unit_losses, unit_grads = [], []
    for inputs in units:
        unit_model = deepcopy(model)
        loss = unit_model(**inputs)
        loss.backward()
        unit_losses.append(loss.detach())
        grads = {}
        for name, p in unit_model.named_parameters():
            if p.grad is None or not torch.isfinite(p.grad).all():
                raise ValueError(f'missing/nonfinite unit parameter gradient: {name}')
            grads[name] = p.grad.detach().clone()
        unit_grads.append(grads)
    global_grads, grad_sum, comparisons = {}, {}, {}
    atol, rtol = 1e-9, 1e-9
    def compare(a, b):
        torch.testing.assert_close(a, b, atol=atol, rtol=rtol, equal_nan=False)
        error = (a-b).abs()
        return dict(max_abs_error=error.max().item(),
                    max_normalized_error=(error/(atol+rtol*b.abs())).max().item())
    summed_loss = torch.stack(unit_losses).sum()
    loss_comparison = compare(global_loss.detach(), summed_loss)
    for name, p in global_model.named_parameters():
        if p.grad is None or not torch.isfinite(p.grad).all():
            raise ValueError(f'missing/nonfinite global parameter gradient: {name}')
        global_grads[name] = p.grad.detach().clone()
        grad_sum[name] = torch.stack([g[name] for g in unit_grads]).sum(0)
        comparisons[name] = compare(global_grads[name], grad_sum[name])
    reducers = [w['reducer'] for w in snapshot['writers'] if w['ref']['op'] == 'CROSS_DP_WRED']
    if any(r['reduce_op'] != 'sum' or r['zero'] != 0 for r in reducers):
        raise ValueError('unsupported: loss sum does not correspond to reducer source')
    validation['loss_reducer_correspondence_checked'] = bool(reducers) and snapshot['reducer_binding'] == 'complete'
    # Static source correspondence is not a proof of TP local derivative factors.
    validation['loss_reducer_correspondence_scope'] = 'source sum operator + CPU unit additivity only; TP/reducer kernel values unproved'
    result = dict(batch=record, validation=validation,
        capture_compatibility=dict(model_config_equal=True, global_batch_shape_equal=True,
            exact_sample_association=False,
            gap='capture receipts contain neither actual input tensors nor sample positions; no CUDA sample/weight association claimed'),
        loss_source=dict(path=inspect.getsourcefile(GPT), forward_source=source,
            objective='sum(logits)', normalizer=1, observed_global_loss=global_loss.item(),
            observed_unit_losses=[x.item() for x in unit_losses], observed_unit_sum=summed_loss.item()),
        numeric=dict(dtype='torch.float64', device='cpu', seed=receipt['seed'],
            weights='deepcopy of one initialized GPT', atol=atol, rtol=rtol,
            objective_close=True, objective=loss_comparison, all_parameter_grads_close=True,
            parameter_count=len(comparisons), parameters=comparisons,
            max_gradient_abs_error=max(v['max_abs_error'] for v in comparisons.values()),
            max_gradient_normalized_error=max(v['max_normalized_error'] for v in comparisons.values())),
        policy='source-only', proof_admissible=False)
    tensors = dict(initial_state=model.state_dict(), global_inputs=global_inputs, unit_inputs=units,
                   global_grads=global_grads, unit_grads=unit_grads, unit_grad_sum=grad_sum)
    return result, tensors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('receipt', 'reference-receipt', 'snapshot', 'config', 'out'):
        parser.add_argument('--'+name, type=Path, required=True)
    args = parser.parse_args()
    read = lambda p: json.loads(p.read_text())
    receipt, reference, snapshot, config = map(read, (args.receipt, args.reference_receipt, args.snapshot, args.config))
    result, tensors = run_witness(receipt, reference, snapshot, config)
    # Check the actual generated tuple unpacking, not equal tids or equal shapes.
    rank_bindings = []
    for item in result['batch']['rank_inputs']:
        source = snapshot['rank_sources'][str(item['rank'])]
        train_step = next(n for n in ast.parse(source).body if isinstance(n, ast.FunctionDef) and n.name == '_train_step')
        targets = [n.targets[0] for n in ast.walk(train_step) if isinstance(n, ast.Assign)
                   and isinstance(n.value, ast.Call) and isinstance(n.value.func, ast.Name) and n.value.func.id == 'next']
        names = [f"{name}_{ref['source_tid']}" for name, ref in zip(('input_ids','position_ids'), item['refs'], strict=True)]
        if len(targets) != 1 or not isinstance(targets[0], ast.Tuple) or [n.id for n in targets[0].elts] != names:
            raise ValueError('unsupported: generated dataloader tuple order/name mismatch')
        rank_bindings.append(dict(rank=item['rank'], ordered_generated_input_names=names))
    result['generated_input_bindings'] = rank_bindings
    result['sources'] = {k: str(getattr(args, k).resolve()) for k in ('receipt', 'reference_receipt', 'snapshot', 'config')}
    result['capture_receipt'] = receipt
    result['reference_capture_receipt'] = reference
    result['command'] = [sys.executable, '-m', 'scripts.gpt_batch_authority', *sys.argv[1:]]
    args.out.mkdir(parents=True, exist_ok=False)
    import torch
    torch.save(tensors, args.out/'tensors.pt')
    # Independently read back actual serialized input tensors and the JSON record.
    saved = torch.load(args.out/'tensors.pt', weights_only=True, map_location='cpu')
    for name in result['batch']['global_inputs']:
        if saved['global_inputs'][name].tolist() != result['batch']['global_inputs'][name]:
            raise ValueError('tensor readback mismatch')
    result['inner_exit'] = 0
    result['tensor_artifact'] = str((args.out/'tensors.pt').resolve())
    (args.out/'result.json').write_text(json.dumps(result, indent=2, allow_nan=False)+'\n')
    reread = read(args.out/'result.json')
    validate_batch_record(reread['batch'], snapshot, receipt, reference)
    if reread != result:
        raise ValueError('JSON readback mismatch')
    print(json.dumps(dict(result=str(args.out/'result.json'), inner_exit=0,
        json_readback=True, tensor_readback=True, numeric=result['numeric']), allow_nan=False))


if __name__ == '__main__':
    main()
