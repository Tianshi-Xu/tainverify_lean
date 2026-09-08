"""Explicit current-run input authority. Integer encoding is not Torch refinement."""
import json
from pathlib import Path
from types import SimpleNamespace


def load_handoff(root, snapshot, batch, receipt, reference_receipt):
    import torch
    from scripts.gpt_batch_runtime import read_run, validate_rank_domain, validate_rank_handoff, exact
    from trainverify.batch_source_authority import validate_batch_record
    root = Path(root)
    validate_batch_record(batch, snapshot, receipt, reference_receipt)
    world = receipt['compute']['runtime_ngpus']
    manifest = json.loads((root/'run.json').read_text())
    if type(manifest.get('world')) is not int:
        raise ValueError('strict run world integer required')
    run = read_run(SimpleNamespace(out=root), world)
    for suffix in ('json', 'pt'):
        if {p.name for p in root.glob(f'rank*.{suffix}')} != {f'rank{r}.{suffix}' for r in range(world)}:
            raise ValueError('exact rank artifact inventory required')
    rows = [json.loads((root/f'rank{rank}.json').read_text()) for rank in range(world)]
    validate_rank_domain(rows, world)
    pm = {}
    for rank, row in enumerate(rows):
        if row['rank'] != rank or type(row.get('inner_exit')) is not int or row['inner_exit'] != 0:
            raise ValueError('rank filename/inner exit mismatch')
        actual = torch.load(root/f'rank{rank}.pt', weights_only=True, map_location='cpu')
        validate_rank_handoff(row, actual, batch, snapshot, receipt, reference_receipt, run)
        pm[rank] = tuple(t.detach().clone() for t in actual['handoff_tensors']['post'][0])
    sm = torch.load(root/'reference.pt', weights_only=True, map_location='cpu')['inputs']
    if set(sm) != {'input_ids', 'position_ids'}:
        raise ValueError('global reference input name inventory')
    for name, tensor in sm.items():
        exact(tensor, torch.tensor(batch['global_inputs'][name], dtype=torch.int64))
    return sm, pm, run


def bind(world, sm, pm, raw_sm, raw_pm, snapshot, batch, receipt, reference, root):
    """Append feeds to the SAME authenticated worlds; never initialize loader tids."""
    import torch
    from Verdict.runtime_world import WorldDefinitions, render
    from Verdict.runtime_lineage import _Index, _training_readpoint
    from trainverify.batch_source_authority import _same_handoff_data
    current = render(sm, pm, raw_sm, raw_pm)
    if world.lean != current.lean or not _same_handoff_data(world.receipt, current.receipt):
        raise ValueError('input feed world differs from current source authority')
    globals_, posts, run = load_handoff(root, snapshot, batch, receipt, reference)
    lines = ['namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
             'set_option maxHeartbeats 500000', 'set_option maxRecDepth 4096', 'open SourceScopedEval']
    inventory = []; slots = {}; theorem_names = []
    def theorem(name, statement, proof):
        lines.extend([f'theorem {name} {statement} := {proof}', f'#print axioms {name}'])
        theorem_names.append(name)
    fields = ('world','runtime_rank','microbatch','source_tid','version')
    for label, view, raw in [('sm',sm,raw_sm), ('pm',pm,raw_pm)]:
        _Index(view, raw)
        loaders = [cell for cell in raw if str(cell.opname).split('.')[-1]=='DATALOADER']
        if (label=='sm' and len(loaders)!=1) or (label=='pm' and (len(loaders)!=len(posts) or {c.rank for c in loaders}!=set(posts))):
            raise ValueError('exact raw loader rank inventory required')
        loader_map = {cell.node:cell for cell in loaders}
        requests = []
        # Canonical re-render above authenticates this exact permutation.
        for i in world.receipt["execution_order"][label]["execution_to_source"]:
            n = view.nodes()[i]
            node = f'{label}Node_{i}'
            if n not in loader_map:
                requests.append(f'({node}, none)'); continue
            cell = loader_map[n]
            outs = view.node_outputs(n)
            if n.mb != 0 or view.node_inputs(n) or len(outs)!=2 or set(cell.kwargs) - {'__consts'}:
                raise ValueError('unsupported raw loader schema')
            refs = [dict(zip(fields, view.source_tensor(t))) for t in outs]
            if label=='pm':
                _training_readpoint(snapshot, cell)
                expected, = [row['refs'] for row in batch['rank_inputs'] if row['rank']==n.rank]
                if not _same_handoff_data(refs, expected): raise ValueError('raw postwait fullref/order mismatch')
            tensors = tuple(globals_[name] for name in ('input_ids','position_ids')) if label=='sm' else posts[n.rank]
            ports = []; records = []
            for port,(t,tensor,ir,name) in enumerate(zip(outs,tensors,cell._output_irs,('input_ids','position_ids'),strict=True)):
                if ir.parent.name != name or tensor.dtype != torch.int64 or tensor.ndim != 2 or tuple(tensor.shape)!=tuple(view.tensor_shape(t)):
                    raise ValueError('raw loader role/dtype/shape mismatch')
                values = tensor.reshape(-1).tolist()
                if any(type(v) is not int or v < 0 for v in values): raise ValueError('noninteger input encoding')
                tn = f'{node}_port{port}'
                shape = list(tensor.shape)
                lines.extend([f'def {tn}_values : List Int := {values}',
                    f'def {tn} : Tensor := {{shape := {shape}, val := fun i => (({tn}_values.getD i.val 0 : Int) : Scalar)}}'])
                theorem(tn+'_shape', f': {tn}.shape = {shape}', 'rfl')
                theorem(tn+'_length', f': {tn}_values.length = prodShape {tn}.shape', 'rfl')
                theorem(tn+'_encoding', f'(i : Fin (prodShape {tn}.shape)) : {tn}.val i = (({tn}_values.getD i.val 0 : Int) : Scalar)', 'rfl')
                ports.append(f'({t.tid}, {tn})')
                records.append(dict(port=port,tid=t.tid,ref=refs[port],shape=shape,values=values))
            feed = node+'_feed'
            lines.append(f'def {feed} : PortFeed := [{", ".join(ports)}]')
            theorem(node+'_contract', f': InputContract {node} {feed}', 'by decide')
            theorem(node+'_step', f'(s : Store) : checkedInputStep s {node} {feed} = some (storeSet s {feed})', f'checkedInputStep_valid s {node} {feed} {node}_contract')
            theorem(node+'_scoped_step', f'(s : Store) : stepWithInputs {label}Graph ({label}Scope {node}) ({label}Peers {node}) s {node} (some {feed}) = some (storeSet s {feed})', f'by\n  change checkedInputStep s {node} {feed} = _\n  exact {node}_step s')
            theorem(node+'_frame', f'(s : Store) (tid : Tid) (h : tid ∉ {node}.outs) : storeSet s {feed} tid = s tid', f'checkedInputStep_skip s (storeSet s {feed}) {node} {feed} tid h ({node}_step s)')
            for port,t in enumerate(outs):
                theorem(f'{node}_read{port}', f'(s : Store) : storeSet s {feed} {t.tid} = {node}_port{port}', f'checkedInputStep_value s (storeSet s {feed}) {node} {feed} {t.tid} {node}_port{port} (by simp [{feed}]) ({node}_step s)')
            requests.append(f'({node}, some {feed})')
            inventory.append(dict(world=label,index=i,node=list(n),ports=records,provenance='fresh-global-reference-inputs' if label=='sm' else 'fresh-postwait-consumer-inputs'))
        slots[label] = len(requests)
        lines.extend([f'def {label}InputRequests : List InputRequest := [', ',\n'.join(requests), ']',
            f'def {label}DenoteWithInputs (s : Store) : Option Store := SourceScopedEval.denoteWithInputs {label}Graph {label}Scope {label}Peers (some {label}InputRequests) s'])
    lines.extend(['end','end TrainVerify.Denote.RuntimeWorld',''])
    result = dict(world.receipt)
    result['input_feed'] = dict(run_id=run,loaders=inventory,slots=slots,source_validated=True,
        integer_encoding_emitted=True,kernel_value_proved=False,kernel_checks=theorem_names,
        whole_world_option_success=False,torch_refinement=False,historicalcapture_sample_association=False)
    return WorldDefinitions(world.lean+'\n'+'\n'.join(lines), result)
