"""External scalar seed -> mathematical Store boundary (not Torch refinement).

`map_requests` is a consistency check, not authentication of caller dictionaries.
The production loader must independently rebuild source requests and validate the
actual event/PT against a caller-selected manifest before invoking it.
"""
from trainverify.batch_source_authority import _same_handoff_data as same
from trainverify.runtime_source_authority import tensor_export_id, writer_export_id

FIELDS = ('world', 'runtime_rank', 'microbatch', 'source_tid', 'version')


def map_requests(view, raw, requests):
    """Join complete original BW_sum requests to bijective full-reference IDs.

    Check ALL graph writers, including future writers, not just prefix writers.
    No hard-coded rank count, source tensor identifier or lowered tensor ID.
    """
    def ref(t):
        value = dict(zip(FIELDS, t, strict=True))
        tensor_export_id(value)
        return value

    tensors = list(view.tensors())
    refs = {}; ids = set()
    for t in tensors:
        original = ref(view.source_tensor(t))
        key = tensor_export_id(original)
        if type(t.tid) is not int or t.tid < 0 or t.tid in ids or key in refs:
            raise ValueError('non-bijective lowered full-reference inventory')
        refs[key] = t; ids.add(t.tid)
    cells = {tuple(c.node): c for c in raw}
    nodes = list(view.nodes())
    if len(cells) != len(raw) or len(nodes) != len(cells) or set(map(tuple,nodes)) != set(cells):
        raise ValueError('complete raw node inventory mismatch')
    written = set(); consumers = []
    for n in nodes:
        cell = cells[tuple(n)]
        op = str(cell.opname).split('.')[-1]
        if str(view.node_opname(n)).split('.')[-1] != op:
            raise ValueError('raw opcode mismatch')
        for method, original in [('node_inputs',cell.inputs),('node_outputs',cell.outputs)]:
            actual = [ref(view.source_tensor(t)) for t in getattr(view,method)(n)]
            expected = [ref(t) for t in original]
            if not same(actual,expected):
                raise ValueError('raw full-reference port order mismatch')
        written.update(tensor_export_id(ref(t)) for t in cell.outputs)
        if op == 'BW_sum': consumers.append(cell)
    if not requests or len(requests) != len(consumers):
        raise ValueError('complete BW_sum seed inventory required')
    remaining = list(consumers); seen = set(); rows = []
    for request in requests:
        seed, x, bw = request['seed'], request['x'], request['bw_writer']
        key = tensor_export_id(seed); tensor_export_id(x); writer_export_id(bw)
        if key in seen or key in written or key not in refs:
            raise ValueError('duplicate, graph-written or absent seed')
        seen.add(key)
        candidates = [c for c in remaining if same(
            dict(world=c.node[0], runtime_rank=c.node.rank, microbatch=c.node.mb,
                 source_cid=c.node.cid, call_instance=0, op='BW_sum', origin='nnscaler'), bw)]
        if len(candidates) != 1:
            raise ValueError('BW_sum source writer identity mismatch')
        cell, = candidates; remaining.remove(cell)
        if (not same([ref(t) for t in cell.inputs], [seed,x]) or len(cell.outputs)!=1
                or not any(same(cell.kwargs, kw) for kw in ({}, {"__consts": []}))
                or not same(dict(view.node_kwargs(cell.node)), cell.kwargs)
                or not cell._input_irs[0].is_grad() or cell._input_irs[0].is_param()
                or list(view.tensor_shape(refs[key])) != [1]):
            raise ValueError('full sum seed role/shape/arity/params mismatch')
        rows.append(dict(tid=refs[key].tid, ref=dict(seed), shape=[1], value=1,
                         consumer=list(cell.node)))
    if remaining:
        raise ValueError('unbound BW_sum consumer')
    return rows


def load_bundle(config, sm, pm, raw_sm, raw_pm, handoff_root):
    """Fresh authority only; paths are explicit caller input, never event input.

    This pure function stores no previous attachment. A failed call returns no
    authority. Callers must not reuse a previous successful result after failure.
    """
    import hashlib
    import json
    import pickle
    from copy import deepcopy
    from pathlib import Path
    import torch
    from verdict.graph import World, WType
    from nnscaler_backend.build_graph import _prepare_rank_cells, _fuse_collective_inputs
    from nnscaler_backend.runtime_source_authority import export_expanded_cells
    from trainverify.runtime_seed_authority import load_seed_capture, validate_seed_event
    if type(config) is not dict or set(config) != {'sm_capture', 'pm_capture', 'sm_run', 'pm_run'}:
        raise ValueError('explicit SM/PM capture and run directories required')
    if Path(config['pm_run']).resolve() != Path(handoff_root).resolve():
        raise ValueError('seed run must equal current input handoff run')
    inventories = {}; runs = {}; pins = {}; actuals = {}
    for label, world_type, view, raw in [('sm','s',sm,raw_sm), ('pm','p',pm,raw_pm)]:
        root, run = Path(config[label+'_capture']), Path(config[label+'_run'])
        authority, _ = load_seed_capture(root, world_type)
        # Reconstruct the entire raw graph independently, not seed metadata or
        # a source-count equality. Preparation may mutate the fresh codegen.
        mg = pickle.loads((root/'capture.pkl').read_bytes())
        world = World(wtype=WType(world_type), plan_ndevs=len(mg.devices),
            runtime_ndevs=mg.runtime_ndevs, **json.loads((root/'capture.json').read_text()))
        cells = [c for rank in range(world.runtime_ndevs) for c in _prepare_rank_cells(world,deepcopy(mg),rank)]
        canonical, _ = _fuse_collective_inputs(cells)
        if not same(export_expanded_cells(world, canonical), export_expanded_cells(world, raw)):
            raise ValueError('complete original capture/raw graph mismatch')
        manifest = json.loads((run/'run.json').read_text())
        if type(manifest.get('world')) is not int or manifest['world'] != world.runtime_ndevs:
            raise ValueError('capture/run world mismatch')
        expected_pt = {f'rank{rank}.pt' for rank in range(world.runtime_ndevs)}
        if {p.name for p in run.glob('rank*.pt')} != expected_pt:
            raise ValueError('complete rank PT inventory required')
        pattern = 'event*.json' if label=='sm' else 'seed-event*.json'
        names = {'event.json'} if label=='sm' else {f'seed-event{r}.json' for r in range(world.runtime_ndevs)}
        if {p.name for p in run.glob(pattern)} != names:
            raise ValueError('complete seed event inventory required')
        files = [run/'run.json']
        actuals[label] = []
        for rank in range(world.runtime_ndevs):
            event_file = run/('event.json' if label=='sm' else f'seed-event{rank}.json')
            pt_file = run/f'rank{rank}.pt'
            actual = torch.load(pt_file, weights_only=True, map_location='cpu')
            validate_seed_event(authority, json.loads(event_file.read_text()), actual, manifest, rank)
            actuals[label].append(actual); files += [event_file, pt_file]
        inventories[label] = map_requests(view, raw, authority['requests'])
        runs[label] = manifest['run_id']; pins.update(authority['pins'])
        pins.update({str(p.resolve()):hashlib.sha256(p.read_bytes()).hexdigest() for p in files})
    from scripts.gpt_batch_runtime import exact
    reference_file = Path(config['pm_run'])/'reference.pt'
    reference = torch.load(reference_file, weights_only=True, map_location='cpu')
    for name in ('input_ids', 'position_ids'):
        exact(actuals['sm'][0]['inputs'][name], reference['inputs'][name])
    pins[str(reference_file.resolve())] = hashlib.sha256(reference_file.read_bytes()).hexdigest()
    tids = [row['tid'] for rows in inventories.values() for row in rows]
    if len(set(tids)) != len(tids):
        raise ValueError('cross-world seed ID collision')
    return dict(inventories=inventories, runs=runs, pins=pins,
                seed_input_adapter_emitted=False, kernel_value_proved=False,
                proof_admissible=False, torch_refinement=False)


def render_adapter(inventories, *, structured=False):
    """Render a mathematical boundary; source authentication is load_bundle's job.

    The returned declarations belong before prefix proofs, not in a Graph node
    list. No existing unseeded entry definition or initial-shape contract changes.
    """
    lines = [] if structured else ['namespace TrainVerify.Denote.RuntimeWorld', 'noncomputable section',
             'open SourceScopedEval', 'set_option maxHeartbeats 500000']
    names = []
    def theorem(name, statement, proof):
        names.append(name)
        lines.extend([f'theorem {name} {statement} := {proof}', f'#print axioms {name}'])
    lines.extend(['def unitSeed : Tensor := Tensor.mkShape [1] (fun _ => 1)',
                  'def applySeeds (s : Store) (seeds : List (Tid × Tensor)) : Store := storeSet s seeds'])
    theorem('unitSeed_shape', ': unitSeed.shape = [1]', 'rfl')
    theorem('unitSeed_value', ': valAt unitSeed 0 = 1', 'rfl')
    theorem('unitSeed_bw_sum', '(x : Tensor) : bw_sum unitSeed x = Tensor.mkShape x.shape (fun _ => 1)', 'rfl')
    theorem('applySeeds_value', '(s : Store) (seeds : List (Tid × Tensor)) (tid : Tid) (v : Tensor) '
        '(hu : (seeds.map Prod.fst).Nodup) (hm : (tid, v) ∈ seeds) : applySeeds s seeds tid = v',
        'storeSet_feed_value s seeds tid v hu hm')
    theorem('applySeeds_frame', '(s : Store) (seeds : List (Tid × Tensor)) (tid : Tid) '
        '(h : tid ∉ seeds.map Prod.fst) : applySeeds s seeds tid = s tid',
        'storeSet_eq_of_not_mem_fst s seeds tid h')
    theorem('applySeeds_parameters', '(s : Store) (seeds : List (Tid × Tensor)) (parameters : List Tid) '
        '(hd : ∀ tid ∈ parameters, tid ∉ seeds.map Prod.fst) (tid : Tid) (hp : tid ∈ parameters) '
        ': applySeeds s seeds tid = s tid', 'applySeeds_frame s seeds tid (hd tid hp)')
    for label in ('sm', 'pm'):
        rows = inventories[label]; ids = [row['tid'] for row in rows]
        if not ids or any(type(t) is not int or t < 0 for t in ids) or len(ids)!=len(set(ids)):
            raise ValueError('nonempty unique strict seed IDs required')
        seeds = label+'ExternalSeeds'; init = label+'InitialWithSeeds'
        lines.extend([f'def {seeds} : List (Tid × Tensor) := ['+', '.join(f'({tid}, unitSeed)' for tid in ids)+']',
                      f'def {init} (s : Store) : Store := applySeeds s {seeds}',
                      f'def {label}SeededDenoteWithInputs (s : Store) : Option Store := {label}DenoteWithInputs ({init} s)'])
        theorem(seeds+'_coverage', f': {seeds}.map Prod.fst = {ids}', 'rfl')
        theorem(seeds+'_unique', f': ({seeds}.map Prod.fst).Nodup', 'by decide')
        theorem(init+'_frame', f'(s : Store) (tid : Tid) (h : tid ∉ {seeds}.map Prod.fst) : {init} s tid = s tid',
                f'applySeeds_frame s {seeds} tid h')
        for i, tid in enumerate(ids):
            theorem(f'{init}_seed_{i}', f'(s : Store) : {init} s {tid} = unitSeed',
                    f'applySeeds_value s {seeds} {tid} unitSeed {seeds}_unique (by simp [{seeds}])')
    if structured:
        from Verdict.runtime_prefix import ProofGroup
        return [ProofGroup('\n'.join(lines), 8 + len(names), ())]
    lines.extend(['end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return '\n'.join(lines)
