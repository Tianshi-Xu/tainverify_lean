"""Observed, ordered global-batch inputs. Never a proof-admission authority.

Canonical producers may execute a declared replication group's inputs once.
Rank refs identify intended consumers, NOT evidence that captured CUDA ranks
consumed these new CPU values. The original captures contain no sample payload.
"""
from copy import deepcopy
from .runtime_source_authority import validate_snapshot


def handoff_binding(snapshot, record, rank, expected_run):
    """Rebind the first consumer from independent prepared IR and schedule source."""
    import ast
    import inspect
    import textwrap
    from .runtime_source_authority import _dataloader_training_point, writer_export_id
    from nnscaler.runtime.executor import Executor, AsyncCommHandler
    validate_snapshot(snapshot)
    try:
        if type(rank) is not int or not isinstance(expected_run, str) or not expected_run:
            raise ValueError('missing fresh run/rank identity')
        producers = [p for p in snapshot['adapter_source']
                     if p['ref']['op'] == 'DATALOADER' and p['ref']['runtime_rank'] == rank]
        if len(producers) != 1:
            raise ValueError('missing/ambiguous source dataloader')
        producer, = producers
        evidence = producer['generated_dataloader']
        call = evidence['training_calls'][0]
        if call['ordinal'] != 1 or call['input_refs'] != producer['outputs']:
            raise ValueError('unsupported first consumer input ports')
        runtime = {k: textwrap.dedent(inspect.getsource(v)) for k, v in
                   [('fexecute', Executor.fexecute), ('sync_tensors', Executor.sync_tensors),
                    ('wait', type(AsyncCommHandler()).wait)]}
        for key, source in runtime.items():
            if ast.dump(ast.parse(source)) != ast.dump(ast.parse(evidence['runtime'][key])):
                raise ValueError('installed executor source differs from snapshot')
        points = [_dataloader_training_point(snapshot, producer, call['method'], name,
                  dict(ref=ref, writer=writer_export_id(producer['ref'])), {}, set())
                  for name, ref in zip(call['parameters'], producer['outputs'], strict=True)]
        group, = [g for g in record['groups'] if rank in g['ranks']]
        return dict(run_id=expected_run, rank=rank, train_step=1,
            writer=deepcopy(producer['ref']), writer_export_id=writer_export_id(producer['ref']),
            refs=deepcopy(producer['outputs']), next_ordinal=evidence['ordinal'],
            consumer=deepcopy(call), parameter_indices=[p['parameter_index'] for p in points],
            unit=group['unit'], positions=deepcopy(group['positions']),
            samples=[deepcopy(s) for s in record['samples'] if s['unit'] == group['unit']],
            runtime=runtime)
    except (KeyError, TypeError, IndexError, AttributeError) as exc:
        raise ValueError(f'missing source-authenticated handoff input: {exc}') from exc


def _same_handoff_data(actual, expected):
    """Preserve JSON field types; bool/int/float equality is not identity binding."""
    if type(actual) is not type(expected):
        return False
    if isinstance(expected, dict):
        return actual.keys() == expected.keys() and all(_same_handoff_data(actual[k], v) for k, v in expected.items())
    if isinstance(expected, (list, tuple)):
        return len(actual) == len(expected) and all(_same_handoff_data(a, b) for a, b in zip(actual, expected))
    return actual == expected


def validate_input_handoff(events, payload, record, snapshot, receipt,
                           reference_receipt, expected_run, rank):
    """Validate measured pre/post tensors, not saved success flags or next-only data."""
    import torch
    result = validate_batch_record(record, snapshot, receipt, reference_receipt)
    binding = handoff_binding(snapshot, record, rank, expected_run)
    try:
        if len(events) != 2 or set(payload) != {'pre', 'post'}:
            raise ValueError('handoff pre/post cardinality')
        group, = [g for g in record['groups'] if g['unit'] == binding['unit']]
        for ordinal, stage in enumerate(('pre', 'post'), 1):
            event = events[ordinal - 1]
            metadata = {k: v for k, v in event.items() if k not in ('values', 'dtypes', 'shapes')}
            expected = dict(binding, stage=stage, event_ordinal=ordinal)
            if not _same_handoff_data(metadata, expected):  # independent metadata association guard
                raise ValueError('handoff event metadata association mismatch')
            if len(payload[stage]) != 1 or len(payload[stage][0]) != 2:
                raise ValueError('handoff tensor cardinality')
            tensors = payload[stage][0]
            if (not _same_handoff_data(event['values'], [t.tolist() for t in tensors]) or
                    not _same_handoff_data(event['dtypes'], [str(t.dtype) for t in tensors]) or
                    not _same_handoff_data(event['shapes'], [list(t.shape) for t in tensors])):
                raise ValueError('handoff JSON/tensor inconsistency')
            for name, tensor in zip(('input_ids', 'position_ids'), tensors, strict=True):
                canonical = torch.tensor(group['inputs'][name], dtype=torch.int64)
                if tensor.dtype != canonical.dtype or tensor.shape != canonical.shape:
                    raise ValueError(f'{stage} tensor dtype/shape mismatch')
                if not torch.equal(tensor.cpu(), canonical):  # canonical post comparison guard
                    raise ValueError(f'{stage} tensor value differs from canonical batch')
    except (KeyError, TypeError, IndexError, AttributeError) as exc:
        raise ValueError(f'malformed handoff: {exc}') from exc
    return dict(result, new_run_segment_input_association=True,
                historicalcapture_sample_association=False)



def _rank_inputs(snapshot):
    return {w['ref']['runtime_rank']: deepcopy(w['outputs'])
            for w in snapshot['writers'] if w['ref']['op'] == 'DATALOADER'}


def build_batch_record(config, unit_inputs, global_inputs, snapshot):
    """Serialize tensors observed at the producer/model call boundary, not tids."""
    def payload(inputs):
        return {name: value.detach().cpu().tolist() if hasattr(value, 'detach')
                else deepcopy(value) for name, value in inputs.items()}
    groups = [dict(unit=u['unit'], ranks=deepcopy(u['ranks']),
                   positions=deepcopy(u['positions']), inputs=payload(inputs))
              for u, inputs in zip(config['units'], unit_inputs, strict=True)]
    return dict(format='trainverify.batch-source.v1', scope='source-only',
        proof_admissible=False, evidence_kind='new-cpu-canonical-producer',
        config=deepcopy(config), groups=groups, global_inputs=payload(global_inputs),
        samples=[dict(global_position=p, unit=u['unit'], local_position=i, microbatch=0)
                 for u in config['units'] for i, p in enumerate(u['positions'])],
        rank_inputs=[dict(rank=r, unit=u['unit'], microbatch=0,
                         refs=_rank_inputs(snapshot)[r])
                     for u in config['units'] for r in u['ranks']])


def validate_batch_record(record, snapshot, receipt, reference_receipt):
    """Independently reconstruct ordered global inputs from observed unit rows."""
    validate_snapshot(snapshot)
    try:
        c = record['config']
        if (record['format'] != 'trainverify.batch-source.v1' or
                record['scope'] != 'source-only' or record['proof_admissible'] is not False or
                record['evidence_kind'] != 'new-cpu-canonical-producer'):
            raise ValueError('not a source-only CPU observation')
        if (any(type(c[k]) is not int or c[k] != 1 for k in ('num_pp', 'num_mb')) or
                type(c['normalizer']) not in (int, float) or c['normalizer'] != 1 or
                c['objective'] != 'sum'):
            raise ValueError('unsupported: only PP1 MB1 sum normalizer exactly 1')
        plan = receipt['compute']['plan_ngpus']
        runtime = receipt['compute']['runtime_ngpus']
        batch = receipt['batch_size']
        if any(type(n) is not int or n <= 0 for n in (plan, runtime, batch, c['gbs'])):
            raise ValueError('invalid batch/topology integer')
        if runtime % plan or runtime < plan:
            raise ValueError('unsupported: nonuniform scale units')
        if (snapshot['source']['plan_ndevs'] != plan or
                snapshot['source']['runtime_ndevs'] != runtime or
                snapshot['runtime_ndevs'] != runtime):
            raise ValueError('capture topology mismatch')
        n = runtime // plan
        if c['gbs'] != n * batch:
            raise ValueError('global batch differs from observed unit batch sizes')
        if reference_receipt['model'] != receipt['model'] or reference_receipt['batch_size'] != c['gbs']:
            raise ValueError('global reference model/batch mismatch')
        expected_units = [dict(unit=u, ranks=list(range(u*plan, (u+1)*plan)),
                               positions=list(range(u*batch, (u+1)*batch))) for u in range(n)]
        if c['units'] != expected_units:
            raise ValueError('unsupported or inconsistent ordered uniform assignment')
        loaders = [w for w in snapshot['writers'] if w['ref']['op'] == 'DATALOADER']
        if (len(loaders) != runtime or {w['ref']['runtime_rank'] for w in loaders} != set(range(runtime)) or
                any(w['ref']['microbatch'] != 0 or len(w['outputs']) != 2 for w in loaders)):
            raise ValueError('unsupported: dataloader inventory/microbatch')
        for tensor in snapshot['tensors']:
            if 'placement' in tensor:
                rank = tensor['ref']['runtime_rank']
                p = tensor['placement']
                if rank >= 0 and (p['scale_unit'], p['plan_rank']) != divmod(rank, plan):
                    raise ValueError('placement differs from declared rank replication groups')
        expected_ranks = [dict(rank=r, unit=u['unit'], microbatch=0, refs=_rank_inputs(snapshot)[r])
                          for u in expected_units for r in u['ranks']]
        if record['rank_inputs'] != expected_ranks:
            raise ValueError('rank input source reference/order mismatch')
        expected_samples = [dict(global_position=p, unit=u['unit'], local_position=i, microbatch=0)
                            for u in expected_units for i, p in enumerate(u['positions'])]
        if record['samples'] != expected_samples or len(record['groups']) != n:
            raise ValueError('missing/duplicate/unordered sample positions')
        reconstructed = {name: [None] * c['gbs'] for name in ('input_ids', 'position_ids')}
        for expected, group in zip(expected_units, record['groups'], strict=True):
            if {k: group[k] for k in expected} != expected:
                raise ValueError('unit input mapping/order mismatch')
            if set(group['inputs']) != set(reconstructed):
                raise ValueError('missing input payload')
            for name in reconstructed:
                rows = group['inputs'][name]
                bound = receipt['model']['num_embeddings'] if name == 'input_ids' else receipt['model']['seqlen']
                if (len(rows) != batch or any(len(row) != receipt['model']['seqlen'] or
                        any(type(v) is not int or not 0 <= v < bound for v in row) for row in rows)):
                    raise ValueError('invalid observed tensor shape/coordinates')
                for local, position in enumerate(group['positions']):
                    if reconstructed[name][position] is not None:
                        raise ValueError('duplicate sample position')
                    reconstructed[name][position] = rows[local]
        if reconstructed != record['global_inputs']:
            raise ValueError('global reference coordinate mismatch')
    except (KeyError, TypeError, IndexError, AttributeError) as exc:
        raise ValueError(f'malformed batch source: {exc}') from exc
    return dict(scope='source-only', batch_input_mapping_verified=True,
        loss_reducer_correspondence_checked=False, kernel_value_proved=False,
        proof_admissible=False, capture_sample_association_verified=False)
