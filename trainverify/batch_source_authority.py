"""Observed, ordered global-batch inputs. Never a proof-admission authority.

Canonical producers may execute a declared replication group's inputs once.
Rank refs identify intended consumers, NOT evidence that captured CUDA ranks
consumed these new CPU values. The original captures contain no sample payload.
"""
from copy import deepcopy
from .runtime_source_authority import validate_snapshot


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
