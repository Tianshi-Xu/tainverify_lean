"""Independent score AA(1,3) raw census, version 1.

Source port of backward-score-exchange-acceptance/check_raw.py. This narrow
stage diagnostic inventories both divisions without implementing them. Its
synthetic integer layout oracle is NOT Torch refinement or a kernel proof.
The pure checker never opens paths from world_binding. Trusted-local capture
loading is a separate, byte-authenticated operation (pickle is not a sandbox).
"""
import json
import math

from trainverify.artifact_tools import require

REPORT_VERSION = 1


def _wire(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False)


def _one(values):
    values = list(values)
    require(len(values) == 1, 'expected exactly one raw source match')
    return values[0]


def _consumers(cells, ref):
    return [c for c in cells if not c.opname.name.startswith('BW_') and tuple(ref) in c.inputs]


def _producer(cells, ref):
    cell = _one(c for c in cells if tuple(ref) in c.outputs)
    return cell, cell._output_irs[cell.outputs.index(tuple(ref))]


def _port(port, ref, ir, cells):
    cell, _ = _producer(cells, ref)
    require(port['endpoint']['ref'] == list(ref) and port['endpoint']['writer'] == list(cell.node), 'source port endpoint/writer')
    require(port['endpoint']['shape'] == list(ir.shape) and port['parent_name'] == ir.parent.name, 'source port shape/parent name')
    require(port['parent_shape'] == list(ir.parent.shape) and port['bounds'] == [list(b) for b in ir.indmap], 'source port parent shape/bounds')
    require(port['value_part'] == list(ir.valmap) == [0, 1], 'source port value partition')
    require(type(ir.tid) is int and ir.tid == ref[3], 'source port tensor identity')


def _ordinary_descriptor(step, cell, cells):
    require(step['node'] == list(cell.node) and step['op'] == cell.opname.name, 'ordinary source node/op')
    for field, irs in [('inputs', cell._input_irs), ('outputs', cell._output_irs)]:
        require([p['endpoint']['ref'] for p in step[field]] == [list(r) for r in getattr(cell, field)], 'ordinary ordered source ports')
        for p, r, ir in zip(step[field], getattr(cell, field), irs, strict=True):
            _port(p, r, ir, cells)



def load_worlds(config, pins, sm_capture, pm_capture):
    """Load trusted local captures after authenticating all four exact payloads.

    Directory arguments and pin keys use original logical absolute names;
    Configuration resolves each file, including file-specific relocations.
    Bytes are retained through authentication and deserialized from memory,
    so a later filesystem replacement cannot substitute an unchecked pickle.
    No fixture import, rank-cell cache, or capture write is involved.
    """
    import hashlib
    import pickle
    from trainverify.artifact_tools import absolute, digest_value, strict_json

    require(isinstance(pins, dict), 'capture pins must be a mapping')
    payloads = []
    for directory in (sm_capture, pm_capture):
        logical = absolute(str(directory))
        pair = []
        for filename in ('capture.pkl', 'capture.json'):
            name = str(logical / filename)
            require(name in pins, 'missing capture pin: ' + name)
            expected = digest_value(pins[name])
            data = config.resolve(name).read_bytes()
            require(hashlib.sha256(data).hexdigest() == expected, 'capture hash mismatch: ' + name)
            pair.append(data)
        payloads.append(pair)
    metadata = [strict_json(pair[1]) for pair in payloads]
    # The module CLI must not depend on a historical PYTHONPATH export.
    import sys
    from pathlib import Path
    verdict_root = str(Path(__file__).resolve().parents[1] / 'Verdict')
    if verdict_root not in sys.path:
        sys.path.insert(0, verdict_root)
    from nnscaler_backend.build_graph import _prepare_rank_cells
    from verdict.graph import World, WType

    worlds = []
    for label, pair, meta in zip(('s', 'p'), payloads, metadata, strict=True):
        mg = pickle.loads(pair[0])
        world = World(wtype=WType(label), plan_ndevs=len(mg.devices),
                      runtime_ndevs=mg.runtime_ndevs, **meta)
        worlds.append([cell for rank in range(world.runtime_ndevs)
                       for cell in _prepare_rank_cells(world, mg, rank)])
    return tuple(worlds)


def check_raw(sm_cells, pm_cells, old_detail, new_detail, world_binding):
    """Check the original stage semantics against already-loaded raw graphs.

    Returns a versioned diagnostic report. Capture pins are reported, not
    authenticated here; use load_worlds to authenticate before deserialization.
    No graph, detail, receipt, cache, or capture is modified.
    """
    import torch
    from trainverify.runtime_source_authority import writer_export_id

    sm, pm = sm_cells, pm_cells
    old, new, world = old_detail, new_detail, world_binding
    frontier, retained, deferred, units = [], [], [], []
    reads, consumed, geometry = {}, [], []
    for i, before in enumerate(old['frontier_units']):
        gc, gir = _producer(sm, before['sm_output_ref'])
        ps = [_producer(pm, r) for r in before['pm_output_refs']]
        if gc.opname.name == 'FW_multiref':
            _ordinary_descriptor(before['source_step'], gc, sm)
            for s, (c, ir) in zip(before['local_steps'], ps, strict=True):
                _ordinary_descriptor(s, c, pm)
            frontier.append(before)
            retained.append(before)
            continue
        if gc.opname.name != 'FW_matmul':
            require(before['layout'] == 'replicated_within_dp' and before['gather_axis'] is None, 'deferred replica layout')
            require(list(gir.shape) == before['global_shape'], 'deferred global shape')
            require(all(c.opname.name == 'AllGatherPrim' and list(ir.shape) == before['local_shape'] for c, ir in ps), 'deferred replica source/shape')
            d = _one(r for r in new['deferred_units'] if r['frontier_index'] == i)
            require(_wire(d['source_boundary']) == _wire(before) and d['unit'] == before['unit'], 'deferred source boundary')
            require(d['reason'] == 'unavailable-or-unsupported-original-consumer' and d['value_proved'] is False, 'deferred scope')
            frontier.append(before)
            deferred.append(d)
            continue
        row = _one(r for r in new['units'] if r['frontier_index'] == i)
        require(_wire(row['input_frontier']) == _wire(before), 'input frontier')
        require(_wire(row['source_step']) == _wire(before['source_step']), 'source step history')
        _ordinary_descriptor(row['source_step'], gc, sm)
        require(row['sm_output_ref'] == before['sm_output_ref'] and row['sm_output_tid'] == before['sm_output_tid'], 'retained SM endpoint')
        require(row['predecessor'] == row['predecessor_facts'] == before['facts_theorem'], 'predecessor facts')
        refs, ranks = before['pm_output_refs'], before['ranks']
        T, D, u = len(ranks), before['dimensions']['D'], before['unit']
        cells = [_one(_consumers(pm, ref)) for ref in refs]
        require([c.rank for c in cells] == ranks and len({tuple(c.node) for c in cells}) == T, 'ordered rank source cover')
        require(row['ranks'] == ranks and row['positions'] == before['positions'], 'ordered ranks/positions')
        require(row['input_refs'] == refs and row['source_output_slot'] == before['source_output_slot'] == row['slot'] == 0, 'input refs/source slot')
        require(row['pm_output_slots'] == [0] * T and row['axes'] == [1, 3], 'output slots/AA axes')
        require(row['layout'] == 'sharded' and row['input_gather_axis'] == 1 and row['gather_axis'] == row['output_gather_axis'] == row['split_axis'] == 3, 'AA layout')
        actual_outputs = []
        for j, (c, s) in enumerate(zip(cells, row['local_steps'], strict=True)):
            require(c.opname.name == s['op'] == 'AllToAllPrim' and s['node'] == list(c.node), 'AA source node/op')
            require(c.ir.signature == 'nnscaler.runtime.adapter.nn.alltoall_alltoall', 'AA source signature')
            require(c.kwargs == dict(idim=1, odim=3, ranks=ranks, __consts=[]), 'AA source kwargs')
            require(c.inputs in ([tuple(refs[j])], [tuple(r) for r in refs]), 'AA original local/all-peer inputs')
            require([p['endpoint']['ref'] for p in s['inputs']] == refs, 'AA ordered peer ports')
            require(s['ranks'] == ranks and s['local_index'] == j and (s['gather_axis'], s['split_axis']) == (1, 3), 'AA ordered receiver/axes')
            for p, ref, (_, ir) in zip(s['inputs'], refs, ps, strict=True):
                _port(p, ref, ir, pm)
            require([p['endpoint']['ref'] for p in s['outputs']] == [list(r) for r in c.outputs], 'AA output refs')
            _port(s['outputs'][0], c.outputs[0], c._output_irs[0], pm)
            own = ps[j][1]
            require(c._input_irs[0].parent.tid == own.parent.tid == c._output_irs[0].parent.tid == gir.parent.tid, 'AA full parent identity')
            read = _one(r for r in new['reads'] if r['node'] == list(c.node))
            require(_wire(read['source_step']) == _wire(s) and read['source_signature'] == c.ir.signature, 'read source descriptor/signature')
            require(read['input_refs'] == refs and read['input_metadata'] == 'local-only', 'read input metadata')
            require(read['producer_metadata'] == 'all-peers' and read['source_writer'] == writer_export_id(read['writer_ref']), 'read producer metadata/writer')
            ref = read['writer_ref']
            require([ref[k] for k in ('world', 'runtime_rank', 'microbatch', 'source_cid')] == list(c.node[:4]), 'read writer identity')
            order = world['execution_order']['pm']
            require(order['source_to_execution'][read['source_index']] == read['execution_index'], 'read execution index')
            require(read['operand_nonwrite_source_indices'] == order['execution_to_source'][read['execution_index']:], 'BW suffix inventory')
            require(not any(tuple(r) in bw.outputs for r in refs for bw in pm if bw.opname.name.startswith('BW_')), 'BW operand nonwrite')
            reads[tuple(c.node)] = read
            actual_outputs.append(c._output_irs[0])
        shape = list(actual_outputs[0].shape)
        require(row['global_shape'] == list(gir.shape) and row['local_shape'] == shape, 'full output shapes')
        require(all(list(ir.shape) == shape for ir in actual_outputs), 'every local output shape')
        require(row['dimensions'] == dict(D=D, T=T, **dict(zip(('B', 'S', 'H', 'C'), shape))), 'full dimensions')
        require(row['pm_output_refs'] == [list(c.outputs[0]) for c in cells], 'ordered PM output refs')
        require(row['input_shape'] == list(ps[0][1].shape), 'AA input shape')
        global_value = torch.arange(math.prod(gir.shape), dtype=torch.int64).reshape(gir.shape) * 13 + 7
        chunk = global_value.chunk(D, dim=0)[u]
        local_inputs = [chunk[tuple(slice(lo, hi) for lo, hi in ir.indmap)] for _, ir in ps]
        outputs = [torch.cat([x.chunk(T, dim=3)[j] for x in local_inputs], dim=1) for j in range(T)]
        require(all(torch.equal(y, chunk[tuple(slice(lo, hi) for lo, hi in ir.indmap)]) for y, ir in zip(outputs, actual_outputs, strict=True)), 'synthetic integer local oracle')
        require(torch.equal(torch.cat(outputs, dim=3), chunk), 'synthetic integer reconstruction')
        require(not torch.equal(torch.cat(outputs[::-1], dim=3), chunk), 'synthetic receiver reversal control')
        reversed_peers = [torch.cat([x.chunk(T, dim=3)[j] for x in local_inputs[::-1]], dim=1) for j in range(T)]
        require(not torch.equal(torch.cat(reversed_peers, dim=3), chunk), 'synthetic remote peer reversal control')
        gs = _consumers(sm, before['sm_output_ref'])
        successors = [_one(_consumers(pm, c.outputs[0])) for c in cells]
        require(len(gs) == 1 and all(c.opname.name == 'FW_div' for c in [*gs, *successors]), 'original division inventory')
        descriptions = row['downstream_consumers']
        require([r['node'] for r in descriptions] == [list(c.node) for c in [*gs, *successors]], 'division source node order')
        for c, r in zip([*gs, *successors], descriptions, strict=True):
            require(c.ir.signature == r['source_signature'] == 'torch.div' and r['value_proved'] is False, 'division signature/scope')
            require(_wire(c.kwargs) == _wire(r['source_kwargs']) == _wire(dict(rounding_mode=None, __consts=[4.0])), 'division source kwargs')
            require(r['source_inputs'] == [list(x) for x in c.inputs] and r['source_outputs'] == [list(x) for x in c.outputs], 'division source ports')
            require(r['input_shapes'] == [list(ir.shape) for ir in c._input_irs] and r['output_shapes'] == [list(ir.shape) for ir in c._output_irs], 'division full shapes')
        require(row['observed_consumer_ops'] == [['FW_div']] * (T + 1), 'division observed ops')
        geometry.append(dict(unit=u, global_shape=row['global_shape'], local_shape=shape, axis3_reconstruction=True, receiver_reversal_rejected=True, remote_peer_reversal_rejected=True))
        frontier.append(row)
        units.append(row)
        consumed.append(i)
    require(_wire(new['frontier_units']) == _wire(frontier), 'complete ordered frontier')
    require(_wire(new['retained_units']) == _wire(retained) and _wire(new['deferred_units']) == _wire(deferred), 'retained/deferred frontier cover')
    require(_wire(new['units']) == _wire(units) and new['consumed_frontier_indices'] == consumed, 'consumed unit cover')
    require(len(reads) == len(new['reads']) and len(units) == len(old['units']), 'complete read/unit counts')
    require(all(new[f] is False for f in ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement')), 'raw diagnostic scope')
    return dict(version=REPORT_VERSION, passed=True, independent_original_raw=True,
                reads=len(reads), units=len(units), frontier=len(frontier), retained=len(retained), deferred=len(deferred),
                consumed_indices=consumed, synthetic_integer_layout_oracle=geometry,
                new_capture=False, kernel=False, torch_refinement=False,
                raw_capture_pins={p: h for p, h in world['source_hashes'].items() if p.endswith(('capture.pkl', 'capture.json'))})
