"""Source-derived INTERNAL autograd edge domain; never Executor per-node calls.

The trusted loader first authenticates original ModuleCodeGen, the complete
executed segment, singleton loss schedule, loaded-code event and raw graph.
This module joins its IR edges to the actual lowered view. Boundary multirefs,
partial cotangents and ambiguous consumer/gradient mappings remain unsupported.
This is bounded source translation authority, not universal Torch refinement.
"""
from copy import deepcopy
import hashlib
from pathlib import Path


def _require(ok, reason):
    if not ok:
        raise ValueError('multiref authority: ' + reason)


def _view_key(view):
    return [(tuple(n), str(view.node_opname(n)), dict(view.node_kwargs(n)),
             [(t.tid, tuple(view.source_tensor(t))) for t in view.node_inputs(n)],
             [(t.tid, tuple(view.source_tensor(t))) for t in view.node_outputs(n)])
            for n in view.nodes()]


_DERIVED = object()


class InternalEdges:
    """Ephemeral loader result, not deserialized metadata or an admission flag."""
    def __init__(self, view, rows, pins, *, _derived=None):
        _require(_derived is _DERIVED, 'requires fresh internal derivation')
        self._view = deepcopy(_view_key(view))
        self._rows = deepcopy(rows)
        self._pins = dict(pins)

    def validate(self, view):
        _require(self._view == _view_key(view), 'stale/rebound lowered graph')
        for path, digest in self._pins.items():
            _require(hashlib.sha256(Path(path).read_bytes()).hexdigest() == digest,
                     'stale source/run pin')
        return {tuple(row['backward_node']) for row in self._rows}

    def receipt(self):
        return dict(domain='internal-retained-autograd-segment', edges=deepcopy(self._rows),
                    pins=dict(self._pins), torch_refinement=False)


def derive(view, cells, mg, world, requests, pins):
    """Called only with freshly authenticated original capture and run evidence.

    Each output occurrence needs one real consumer input occurrence and its
    matching returned cotangent. No sets of tensor IDs stand in for edge order.
    Multiple consumers of one output would require explicit accumulation-tree
    authority, so that larger domain is deliberately rejected here.
    """
    from nnscaler.graph.segment import IRSegment
    from nnscaler_backend.build_graph import _flatten_exereuse_then_scale
    refs = {tuple(view.source_tensor(t)): t.tid for t in view.tensors()}
    _require(len(refs) == len(list(view.tensors())), 'partial/nonbijective view')
    rows = []
    for rank in range(world.runtime_ndevs):
        seq = _flatten_exereuse_then_scale(mg.execplan.seq(rank % world.plan_ndevs), mg, rank)
        rank_cells = [c for c in cells if c.rank == rank]
        reqs = [r for r in requests if r['seed']['runtime_rank'] == rank]
        _require(len(reqs) == 1, 'singleton retained schedule required')
        request, = reqs
        ordinal = request['schedule_ordinal']
        _require(0 < ordinal < len(seq), 'missing backward occurrence')
        segment, back = seq[ordinal-1:ordinal+1]
        _require(isinstance(segment, IRSegment) and isinstance(back, IRSegment)
                 and segment.isfw() and not back.isfw()
                 and 'segment'+str(segment.cid) == request['segment']
                 and back.cid == request['backward_cid']
                 and back.mirror.cid == segment.cid
                 and len(segment.outputs()) == len(back.inputs()) == 1 and not back.outputs(),
                 'retained segment/mirror/root mismatch')
        fw_nodes, bw_nodes = list(segment.nodes()), list(back.nodes())
        for bw in rank_cells:
            if bw.opname.name != 'BW_multiref':
                continue
            try:
                fw = bw.ir.mirror
                _require(bw.mb == 0 and fw.mirror.cid == bw.ir.cid, 'mirror/call mismatch')
                _require(sum(n.cid == fw.cid for n in fw_nodes) == 1
                         and sum(n.cid == bw.ir.cid for n in bw_nodes) == 1,
                         'multiref outside retained segment')
                fcell, = [c for c in rank_cells if c.opname.name == 'FW_multiref' and c.ir.cid == fw.cid]
                outputs = list(fw.outputs())
                _require(len(fw.inputs()) == len(bw.outputs) == 1 and outputs
                         and len(outputs) == len(bw.inputs) == len(bw.ir.inputs())
                         and len(fcell.outputs) == len(outputs), 'partial mirror ports')
                _require(fw.input(0).grad == bw.ir.output(0)
                         and bw.outputs[0].tid == bw.ir.output(0).tid, 'input gradient mirror')
                edges = []
                for port, (out, grad, raw_out, raw_grad) in enumerate(zip(
                        outputs, bw.ir.inputs(), fcell.outputs, bw.inputs, strict=True)):
                    _require(out.grad == grad and raw_out.tid == out.tid and raw_grad.tid == grad.tid,
                             'ordered output/cotangent mirror mismatch')
                    _require(out not in segment.outputs(), 'Executor boundary output unsupported')
                    consumers = [(n, p) for n in fw_nodes for p, t in enumerate(n.inputs()) if t == out]
                    _require(len(consumers) == 1, 'missing/ambiguous consumer edge')
                    consumer, input_port = consumers[0]
                    _require(fw_nodes.index(consumer) > next(i for i,n in enumerate(fw_nodes) if n.cid == fw.cid),
                             'consumer precedes multiref')
                    mirror = consumer.mirror
                    _require(mirror is not None and mirror.mirror.cid == consumer.cid
                             and sum(n.cid == mirror.cid for n in bw_nodes) == 1,
                             'consumer backward outside retained segment')
                    _require(list(mirror.outputs()) == [t.grad for t in consumer.inputs()
                             if getattr(t, 'grad', None) is not None], 'ordered consumer returned gradients')
                    grad_ports = [p for p,t in enumerate(mirror.outputs()) if t == grad]
                    _require(len(grad_ports) == 1, 'ambiguous returned cotangent')
                    _require(next(i for i,n in enumerate(bw_nodes) if n.cid == mirror.cid)
                             < next(i for i,n in enumerate(bw_nodes) if n.cid == bw.ir.cid), 'cotangent schedule order')
                    writers = [(c,p) for c in rank_cells for p,t in enumerate(c.outputs) if t == raw_grad]
                    _require(len(writers) == 1, 'missing/ambiguous raw gradient writer')
                    writer, grad_port = writers[0]
                    owner = getattr(writer, 'adapter', None) or writer.ir
                    _require(getattr(owner, 'cid', None) == mirror.cid, 'raw gradient owner mismatch')
                    edges.append(dict(output_port=port, forward_ref=list(raw_out), gradient_ref=list(raw_grad),
                        output_tid=refs[tuple(raw_out)], gradient_tid=refs[tuple(raw_grad)],
                        consumer_cid=consumer.cid, consumer_input_port=input_port,
                        consumer_backward_cid=mirror.cid, returned_gradient_port=grad_ports[0],
                        gradient_writer=list(writer.node), gradient_writer_port=grad_port))
                rows.append(dict(runtime_rank=rank, microbatch=bw.mb, call_instance=0,
                    segment=request['segment'], backward_segment=back.cid, schedule_ordinal=ordinal,
                    forward_node=list(fcell.node), backward_node=list(bw.node), edges=edges,
                    result_ref=list(bw.outputs[0]), result_tid=refs[tuple(bw.outputs[0])]))
            except (ValueError, AttributeError, KeyError):
                # Unsupported source domains never acquire an admission entry.
                continue
    return InternalEdges(view, rows, pins, _derived=_DERIVED)
