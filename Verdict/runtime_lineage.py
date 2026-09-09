"""Bounded source-only loader -> ordinary embedding lineage and consumers.

These are candidate relations with unproved value obligations, NOT InitGoals.
Batch positions are validated externally; placement never supplies sample identity.
"""
from dataclasses import dataclass, asdict, fields, is_dataclass
from enum import Enum
import json


class Role(str, Enum):
    BATCH = 'batch-input'
    ACTIVATION = 'batch-activation'
    PARAMETER = 'initial-parameter-copy'
    VALUE_PART = 'tp-value-part-sum'
    GRADIENT = 'unit-gradient-contribution'


@dataclass(frozen=True)
class Endpoint:
    ref: tuple
    tid: int
    writer: tuple | None
    phase: str
    shape: tuple


@dataclass(frozen=True)
class Piece:
    endpoint: Endpoint
    bounds: tuple
    value_part: tuple


@dataclass(frozen=True)
class Unit:
    unit: int
    positions: tuple
    reconstruction: str
    pieces: tuple[Piece, ...]


@dataclass(frozen=True)
class Lineage:
    target: Endpoint
    role: Role
    composition: str
    units: tuple[Unit, ...]
    obligations: tuple[str, ...]


class RuntimeLineageBlocked(ValueError):
    def __init__(self, message, receipt):
        super().__init__(message)
        self.receipt = receipt


def op(cell):
    return str(cell.opname).split('.')[-1]


def _metadata(ir):
    p = ir.parent
    if not p.name or not p.shape:
        raise ValueError('missing raw parent identity/layout')
    return (p.name, tuple(p.shape), tuple(tuple(b) for b in ir.indmap),
            tuple(ir.valmap), bool(ir.is_param()), bool(ir.is_grad()))


class _Index:
    def __init__(self, view, cells):
        self.view = view
        self.refs = {tuple(view.source_tensor(t)): t for t in view.tensors()}
        self.writers = {tuple(view.source_tensor(t)): n for n in view.nodes() for t in view.node_outputs(n)}
        self.raw = {tuple(c.node): c for c in cells}
        if len(self.raw) != len(cells):
            raise ValueError('ambiguous raw writer')
        self.meta = {}
        for cell in cells:
            if op(cell) not in ('DATALOADER', 'FW_embedding', 'FW_layernorm', 'FW_linear'):
                continue
            n = cell.node
            if n not in view.nodes() or str(view.node_opname(n)).split('.')[-1] != op(cell):
                raise ValueError('raw opcode/writer mismatch')
            for method, refs, irs in [('node_inputs',cell.inputs,cell._input_irs),('node_outputs',cell.outputs,cell._output_irs)]:
                actual = [tuple(view.source_tensor(t)) for t in getattr(view,method)(n)]
                if actual != [tuple(t) for t in refs] or len(refs) != len(irs):
                    raise ValueError('raw ordered port mismatch')
                for ref, ir in zip(refs, irs):
                    if ref.tid != ir.tid: raise ValueError('raw original tensor port identity mismatch')
                    m = _metadata(ir)
                    if tuple(ref) in self.meta and self.meta[tuple(ref)] != m:
                        raise ValueError('ambiguous raw tensor metadata')
                    self.meta[tuple(ref)] = m
                    if tuple(view.tensor_shape(self.refs[tuple(ref)])) != tuple(b-a for a,b in m[2]):
                        raise ValueError('raw layout/shape mismatch')
            if op(cell) == 'FW_embedding':
                if dict(view.node_kwargs(n)) != dict(cell.kwargs):
                    raise ValueError('raw embedding kwargs mismatch')
                if cell.ir is None or cell.ir.mirror is None:
                    raise ValueError('missing raw embedding mirror')
                if [x.tid for x in cell.ir.inputs()] != [x.tid for x in cell._input_irs]:
                    raise ValueError('raw original embedding input order mismatch')
                if [x.tid for x in cell.ir.outputs()] != [x.tid for x in cell._output_irs]:
                    raise ValueError('raw original embedding output order mismatch')

    def endpoint(self, ref, phase=None):
        ref = tuple(ref)
        t = self.refs[ref]
        writer = self.writers.get(ref)
        inferred = ('boundary-input' if writer and str(self.view.node_opname(writer)).split('.')[-1]=='DATALOADER'
                    else 'intermediate' if writer else 'initial')
        if phase is not None and inferred != phase:
            raise ValueError(f'graph-written tensor cannot be initial: {ref}')
        if inferred=='initial' and not self.view.is_initialized(t):
            raise ValueError(f'missing initial read authority: {ref}')
        shape=tuple(self.view.tensor_shape(t))
        if not shape or any(type(d) is not int or d<=0 for d in shape):
            raise ValueError(f'missing strict shape: {ref}')
        return Endpoint(ref,t.tid,tuple(writer) if writer else None,inferred,shape)


class _TraceValidation(dict):
    """Receipt plus live independent trace inputs, not authority from DTO fields."""
    def __init__(self, validation, inputs):
        super().__init__(validation)
        self._inputs = inputs


def _same_typed(actual, expected):
    # Python equality alone admits bools as ints and strings as Role enums.
    if type(actual) is not type(expected):
        return False
    if is_dataclass(expected):
        return all(_same_typed(getattr(actual, f.name), getattr(expected, f.name)) for f in fields(expected))
    if isinstance(expected, (tuple, list)):
        return len(actual) == len(expected) and all(_same_typed(a, b) for a, b in zip(actual, expected))
    if isinstance(expected, dict):
        return actual.keys() == expected.keys() and all(_same_typed(actual[k], v) for k, v in expected.items())
    return actual == expected


def _training_readpoint(snapshot, loader):
    from nnscaler.codegen.emit import CodeEmission
    from trainverify.runtime_source_authority import _dataloader_training_point, writer_export_id
    emit = CodeEmission()
    fields = ('world', 'runtime_rank', 'microbatch', 'source_tid', 'version')
    refs = [dict(zip(fields, t)) for t in loader.outputs]
    rows = [r for r in snapshot.get('adapter_source', ())
            if r['ref']['runtime_rank'] == loader.rank and r['ref']['source_cid'] == loader.node.cid
            and r['ref']['microbatch'] == loader.node.mb and r['ref']['op'] == 'DATALOADER']
    if len(rows) != 1:
        raise ValueError('missing/ambiguous generated dataloader raw authority')
    row, = rows
    evidence = row['generated_dataloader']
    if (row['outputs'] != refs or evidence['output_refs'] != refs
            or evidence['loader'] != emit.tensor_name(loader.ir.input(0))
            or evidence['outputs'] != [emit.tensor_name(t) for t in loader.ir.outputs()]):
        raise ValueError('generated dataloader raw loader/port order mismatch')
    calls = evidence['training_calls']
    if not calls or calls[0]['input_refs'] != refs or calls[0]['arguments'] != evidence['outputs']:
        raise ValueError('generated first consumer input order mismatch')
    call = calls[0]
    for name, ref in zip(call['parameters'], refs):
        _dataloader_training_point(snapshot, row, call['method'], name,
            dict(ref=ref, writer=writer_export_id(row['ref'])), {}, set())
    if len(call['parameters']) != len(refs):
        raise ValueError('generated first consumer parameter order mismatch')


def trace(sm, pm, sm_cells, pm_cells, snapshot, batch, receipt, reference):
    from trainverify.batch_source_authority import validate_batch_record
    validation = validate_batch_record(batch,snapshot,receipt,reference)
    si,pi = _Index(sm,sm_cells),_Index(pm,pm_cells)
    units=batch['config']['units']
    # Bind validated record back to current independent raw writer ports.
    loaders=[x for x in sm_cells if op(x)=='DATALOADER']
    if len(loaders)!=1:
        raise ValueError('ambiguous global dataloader')
    sl=loaders[0]
    pls={x.rank:x for x in pm_cells if op(x)=='DATALOADER'}
    fields=('world','runtime_rank','microbatch','source_tid','version')
    for row in batch['rank_inputs']:
        if [tuple(r[f] for f in fields) for r in row['refs']] != [tuple(t) for t in pls[row['rank']].outputs]:
            raise ValueError('current raw dataloader readrefs/order mismatch')
    for loader in pls.values():
        try:
            _training_readpoint(snapshot, loader)
        except (KeyError, TypeError, AttributeError, IndexError, SyntaxError, ValueError) as exc:
            raise ValueError('generated dataloader readpoint/order rejected: ' + str(exc)) from exc
    if len(pls)!=len(batch['rank_inputs']):
        raise ValueError('current raw dataloader rank inventory mismatch')
    lineages=[]
    def relation(sr, prs, role):
        smeta=si.meta[tuple(sr)]
        parameter=role==Role.PARAMETER
        if smeta[2]!=tuple((0,d) for d in smeta[1]) or smeta[3]!=(0,1):
            raise ValueError('unsupported global source placement')
        if not parameter and smeta[1][0]!=batch['config']['gbs']:
            raise ValueError('global source batch extent disagrees with authority')
        nested=[]
        for u in units:
            pieces=[]
            full=None
            for rank in u['ranks']:
                pr=prs[rank]; m=pi.meta[tuple(pr)]
                expected_full=smeta[1] if parameter else (len(u['positions']),*smeta[1][1:])
                if (m[0],m[1],m[4:]) != (smeta[0],expected_full,smeta[4:]) or m[3]!=(0,1):
                    raise ValueError('independent raw parent identity/layout/value-part mismatch')
                if full is not None and full!=m[1]: raise ValueError('inconsistent unit parent shape')
                full=m[1]
                pieces.append(Piece(pi.endpoint(pr,'initial' if parameter else None),m[2],m[3]))
            bounds=[p.bounds for p in pieces]
            whole=tuple((0,d) for d in full)
            if all(b==whole for b in bounds):
                reconstruction='tp-copy-obligation'
            else:
                axes=[i for i in range(len(full)) if any(b[i]!=whole[i] for b in bounds)]
                if len(axes)!=1:
                    raise ValueError('unsupported TP multi-axis placement')
                axis=axes[0]; end=0
                for b in bounds:
                    if b[axis][0]!=end or b[axis][1]<=end or any(b[i]!=whole[i] for i in range(len(full)) if i!=axis):
                        raise ValueError('unordered or incomplete TP placement')
                    end=b[axis][1]
                if end!=full[axis]: raise ValueError('incomplete TP reconstruction')
                reconstruction=f'tp-axis-gather:{axis}'
            nested.append(Unit(u['unit'],() if parameter else tuple(u['positions']),reconstruction,tuple(pieces)))
        obligations=('initial-parameter-value-equality-unproved',) if parameter else ('capture-sample-association-unproved','operator-value-propagation-unproved')
        return Lineage(si.endpoint(sr,'initial' if parameter else None),role,
                       'unit-parameter-copies' if parameter else 'ordered-global-batch:0',tuple(nested),obligations)
    for port,sr in enumerate(sl.outputs):
        lineages.append(relation(sr,{r:cell.outputs[port] for r,cell in pls.items()},Role.BATCH))
    # Only embedding fed directly by an authenticated loader output. No index alignment.
    for sc in sm_cells:
        if op(sc)!='FW_embedding' or len(sc.inputs)!=2 or sc.inputs[0] not in sl.outputs:
            continue
        candidates={}
        for rank,loader in pls.items():
            port=sl.outputs.index(sc.inputs[0])
            matches=[pc for pc in pm_cells if pc.rank==rank and op(pc)=='FW_embedding'
                     and len(pc.inputs)==2 and pc.inputs[0]==loader.outputs[port]
                     and _metadata(pc._input_irs[1])[0]==_metadata(sc._input_irs[1])[0]]
            if len(matches)!=1:
                candidates={}; break
            pc=matches[0]
            if pc.ir.signature!=sc.ir.signature or dict(pc.kwargs)!=dict(sc.kwargs):
                raise ValueError('independent raw embedding signature/kwargs mismatch')
            if not pc._input_irs[1].is_param() or not sc._input_irs[1].is_param() or len(pc.outputs)!=1 or len(sc.outputs)!=1:
                raise ValueError('unsupported embedding parameter/output roles')
            candidates[rank]=pc
        if not candidates: continue
        # Ordinary hidden slicing only: indices full within unit, weight row range whole.
        for pc in candidates.values():
            x,w,y=map(_metadata,[pc._input_irs[0],pc._input_irs[1],pc._output_irs[0]])
            if x[2]!=tuple((0,d) for d in x[1]) or w[2][0]!=(0,w[1][0]) or y[2]!=(*x[2],w[2][1]):
                raise ValueError('unsupported ordinary embedding placement')
            if pc.kwargs.get('start')!=0 or pc.kwargs.get('stop')!=w[1][0]:
                raise ValueError('unsupported ordinary embedding offset')
        lineages.append(relation(sc.inputs[1],{r:pc.inputs[1] for r,pc in candidates.items()},Role.PARAMETER))
        lineages.append(relation(sc.outputs[0],{r:pc.outputs[0] for r,pc in candidates.items()},Role.ACTIVATION))
    # Initial parameters come from the same original raw input ports as
    # runtime_parameter_inputs, never from an observation/receipt or a shape.
    def parameters(index, cells, world, ranks):
        refs={}; parents={}; names={}
        for cell in cells:
            if op(cell) not in ('FW_embedding', 'FW_layernorm', 'FW_linear'):
                continue
            for ref, ir in zip(cell.inputs, cell._input_irs, strict=True):
                ref=tuple(ref)
                if not ir.is_param() or ir.is_grad() or ref in index.writers:
                    continue
                if (ref[0]!=world or ref[1]!=cell.rank or ref[1] not in ranks
                        or ref[2]!=-1 or ref[4]!=0):
                    raise ValueError('initial parameter fullref owner/phase mismatch')
                if ref in parents and parents[ref]!=ir.parent.tid:
                    raise ValueError('ambiguous raw parameter parent')
                parents[ref]=ir.parent.tid
                index.endpoint(ref,'initial')
                meta=index.meta[ref]
                if meta[3]!=(0,1):
                    raise ValueError('unsupported initial parameter value partition')
                key=(meta[0],ref[1])
                if key in names and names[key]!=ref:
                    raise ValueError('ambiguous initial parameter logical name/rank')
                names[key]=ref
                refs[ref]=meta
        return refs
    ranks={rank for u in units for rank in u['ranks']}
    global_parameters=parameters(si,sm_cells,'s',{0})
    local_parameters=parameters(pi,pm_cells,'p',ranks)
    globals_by_name={meta[0]:ref for ref,meta in global_parameters.items()}
    locals_by_name={}
    for ref,meta in local_parameters.items():
        if meta[0] not in globals_by_name:
            raise ValueError('missing original global parameter identity')
        locals_by_name.setdefault(meta[0],{})[ref[1]]=ref
    covered={l.target.ref for l in lineages}
    for sr,smeta in global_parameters.items():
        prs=locals_by_name.get(smeta[0],{})
        if set(prs)!=ranks:
            raise ValueError('incomplete initial parameter rank inventory')
        # Validate already-covered embedding parameters too, without changing
        # their original relation or the existing loader/embedding order.
        candidate=relation(sr,prs,Role.PARAMETER)
        if sr not in covered:
            lineages.append(candidate)
            covered.add(sr)
    gaps=[dict(ref=list(t),role='unsupported-target',op=str(sm.node_opname(n))) for n in sm.nodes()
          for low in sm.node_outputs(n) for t in [sm.source_tensor(low)] if tuple(t) not in covered]
    return tuple(lineages),gaps,_TraceValidation(validation, (sm_cells,pm_cells,snapshot,batch,receipt,reference))


def consume(sm, pm, lineages, gaps, validation, closure):
    """Use typed grouping/roots in a single full backward closure per world."""
    if type(validation) is not _TraceValidation:
        raise ValueError('missing independent trace authority')
    canonical, _, current = trace(sm, pm, *validation._inputs)
    if not _same_typed(dict(validation), dict(current)):
        raise ValueError('stale/forged batch validation metadata')
    expected = {l.target.ref: l for l in canonical}
    for l in lineages:
        if type(l) is not Lineage or not any(_same_typed(l, e) for e in expected.values()):
            raise ValueError('typed lineage differs from current raw/batch authority')
    by_target={}
    indexes={id(view):_Index(view,[]) for view in (sm,pm)}
    for l in lineages:
        if l.role not in (Role.BATCH,Role.ACTIVATION,Role.PARAMETER):
            raise ValueError(f'unsupported typed role: {l.role}')
        for view,e in [(sm,l.target), *[(pm,p.endpoint) for u in l.units for p in u.pieces]]:
            actual=indexes[id(view)].endpoint(e.ref,e.phase)
            if actual!=e: raise ValueError(f'typed endpoint identity/shape/writer mismatch: {e.ref}')
        if l.target.ref in by_target: raise ValueError('ambiguous typed target')
        by_target[l.target.ref]=l
    covered={l.target.ref for l in lineages}|{p.endpoint.ref for l in lineages for u in l.units for p in u.pieces}
    gaps=sorted((dict(ref=list(view.source_tensor(t)),role='unsupported-source-tensor')
                 for view in (sm,pm) for t in view.tensors() if tuple(view.source_tensor(t)) not in covered),
                key=lambda gap: tuple(gap['ref']))
    sm_roots=[l.target.tid for l in by_target.values()]
    pm_roots=[p.endpoint.tid for l in by_target.values() for u in l.units for p in u.pieces]
    boundaries=[]; closures={}
    for label,view,roots in [('s',sm,sm_roots),('p',pm,pm_roots)]:
        needed=closure(view,roots);closures[label]=needed
        tensors={t.tid:t for t in view.tensors()}
        writers={t.tid:n for n in view.nodes() for t in view.node_outputs(n)}
        for tid in needed:
            t=tensors[tid];shape=tuple(view.tensor_shape(t)); ref=tuple(view.source_tensor(t))
            if not shape or any(type(d)is not int or d<=0 for d in shape): raise ValueError(f'missing strict shape: {ref}')
            n=writers.get(tid)
            if n is None:
                if not view.is_initialized(t): raise ValueError(f'unclassified initial read: {ref}')
                kind='initial-value-obligation'
            elif str(view.node_opname(n)).split('.')[-1]=='DATALOADER': kind='boundary-input-not-initialized'
            else: continue
            boundaries.append(dict(ref=list(ref),tid=tid,shape=list(shape),kind=kind))
    return dict(stage='runtime-world-render/public-adapter',scope='source-only',proof_admissible=False,
                publication=False,capture_sample_association_verified=False,global_complete=False,
                validation=validation,lineages=json.loads(json.dumps([asdict(l) for l in lineages])),gaps=gaps,boundary=boundaries,
                sm_roots=sm_roots,pm_roots=pm_roots,closures=closures,
                coverage=dict(typed_targets=len(by_target),unsupported_targets=len(gaps)),
                unproved_value_obligations=sorted({o for l in lineages for o in l.obligations}))
