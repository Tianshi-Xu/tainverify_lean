"""Complete source-only world definitions. No public or input-value theorem.

The explicit ordinary policy is a bounded Denote domain, not Torch refinement.
Unknown operations and graph-written loader inputs get a missing request, never
Denote's permissive ordinary/zero fallback. All graph nodes remain represented.
"""
from copy import copy
from dataclasses import dataclass, field
import hashlib
import re
import json
from pathlib import Path
import tempfile

COLLECTIVES = {'AllToAllPrim', 'AllGatherPrim', 'AllReducePrim', 'ReduceScatterPrim', 'ChunkPrim', 'CROSS_DP_WRED', 'WRED'}
# Only source parameter schemas examined for this bounded generator.
SCHEMAS = {'sum': set(), 'linear': {'bias'}, 'add': {'alpha'}, 'multiref': {'times'},
           'layernorm': {'normalized_shape', 'eps'}, 'view': {'size'}, 'reshape': {'shape', 'size'},
           'transpose': {'dim0', 'dim1'}, 'matmul': set(), 'div': {'rounding_mode'},
           'softmax': {'dim', 'dtype'}, 'contiguous': set(), 'gelu': {'approximate'},
           'embedding': {'padding_idx', 'start', 'stop'}}
ARITIES = {'sum': (1, 1, 2, 1), 'linear': (2, 1, 3, 2), 'add': (2, 1, 3, 2),
           'layernorm': (3, 1, 4, 3), 'view': (1, 1, 2, 1), 'reshape': (1, 1, 2, 1),
           'transpose': (1, 1, 2, 1), 'matmul': (2, 1, 3, 2), 'div': (1, 1, 2, 1),
           'softmax': (1, 1, 2, 1), 'contiguous': (1, 1, 2, 1), 'gelu': (1, 1, 2, 1),
           'embedding': (2, 1, 3, 1)}


def _ordinary(view, n, get_params):
    op = str(view.node_opname(n)).split('.')[-1]
    kw = dict(view.node_kwargs(n))
    if op == 'DATALOADER':
        if set(kw) - {'__consts'}: raise ValueError('unknown loader parameters')
        return [], 'input-adapter-unproved'
    stem = op[3:] if op.startswith(('FW_', 'BW_')) else None
    if stem not in SCHEMAS:
        if kw: raise ValueError(f'unknown source operation parameters: {op}')
        return [], 'unsupported-source-operation'
    consts = kw.pop('__consts', [])
    if set(kw) - SCHEMAS[stem]: raise ValueError(f'unknown ordinary parameters: {op}: {kw}')
    if stem != 'div' and consts: raise ValueError(f'unsupported ordinary constants: {op}')
    for key, expected in [('bias', None), ('alpha', 1), ('rounding_mode', None), ('dtype', None), ('approximate', 'none'), ('padding_idx', None)]:
        if key in kw and kw[key] != expected: raise ValueError(f'unsupported source parameter {op}.{key}')

    if stem == 'embedding' and (type(kw.get('start')) is not int or kw['start'] != 0 or type(kw.get('stop')) is not int):
        raise ValueError('missing source embedding offset authority')
    if stem == 'div' and (len(consts) != 1 or type(consts[0]) not in (int, float) or consts[0] <= 0 or int(consts[0]) != consts[0]):
        raise ValueError('nonintegral or missing divisor')
    if stem == 'transpose' and (set(kw) != {'dim0', 'dim1'} or any(type(d) is not int for d in kw.values())):
        raise ValueError('missing transpose dimensions')
    params = get_params(view, n, num_parts=0)
    if stem in ('view', 'reshape', 'transpose', 'div') and params is None: raise ValueError('missing ordinary params')
    params = params or []
    if any(type(p) is not int or p < 0 for p in params): raise ValueError('invalid Nat params')
    if stem == 'transpose' and any(p >= len(view.tensor_shape(view.node_inputs(n)[0])) for p in params):
        raise ValueError('transpose dimension out of bounds')
    ins, outs = len(view.node_inputs(n)), len(view.node_outputs(n))
    if stem == 'multiref':
        valid = (ins == 1 and outs == kw.get('times')) if op.startswith('FW_') else (ins > 0 and outs == 1)
    else:
        a = ARITIES[stem]; valid = (ins, outs) == (a[:2] if op.startswith('FW_') else a[2:])
    if stem == 'softmax' and valid:
        # BW takes (gradient, original x); its axis belongs to x, not gradient.
        offset = 0 if op.startswith('FW_') else 1
        xshape = tuple(view.tensor_shape(view.node_inputs(n)[offset]))
        dim = kw.get('dim')
        if (type(dim) is not int or not xshape or not -len(xshape) <= dim < len(xshape)
                or dim % len(xshape) != len(xshape) - 1):
            raise ValueError('unsupported softmax axis')
    if stem == 'layernorm' and valid:
        # Denote.layerNormEps is fixed and fw/bw_layernorm normalize only the last axis.
        eps, norm = kw.get('eps', 1e-5), kw.get('normalized_shape')
        tids = view.node_inputs(n)
        offset = 0 if op.startswith('FW_') else 1
        xshape = tuple(view.tensor_shape(tids[offset]))
        if type(eps) not in (float, int) or eps != 1e-5:
            raise ValueError('unsupported layernorm epsilon')
        if (type(norm) not in (list, tuple) or len(norm) != 1
                or type(norm[0]) is not int or not xshape or norm[0] != xshape[-1]
                or any(tuple(view.tensor_shape(t)) != tuple(norm) for t in tids[offset+1:offset+3])):
            raise ValueError('unsupported layernorm normalized shape')
    return params, None if valid else 'unsupported-source-arity'


def _authenticate(view, raw_cells, c):
    if not isinstance(view, c._RuntimeGraphView): raise ValueError('world requires identity-safe view')
    if tuple(view.nodes()) != view._runtime_original_nodes or view.nodes() != list(view.source.nodes()):
        raise ValueError('world raw node sequence mismatch')
    if view.W.runtime_ndevs != view._runtime_world_size or type(view.W.runtime_ndevs) is not int or view.W.runtime_ndevs <= 0:
        raise ValueError('world size mismatch')
    if len(set(view.nodes())) != len(view.nodes()): raise ValueError('duplicate source node')
    if list(view.source.tensors()) != list(view._lowered) or view.tensors() != list(view._lowered.values()):
        raise ValueError('world fullref inventory mismatch')
    raw = {x.node: x for x in raw_cells}
    if len(raw) != len(raw_cells) or set(raw) != set(view.nodes()): raise ValueError('raw writer inventory mismatch')
    written = set()
    for n in view.nodes():
        if type(n.rank) is not int or not 0 <= n.rank < view.W.runtime_ndevs: raise ValueError('invalid world rank')
        op = str(view.node_opname(n)).split('.')[-1]
        cell = raw[n]
        if str(cell.opname).split('.')[-1] != op: raise ValueError('raw source opcode mismatch')
        if op not in COLLECTIVES and dict(cell.kwargs) != dict(view.node_kwargs(n)):
            raise ValueError('raw source params mismatch')
        for method in ('node_inputs', 'node_outputs'):
            ts = getattr(view, method)(n)
            if [view.source_tensor(t) for t in ts] != list(getattr(view.source, method)(n)):
                raise ValueError('raw ordered fullref mismatch')
        if op not in COLLECTIVES:
            for method, field, irfield in (('node_inputs', 'inputs', '_input_irs'), ('node_outputs', 'outputs', '_output_irs')):
                if not isinstance(getattr(cell, field, None), (list, tuple)) or not hasattr(cell, irfield):
                    raise ValueError('missing independent raw ports/shapes')
                if hasattr(cell, field):
                    ts = getattr(view, method)(n)
                    if [view.source_tensor(t) for t in ts] != list(getattr(cell, field)):
                        raise ValueError('independent raw ordered fullref mismatch')
                    irs = getattr(cell, irfield)
                    if len(ts) != len(irs) or any(tuple(view.tensor_shape(t)) != tuple(ir.shape) for t, ir in zip(ts, irs)):
                        raise ValueError('independent raw shape mismatch')
        for t in view.node_outputs(n):
            if t.tid in written: raise ValueError('duplicate fullref writer')
            written.add(t.tid)
    for t in view.tensors():
        sh = tuple(view.tensor_shape(t))
        if any(type(d) is not int or d <= 0 for d in sh): raise ValueError('invalid tensor shape')
        if type(t.tid) is not int or t.tid < 0: raise ValueError('invalid lowered ID')
        view.source_tensor(t)
    # Rebind on a copy: failed validation must not repair a tampered attachment.
    fresh = copy(view)
    for name in ('chunk_scopes', 'collective_scopes', 'wred_scopes'):
        fresh.__dict__.pop(name, None)
    ops = {str(view.node_opname(n)).split('.')[-1] for n in view.nodes()}
    if 'CROSS_DP_WRED' in ops:
        if not all(hasattr(view, field) for field in ('_wred_source', '_wred_raw', '_wred_rank_sources')):
            raise ValueError('missing WRED source authority')
        c.attach_wred_scopes(fresh, view._wred_source, view._wred_raw, view._wred_rank_sources)
    elif ops & (COLLECTIVES - {'ChunkPrim', 'CROSS_DP_WRED', 'WRED'}):
        if not hasattr(view, '_collective_source'): raise ValueError('missing collective source authority')
        c.attach_collective_scopes(fresh, view._collective_source)
    elif 'ChunkPrim' in ops:
        if not hasattr(view, '_chunk_source'): raise ValueError('missing Chunk source authority')
        c.attach_chunk_scopes(fresh, view._chunk_source)
    for name in ('chunk_scopes', 'collective_scopes', 'wred_scopes'):
        if getattr(view, name, {}) != getattr(fresh, name, {}): raise ValueError('stale attached scope')
    return written


@dataclass(frozen=True)
class WorldDefinitions:
    lean: str
    receipt: dict
    supporting_sources: dict = field(default_factory=dict)


WORLD_DATA_MODULE = 'TrainVerifyRuntimeWorldData'
WORLD_DATA_FILE = WORLD_DATA_MODULE + '.lean'


def _proof_bundle(lean, supporting_sources, entry='$entry'):
    """Source consistency inventory, not a kernel or execution certificate."""
    if type(supporting_sources) is not dict or WORLD_DATA_FILE not in supporting_sources:
        raise ValueError('world bundle requires exactly one data module')
    from Verdict.runtime_prefix import PREFIX_MODULE, SUPPORT_MODULE, SUPPORT_FILE, support_source, expand_names
    if supporting_sources.get(SUPPORT_FILE) != support_source():
        raise ValueError('world bundle prefix support source mismatch')
    chunks = sorted(set(supporting_sources) - {WORLD_DATA_FILE, SUPPORT_FILE})
    if chunks != [f'{PREFIX_MODULE}{i:04d}.lean' for i in range(len(chunks))]:
        raise ValueError('world bundle prefix module identity mismatch')
    if not lean.startswith(f'import {WORLD_DATA_MODULE}\nimport denote.SourceScopedPrefix\n'):
        raise ValueError('world bundle entry must import its data and prefix helper')
    from Verdict.graph_to_lean import GENERATED_LEAN_SOURCE_LIMIT
    source_bytes = 0
    modules = []
    for filename, text, role in [(WORLD_DATA_FILE, supporting_sources[WORLD_DATA_FILE], 'data'),
                                  (SUPPORT_FILE, supporting_sources[SUPPORT_FILE], 'support'),
                                  *((name, supporting_sources[name], 'prefix') for name in chunks),
                                  (entry, lean, 'entry')]:
        if type(text) is not str:
            raise ValueError('world bundle source must be text')
        imports = [name for line in re.findall(r'^\s*import\s+([^\n]+)', text, re.M) for name in line.split()]
        expected = (['denote.SourceScopedEval'] if role == 'data' else
                    ['Lean', 'denote.Denote'] if role == 'support' else
                    [WORLD_DATA_MODULE, 'denote.SourceScopedPrefix', SUPPORT_MODULE])
        parameter_helper = ('denote.SourceParameterFrame' if 'denote.SourceParameterFrame' in imports else
                            'denote.SourceInitialParameterSpecs' if 'denote.SourceInitialParameterSpecs' in imports
                            else 'denote.SourceInitialParameters')
        if role == 'entry' and parameter_helper in imports:
            expected.insert(2, parameter_helper)
            if 'denote.SourceInitialInputEncoding' in imports:
                expected.insert(3, 'denote.SourceInitialInputEncoding')
                read_helper = ('denote.SourceEmbeddingRead' if 'denote.SourceEmbeddingRead' in imports
                               else 'denote.SourceInitialInputRead')
                if read_helper in imports:
                    expected.insert(4, read_helper)
                if read_helper == 'denote.SourceEmbeddingRead' and 'denote.SourceEmbeddingUnit' in imports:
                    expected.insert(5, 'denote.SourceEmbeddingUnit')
                if read_helper == 'denote.SourceEmbeddingRead' and 'denote.SourcePrimitiveRead' in imports:
                    expected.insert(5, 'denote.SourcePrimitiveRead')
                    if 'denote.SourceEmbeddingPositionUnit' in imports:
                        expected.insert(6, 'denote.SourceEmbeddingPositionUnit')
                if read_helper == 'denote.SourceEmbeddingRead' and all(
                        name in imports for name in ('denote.SourceAddRead', 'denote.SourceAddUnit')):
                    expected[5:5] = ['denote.SourceAddRead', 'denote.SourceAddUnit']
                    if 'denote.SourceAddFacts' in imports:
                        expected.insert(7, 'denote.SourceAddFacts')
                        if 'denote.SourceMultirefRead' in imports:
                            expected.insert(8, 'denote.SourceMultirefRead')
                            if 'denote.SourceHiddenSequenceExchange' in imports:
                                expected.insert(9, 'denote.SourceHiddenSequenceExchange')
                                if all(name in imports for name in ('denote.SourceLayernormRead', 'denote.SourceLayernormUnit')):
                                    expected[10:10] = ['denote.SourceLayernormRead', 'denote.SourceLayernormUnit']
                                    projection_imports = ['denote.SourceLinearRead', 'denote.SourceAllGatherRead', 'denote.SourceLinearUnit']
                                    if all(name in imports for name in projection_imports):
                                        expected[12:12] = projection_imports
                                        view_imports = ['denote.SourceLayoutRead', 'denote.SourceViewUnit']
                                        if all(name in imports for name in view_imports):
                                            expected[15:15] = view_imports
                                            if 'denote.SourceRank4Exchange' in imports:
                                                expected.insert(17, 'denote.SourceRank4Exchange')
                                                if 'denote.SourceTransposeUnit' in imports:
                                                    expected.insert(18, 'denote.SourceTransposeUnit')
                                                    post_imports = ['denote.SourceTranspose23Unit', 'denote.SourceRank4ReverseExchange']
                                                    if all(name in imports for name in post_imports):
                                                        expected[19:19] = post_imports
                                                        if 'denote.SourceRank4MiddleExchange' in imports:
                                                            expected.insert(21, 'denote.SourceRank4MiddleExchange')
                                                            matmul_imports = ['denote.SourceMatmulRead', 'denote.SourceMatmulUnit']
                                                            if all(name in imports for name in matmul_imports):
                                                                expected[22:22] = matmul_imports
                                                                div_imports = ['denote.SourceDivRead', 'denote.SourceDivUnit']
                                                                if all(name in imports for name in div_imports):
                                                                    expected[24:24] = div_imports
                                                                    softmax_imports = ['denote.SourceSoftmaxRead', 'denote.SourceSoftmaxUnit']
                                                                    if all(name in imports for name in softmax_imports):
                                                                        expected[26:26] = softmax_imports
                                                                        if 'denote.SourceRank4InnerExchange' in imports:
                                                                            expected.insert(28, 'denote.SourceRank4InnerExchange')
                                                                            if 'denote.SourceQueryMatmulUnit' in imports:
                                                                                expected.insert(29, 'denote.SourceQueryMatmulUnit')
                                                                                if 'denote.SourceQueryTransposeUnit' in imports:
                                                                                    expected.insert(30, 'denote.SourceQueryTransposeUnit')
                                                                                    if 'denote.SourceContiguousRead' in imports:
                                                                                        expected.insert(31, 'denote.SourceContiguousRead')
                                                                                        if 'denote.SourceViewFlattenUnit' in imports:
                                                                                            expected.insert(32, 'denote.SourceViewFlattenUnit')
                                                                                            if 'denote.SourceSequenceHiddenExchange' in imports:
                                                                                                expected.insert(33, 'denote.SourceSequenceHiddenExchange')
                                                                                                gelu_imports = ['denote.SourceGeluRead', 'denote.SourceGeluUnit']
                                                                                                if all(name in imports for name in gelu_imports):
                                                                                                    expected[34:34] = gelu_imports
                if read_helper == 'denote.SourceEmbeddingRead' and 'denote.SourceEmbeddingFacts' in imports:
                    expected.insert(5, 'denote.SourceEmbeddingFacts')
        if role in ('prefix', 'entry') and modules[-1]['role'] == 'prefix':
            expected.append(modules[-1]['module'])
        if imports != expected:
            raise ValueError('world bundle import membership mismatch')
        source_bytes += len(text.encode('utf-8'))
        modules.append(dict(file=filename, module=Path(filename).stem, role=role, imports=imports,
            source_sha256=hashlib.sha256(text.encode('utf-8')).hexdigest(),
            theorems=re.findall(r'^theorem (\S+)', expand_names(text) if role in ('prefix', 'entry') else text, re.M), kernel_checked=False))
    # Unlike the generic per-file scanner, runtime-world bounds the whole bundle.
    # This shared inventory is checked by both rendering and publish, before staging.
    if source_bytes >= GENERATED_LEAN_SOURCE_LIMIT:
        raise ValueError(f'world bundle generated Lean source exceeds {GENERATED_LEAN_SOURCE_LIMIT} byte limit: '
                         f'{source_bytes} bytes total')
    return dict(modules=modules, dependency_order=[WORLD_DATA_FILE, SUPPORT_FILE, *chunks, entry], kernel_checked=False)


def render(sm, pm, raw_sm, raw_pm):
    from Verdict import graph_to_lean as c
    lines = ['import denote.SourceScopedEval', 'namespace TrainVerify.Denote.RuntimeWorld',
             'set_option maxHeartbeats 500000', 'noncomputable section',
             '-- Source-only definitions; no Torch refinement or public value closure.']
    from Verdict.runtime_schedule import build
    missing = []; counts = {}; refs = {}; identity = {}; execution_order = {}
    for label, view, raw in [('sm', sm, raw_sm), ('pm', pm, raw_pm)]:
        written = _authenticate(view, raw, c)
        execution_order[label] = build(view)
        order = execution_order[label]["execution_to_source"]
        for t in view.tensors():
            ref = tuple(view.source_tensor(t))
            if t.tid in identity and identity[t.tid] != ref: raise ValueError('cross-world lowered ID collision')
            identity[t.tid] = ref
        refs[label] = [dict(tid=t.tid, ref=list(view.source_tensor(t)), shape=list(view.tensor_shape(t)),
                            graph_written=t.tid in written) for t in sorted(view.tensors(), key=lambda t: t.tid)]
        table = []; declared = {}
        for i, n in enumerate(view.nodes()):
            op = str(view.node_opname(n)).split('.')[-1]
            ins = [t.tid for t in view.node_inputs(n)]; outs = [t.tid for t in view.node_outputs(n)]
            peers = (); reason = None
            if op in COLLECTIVES:
                scopes = getattr(view, 'chunk_scopes' if op == 'ChunkPrim' else 'wred_scopes' if op == 'CROSS_DP_WRED' else 'collective_scopes', {})
                if n not in scopes: raise ValueError(f'missing authenticated collective scope: {n}')
                scope = scopes[n]
                params = [scope.dim] if op == 'ChunkPrim' else [] if op == 'CROSS_DP_WRED' else list(scope.params)
                request = f'.group (some {list(scope.ranks)})'
                if op != 'ChunkPrim': peers = tuple(zip(scope.ranks, scope.input_tids))
            else:
                params, reason = _ordinary(view, n, c._get_node_params)
                request = '.group none' if reason else '.global'
            literal = f'{{rank := {n.rank}, op := {json.dumps("OpName." + op)}, ins := {ins}, outs := {outs}, params := {params}}}'
            meaning = (request, peers)
            if literal in declared and declared[literal] != meaning: raise ValueError('equal NodeDecl requires incompatible scopes/peers')
            declared[literal] = meaning
            name = f'{label}Node_{i}'
            lines.append(f'def {name} : NodeDecl := {literal}')
            table.append(f'({name}, {request}, [{", ".join(f"({r}, {t})" for r,t in peers)}])')
            if reason:
                missing.append(dict(world=label, node=list(n), index=i, reason=reason))
                # Kernel-checkable fail-closed witness generated from the same exact node.
                lines.extend([f'theorem {name}_blocked (g : GraphDecl) (s : Store) (peer : Nat → Tid) :',
                    f'    SourceScopedEval.step g (.group none) peer s {name} = none := rfl',
                    f'#print axioms {name}_blocked'])
        counts[label + '_nodes'] = len(view.nodes())
        lines.extend([f'def {label}Graph : GraphDecl := {{numRanks := {view.W.runtime_ndevs}, nodes := [{", ".join(f"{label}Node_{i}" for i in order)}]}}',
            f'def {label}Requests : List (NodeDecl × GroupScopedEval.Request × List (Nat × Tid)) := [', ',\n'.join(table), ']',
            f'def {label}Scope (n : NodeDecl) : GroupScopedEval.Request :=',
            f'  match {label}Requests.find? (fun row => row.1 == n) with', '  | some row => row.2.1', '  | none => .group none',
            f'def {label}Peers (n : NodeDecl) (r : Nat) : Tid :=',
            f'  match {label}Requests.find? (fun row => row.1 == n) with',
            '  | some row => ((row.2.2.find? (fun p => p.1 == r)).map Prod.snd).getD 0', '  | none => 0',
            f'def {label}Denote (s : Store) : Option Store := SourceScopedEval.denote {label}Graph {label}Scope {label}Peers s'])
    lines.extend(['end', 'end TrainVerify.Denote.RuntimeWorld', ''])
    return WorldDefinitions('\n'.join(lines), dict(**counts, fullrefs=refs, missing=missing,
        execution_order=execution_order, execution_order_policy="source-rank-control/fullref-producer/stable-kahn",
        execution_complete=False, public_complete=False, proof_admissible=False,
        source_only=True, source_defined_operations_are_torch_refinement=False,
        later_blockers=['input-adapter-unproved', 'scoped-dependent-chain/public-adapter-unproved', 'DP-value-decomposition-unproved']))


def publish(artifact, out):
    """Reuse canonical fresh-only staged directory publication."""
    from Verdict import graph_to_lean as c
    out = Path(out)
    if out.suffix != '.lean': raise ValueError('world definitions require a .lean destination')
    receipt = artifact.receipt
    if (artifact.supporting_sources or 'proof_bundle' in receipt
            or artifact.lean.startswith(f'import {WORLD_DATA_MODULE}\n')):
        from trainverify.batch_source_authority import _same_handoff_data
        if out.name == WORLD_DATA_FILE or out.stem.startswith('TrainVerifyRuntimePrefix'):
            raise ValueError('world entry collides with reserved data module')
        expected = _proof_bundle(artifact.lean, artifact.supporting_sources)
        if not _same_handoff_data(receipt.get('proof_bundle'), expected):
            raise ValueError('world bundle source inventory mismatch')
        receipt = dict(receipt, proof_bundle=_proof_bundle(artifact.lean, artifact.supporting_sources, out.name))
    c._validate_definitions_only_destination(out)
    out.parent.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='trainverify-world-', dir=out.parent.parent) as staging:
        root = Path(staging)
        (root / out.name).write_text(artifact.lean, encoding='utf-8')
        for name, text in artifact.supporting_sources.items():
            (root / name).write_text(text, encoding='utf-8')
        (root / 'world-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
        c._validate_generated_authority_tree(root)
        if 'proof_bundle' in receipt:
            sources = {out.name: artifact.lean, **artifact.supporting_sources}
            if {p.name for p in root.iterdir()} != set(sources) | {'world-receipt.json'}:
                raise ValueError('staged world bundle membership mismatch')
            if any((root/name).read_text(encoding='utf-8') != text for name, text in sources.items()):
                raise ValueError('staged world bundle source mismatch')
            if (root/'world-receipt.json').read_text() != json.dumps(receipt, indent=2) + '\n':
                raise ValueError('staged world bundle receipt mismatch')
        c._validate_definitions_only_destination(out)
        c._atomic_publish_generated_directory(root, out.parent)
