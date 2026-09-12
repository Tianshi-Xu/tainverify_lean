"""Maximal contiguous computed prefixes of the authenticated full input schedule.

Only unwritten raw parameter shapes are premises. Values are computed from the
actual feeds and arbitrary initial weights, in one Store chain. Unsupported nodes
are frontiers, never skipped. Small read/value-shape lemmas bound elaboration.
"""
from math import prod
from dataclasses import dataclass
from Verdict.runtime_lineage import _Index


PROOF_BYTE_BUDGET = 40000
PROOF_DECLARATION_BUDGET = 80
# Bound fold elaboration independently of graph, operator and packing budgets.
RUN_STEP_BUDGET = 16
PREFIX_MODULE = 'TrainVerifyRuntimePrefix'
SUPPORT_MODULE = PREFIX_MODULE + 'Support'
SUPPORT_FILE = SUPPORT_MODULE + '.lean'
NAMES_V3_MODULE = 'TrainVerifyRuntimePrefixNamesV3'
NAMES_V3_FILE = NAMES_V3_MODULE + '.lean'
_NAMES_V3_IMPORT = f'import {NAMES_V3_MODULE}\n'
_QUALIFIED_HELPER = 'AllToAllSourceFaithful.localStep'


# These aliases are syntax only: Lean restores the original identifiers before
# elaborating each command. Public names, types, proof terms and opacity agree.
_NAME_CODES: dict[str, str] = dict(zip(
    ('State', 'Value', 'Read', 'Written', 'Shape', 'Skip', 'Step', 'NoWrite',
     'Guard', 'InitialShape', 'InitialRead', 'Requests', 'Run'),
    ('s', 'v', 'r', 'w', 'h', 'k', 't', 'n', 'g', 'i', 'e', 'q', 'u')))


_LOCAL_CODES = {'init': 'z', 'hInitShapes': 'z_'}
# The single '+' vocabulary is frozen; '+ +' adds only these two enums.
_HELPER_CODES = {'prefixRead': 'pR', 'storeSet_eq_of_not_mem_fst': 'pS',
                 'prefixFrame_trans': 'pF'}

def compact_names(text, *, names_v3=True):
    import re
    # The generated prefix subset has no quoted identifiers, strings or block
    # comments. Keep other Lean source forms unchanged rather than lex them badly.
    if any(token in text for token in ('"', '«', '`', '/-', 'prefix_names ', '#a')):
        return text
    if 'prefix_names_v' in text or NAMES_V3_MODULE in text:
        return text
    # Only the exact native query spelling is reversible without a side table.
    # Preserve indentation, trailing whitespace, qualified names and line endings;
    # any other #print form (including one in a comment) rejects the whole source.
    queries = re.compile(r"^([ \t]*)#print axioms ([^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*)([ \t]*\r?$)", re.M)
    query_count = len(queries.findall(text))
    if text.count('#print') != query_count:
        return text
    tokens = re.compile(r"--[^\n]*|[^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*")
    pattern = re.compile(r'([A-Za-z][A-Za-z_0-9]*Prefix)(' +
                         '|'.join(_NAME_CODES) + r')_([0-9]+(?:_[0-9]+)*)\Z')
    short = re.compile(r'[' + ''.join(_NAME_CODES.values()) + r']_[0-9]+(?:_[0-9]+)*\Z')
    identifiers = [m[0] for m in tokens.finditer(text) if not m[0].startswith('--')]
    names = {name: pattern.fullmatch(name) for name in identifiers}
    stems = {m[1] for m in names.values() if m is not None}
    if len(stems) != 1 or any(short.fullmatch(name) or name in _LOCAL_CODES.values()
                              or name in _HELPER_CODES.values() for name in identifiers):
        return text
    stem, = stems
    helpers_used = False
    helpers_v2 = False
    imports = re.findall(r'^(?:import [^\n]+\n)*', text)[0]
    qualified = names_v3 and any(m[0] == _QUALIFIED_HELPER for m in tokens.finditer(text[len(imports):]))
    if qualified and 'pL' in identifiers:
        return text
    def replace(m):
        nonlocal helpers_used, helpers_v2
        helpers_used |= m[0] in _HELPER_CODES
        helpers_v2 |= m[0] in _HELPER_CODES and m[0] != 'prefixRead'
        if qualified and m[0] == _QUALIFIED_HELPER:
            return 'pL'
        found = names.get(m[0])
        return _NAME_CODES[found[2]] + '_' + found[3] if found else _LOCAL_CODES.get(m[0], _HELPER_CODES.get(m[0], m[0]))
    body = tokens.sub(replace, text[len(imports):])
    body = queries.sub(lambda m: m[1] + '#a ' + m[2] + m[3], body)
    first = next((line for line in body.splitlines() if line.strip()), '')
    if first[:1].isspace():
        return text
    marker = ' +' if helpers_used else ''
    if helpers_v2:
        marker += ' +'
    if query_count:
        marker += ' !'
    wrapper = 'prefix_names_v3' if qualified else 'prefix_names'
    compact = imports + (_NAMES_V3_IMPORT if qualified else '') + f'{wrapper} {stem}{marker} where\n' + ''.join(
        ' ' + line if line.strip() else line for line in body.splitlines(keepends=True))
    return compact if len(compact.encode()) < len(text.encode()) else text


def expand_names(text):
    """Recover canonical source for inventories and independent byte comparisons.

    This does not implement the proof: Lean independently transforms parsed
    identifiers in runtime_prefix_support.lean. The source scanner is unchanged.
    """
    import re
    header = re.search(r'^prefix_names(?:_v3)? ([A-Za-z][A-Za-z_0-9]*)( \+( \+)?)?( !)? where\n', text, re.M)
    first_marker = re.search(r'^prefix_names(?:_v\w*)?\b', text, re.M)
    if first_marker and (header is None or first_marker.start() != header.start()):
        raise ValueError('invalid compact prefix header')
    if header is None:
        return text
    qualified = header[0].startswith('prefix_names_v3 ')
    preamble = text[:header.start()]
    if qualified:
        # The encoder appends exactly one owned import immediately before the
        # wrapper. Never remove a caller import from any other source shape.
        if not preamble.endswith(_NAMES_V3_IMPORT) or preamble.count(_NAMES_V3_IMPORT) != 1:
            raise ValueError('invalid compact prefix v3 import')
        preamble = preamble[:-len(_NAMES_V3_IMPORT)]
    lines = text[header.end():].splitlines(keepends=True)
    stop = next((i for i, line in enumerate(lines) if line.strip() and not line[0].isspace()), len(lines))
    block, suffix = lines[:stop], ''.join(lines[stop:])
    # Keep the historical two-space wrapper readable; only the outer offset
    # changes. All original relative indentation and source bytes are restored.
    first = next((line for line in block if line.strip()), '')
    indent = len(first) - len(first.lstrip(' '))
    if indent not in (1, 2) or any(line.strip() and not line.startswith(' ' * indent) for line in block):
        raise ValueError('invalid compact prefix indentation')
    body = ''.join(line[indent:] if line.strip() else line for line in block)
    if header[4]:
        body = re.sub(r'^([ \t]*)#a ', r'\1#print axioms ', body, flags=re.M)
    families = {code: name for name, code in _NAME_CODES.items()}
    locals_ = {code: name for name, code in _LOCAL_CODES.items()}
    helpers = {code: name for name, code in _HELPER_CODES.items()
               if header[3] or name == 'prefixRead'} if header[2] else {}
    pattern = re.compile(r'([' + ''.join(families) + r'])_([0-9]+(?:_[0-9]+)*)\Z')
    def replace(m):
        if qualified and m[0] == 'pL':
            return _QUALIFIED_HELPER
        short = pattern.fullmatch(m[0])
        return header[1] + families[short[1]] + '_' + short[2] if short else locals_.get(m[0], helpers.get(m[0], m[0]))
    return preamble + re.sub(r"--[^\n]*|[^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*", replace, body) + expand_names(suffix)


def support_source():
    from pathlib import Path
    return Path(__file__).with_name('runtime_prefix_support.lean').read_text(encoding='utf-8')

def names_v3_source():
    from pathlib import Path
    return Path(__file__).with_name('runtime_prefix_names_v3.lean').read_text(encoding='utf-8')


_HEADER = '\n'.join(['namespace TrainVerify.Denote.RuntimeWorld',
    'noncomputable section', 'open SourceScopedEval',
    'set_option maxHeartbeats 500000', 'set_option maxRecDepth 4096']) + '\n'
_FOOTER = '\nend\nend TrainVerify.Denote.RuntimeWorld\n'


@dataclass(frozen=True)
class ProofGroup:
    """An indivisible initializer, node proof, or final assembly declaration group."""
    text: str
    declarations: int
    opaque: tuple
    final: bool = False


def pack_proofs(prefixes, *, names_v3=False):
    """Maximal sequential packing; every edge imports the actual prior chain.

    V3 is opt-in: legacy/default bundles also contain localStep and must retain
    their exact bytes. The caller chooses whether to enable the new vocabulary.
    Budgets cover declaration bodies (import/local-attribute scaffolding is not
    a declaration). A single oversized group is an error, never split by syntax.
    """
    from Verdict.runtime_world import WORLD_DATA_MODULE
    imports = f'import {WORLD_DATA_MODULE}\nimport denote.SourceScopedPrefix\nimport {SUPPORT_MODULE}\n'
    groups = [g for prefix in prefixes for g in prefix]
    def fits(gs):
        return (sum(len(g.text.encode('utf-8')) for g in gs) <= PROOF_BYTE_BUDGET
                and sum(g.declarations for g in gs) <= PROOF_DECLARATION_BUDGET)
    if any(not fits([g]) for g in groups):
        raise ValueError('prefix atomic declaration group exceeds proof budget')
    supporting = {SUPPORT_FILE: support_source()}
    def compact(text):
        encoded = compact_names(text, names_v3=names_v3)
        if encoded != text and _NAMES_V3_IMPORT in encoded:
            supporting[NAMES_V3_FILE] = names_v3_source()
        return encoded
    if fits(groups):
        return compact(imports + _HEADER + '\n'.join(g.text for g in groups) + _FOOTER), supporting
    chunks = []; current = []; finals = []
    for g in groups:
        if g.final:
            finals.append(g)
            continue
        if current and not fits(current + [g]):
            chunks.append(current); current = []
        current.append(g)
    if current: chunks.append(current)
    if not fits(finals):
        raise ValueError('prefix final assembly exceeds proof budget')
    previous = None
    def source(gs):
        edge = f'import {previous}\n' if previous else ''
        attrs = 'restore_prefix_opacity\n' if previous else ''
        # Metadata is not the immediate attribute stream: preserve both exactly.
        opaque = [n for g in gs for n in g.opaque]
        record = '\nrecord_prefix_opacity ' + ' '.join(opaque) + '\n' if opaque else ''
        return compact(imports + edge + _HEADER + attrs + '\n'.join(g.text for g in gs) + record + _FOOTER)
    for index, chunk in enumerate(chunks):
        name = f'{PREFIX_MODULE}{index:04d}'
        supporting[name+'.lean'] = source(chunk)
        previous = name
    return source(finals), supporting


class PrefixUnavailable(ValueError):
    def __init__(self, reason, **details):
        super().__init__(reason)
        self.details = dict(status='prefix-proof-unavailable', reason=reason, **details)


def render(label, view, raw, world, loaders, *, structured=False, seed_inventories=None, internal_multiref=None):
    """Called after bind's canonical world and raw/feed authentication."""
    order = world.receipt['execution_order'][label]['execution_to_source']
    if not any(str(view.node_opname(view.nodes()[i])).split('.')[-1]
               in ('AllToAllPrim', 'CROSS_DP_WRED') for i in order):
        from Verdict.runtime_ordinary_fold import render as render_ordinary
        return render_ordinary(label, view, world, loaders, structured=structured,
                               seeded=seed_inventories is not None)
    from Verdict.runtime_multiref_authority import InternalEdges
    authorized_multirefs = (internal_multiref.validate(view)
        if isinstance(internal_multiref, InternalEdges) else set())
    index = _Index(view, raw)
    feeds = {row['index']: row for row in loaders if row['world'] == label}
    missing = {row['index']: row['reason'] for row in world.receipt['missing'] if row['world'] == label}
    seeds = None if seed_inventories is None else seed_inventories[label]
    seed_ids = {} if seeds is None else {row['tid']: q for q, row in enumerate(seeds)}
    shapes = {tid: [1] for tid in seed_ids}; initial = {}; rows = []; frontier = None
    # Only authenticated integer feeds and value-preserving descendants qualify
    # as IDs. No real-valued activation or initial parameter receives this fact.
    integer_ids = set()
    # Commit each node's inferred shapes/premises only after all checks succeed.
    for j, i in enumerate(order):
        n = view.nodes()[i]; op = str(view.node_opname(n)).split('.')[-1]
        ins = view.node_inputs(n); outs = view.node_outputs(n)
        ss = dict(shapes); ii = dict(initial)
        try:
            if op == 'BW_sum' and seeds is not None:
                if (len(ins) != 2 or len(outs) != 1
                        or ins[0].tid not in seed_ids
                        or ins[1].tid not in {t.tid for row in rows for t in row['outs']}
                        or list(n) != seeds[seed_ids[ins[0].tid]]['consumer']
                        or dict(view.node_kwargs(n)) not in ({}, {'__consts': []})):
                    raise PrefixUnavailable('unsupported-seed-sum-contract', op=op)
            elif op == 'BW_multiref' and seeds is not None:
                if tuple(n) not in authorized_multirefs:
                    raise PrefixUnavailable('missing-internal-autograd-edge-authority', op=op)
                from Verdict import graph_to_lean as c
                from Verdict.runtime_world import _ordinary
                params, reason = _ordinary(view, n, c._get_node_params)
                if reason or params or dict(view.node_kwargs(n)) not in ({}, {'__consts': []}):
                    raise PrefixUnavailable(reason or 'unsupported-producer-schema', op=op)
                computed = {t.tid for row in rows for t in row['outs']}
                if any(t.tid not in computed for t in ins):
                    raise PrefixUnavailable('unsupported-producer-input', op=op)
            elif op in ('BW_linear', 'BW_layernorm', 'BW_add', 'BW_gelu', 'BW_view', 'BW_contiguous', 'BW_transpose', 'BW_matmul', 'BW_softmax', 'BW_div', 'BW_embedding') and seeds is not None:
                from Verdict import graph_to_lean as c
                from Verdict.runtime_world import _ordinary
                _, reason = _ordinary(view, n, c._get_node_params)
                arity = (3, 1) if op == 'BW_embedding' else (4, 3) if op == 'BW_layernorm' else (2, 1) if op in ('BW_gelu', 'BW_view', 'BW_contiguous', 'BW_transpose', 'BW_softmax', 'BW_div') else (3, 2)
                if reason or (len(ins), len(outs)) != arity or len({t.tid for t in outs}) != len(outs):
                    raise PrefixUnavailable(reason or 'unsupported-producer-schema', op=op)
            elif op == 'CROSS_DP_WRED':
                computed = {t.tid for row in rows for t in row['outs']}
                if any(t.tid not in computed for t in ins):
                    raise PrefixUnavailable('unsupported-producer-input', op=op)
            elif op not in ('DATALOADER', 'FW_embedding', 'ChunkPrim', 'AllToAllPrim', 'FW_add', 'FW_multiref', 'FW_layernorm', 'FW_linear', 'AllGatherPrim', 'FW_view', 'FW_reshape', 'FW_transpose', 'FW_matmul', 'FW_div', 'FW_softmax', 'FW_contiguous', 'FW_gelu', 'FW_sum', 'ReduceScatterPrim', 'AllReducePrim'):
                raise PrefixUnavailable('unsupported-producer', op=op)
            if i in missing and op != 'DATALOADER':
                raise PrefixUnavailable(missing[i], op=op)
            if not outs or (op == 'FW_embedding' and (len(ins) != 2 or len(outs) != 1)) or (op == 'FW_add' and (len(ins) not in (1, 2) or len(outs) != 1)) or (op == 'FW_multiref' and (len(ins) != 1 or view.node_kwargs(n).get('times', len(outs)) != len(outs))):
                raise PrefixUnavailable('unsupported-producer-schema', op=op)
            for port, t in enumerate(ins):
                if t.tid not in ss:
                    ref = tuple(view.source_tensor(t))
                    if port not in {'FW_embedding': (1,), 'FW_layernorm': (1, 2), 'FW_linear': (1,)}.get(op, ()) or ref in index.writers:
                        raise PrefixUnavailable('unsupported-producer-input', tid=t.tid, op=op)
                    ep = index.endpoint(ref, 'initial'); meta = index.meta.get(ref)
                    if not meta or not meta[4] or meta[5]:
                        raise PrefixUnavailable('unauthorized-initial-weight', tid=t.tid)
                    ii[t.tid] = dict(tid=t.tid, ref=list(ref), shape=list(ep.shape), authority='unwritten-raw-parameter')
                    ss[t.tid] = list(ep.shape)
            scope = None; params = None
            if op == 'DATALOADER':
                if i not in feeds: raise PrefixUnavailable('missing-feed')
                output_shapes = [p['shape'] for p in feeds[i]['ports']]
            elif op == 'FW_embedding':
                output_shapes = [ss[ins[0].tid] + [ss[ins[1].tid][-1]]]
            elif op in ('ChunkPrim', 'AllToAllPrim', 'ReduceScatterPrim'):
                scope = (view.chunk_scopes if op == 'ChunkPrim' else view.collective_scopes)[n]
                rs = list(scope.ranks); sh = ss[ins[0].tid].copy()
                dim, odim = (scope.dim, scope.dim) if op == 'ChunkPrim' else ((scope.params[0], scope.params[0]) if op == 'ReduceScatterPrim' else scope.params)
                if (len(outs) != 1 or len(ins) != (1 if op == 'ChunkPrim' else len(rs)) or
                        any(ss[t.tid] != sh for t in ins) or max(dim, odim) >= len(sh) or
                        sh[odim] <= 0 or sh[odim] % len(rs)):
                    raise PrefixUnavailable('chunk-shape-contract' if op == 'ChunkPrim' else 'reducescatter-shape-contract' if op == 'ReduceScatterPrim' else 'alltoall-shape-contract', computed_shapes=[ss[t.tid] for t in ins])
                sh[odim] //= len(rs)
                if op == 'AllToAllPrim': sh[dim] *= len(rs)
                output_shapes = [sh]
            elif op == 'CROSS_DP_WRED':
                scope = view.wred_scopes[n]
                if (len(outs) != 1 or not ins or len(ins) != len(scope.ranks)
                        or any(ss[t.tid] != ss[ins[0].tid] for t in ins)):
                    raise PrefixUnavailable('wred-shape-contract')
                output_shapes = [ss[ins[0].tid].copy()]
            elif op == 'AllReducePrim':
                scope = view.collective_scopes[n]
                if (len(outs) != 1 or not ins or len(ins) != len(scope.ranks)
                        or scope.params or not 0 <= scope.local_index < len(scope.ranks)
                        or any(ss[t.tid] != ss[ins[0].tid] for t in ins)):
                    raise PrefixUnavailable('allreduce-shape-contract')
                output_shapes = [ss[ins[0].tid].copy()]
            elif op == 'AllGatherPrim':
                scope = view.collective_scopes[n]
                sh = ss[ins[0].tid].copy(); dim, = scope.params
                if (len(outs) != 1 or len(ins) != len(scope.ranks) or dim >= len(sh)
                        or any(ss[t.tid] != sh for t in ins)):
                    raise PrefixUnavailable('allgather-shape-contract')
                sh[dim] *= len(scope.ranks)
                output_shapes = [sh]
            elif op in ('FW_view', 'FW_reshape', 'FW_transpose'):
                from Verdict import graph_to_lean as c
                from Verdict.runtime_world import _ordinary
                params, reason = _ordinary(view, n, c._get_node_params)
                if reason or len(ins) != 1 or len(outs) != 1:
                    raise PrefixUnavailable(reason or 'unsupported-producer-schema')
                sh = ss[ins[0].tid]
                if op == 'FW_transpose':
                    if len(params) != 2 or any(d >= len(sh) for d in params):
                        raise PrefixUnavailable('layout-axis-contract')
                    target = sh.copy(); a, b = params
                    target[a], target[b] = target[b], target[a]
                else:
                    # Lowering uses output metadata; independently validate the
                    # literal source request, never infer it from that metadata.
                    kw = view.node_kwargs(n)
                    keys = [key for key in ('size', 'shape') if key in kw]
                    if len(keys) != 1 or (op == 'FW_view' and keys != ['size']):
                        raise PrefixUnavailable('layout-source-params')
                    requested = kw[keys[0]]
                    if not isinstance(requested, (tuple, list)) or not requested or any(type(d) is not int or d < -1 for d in requested) or requested.count(-1) > 1:
                        raise PrefixUnavailable('layout-source-params')
                    target = list(requested)
                    if -1 in target:
                        known = prod(d for d in target if d != -1)
                        if known <= 0 or prod(sh) % known:
                            raise PrefixUnavailable('layout-product-contract')
                        target[target.index(-1)] = prod(sh) // known
                    if prod(target) != prod(sh):
                        raise PrefixUnavailable('layout-product-contract')
                    if target != params:
                        raise PrefixUnavailable('layout-source-params')
                output_shapes = [target]
            elif op in ('FW_matmul', 'FW_div', 'FW_softmax'):
                from Verdict import graph_to_lean as c
                from Verdict.runtime_world import _ordinary
                params, reason = _ordinary(view, n, c._get_node_params)
                if reason:
                    raise PrefixUnavailable(reason)
                sh = ss[ins[0].tid]
                if op == 'FW_matmul':
                    other = ss[ins[1].tid]
                    # Denote indexes both operands with the same flat batch
                    # offset. Broadcasting (even singleton batches) is not its
                    # semantics. Infer only from computed operand shapes.
                    if (len(sh) not in (2, 3, 4) or len(other) != len(sh)
                            or sh[:-2] != other[:-2] or sh[-1] != other[-2]):
                        raise PrefixUnavailable('matmul-shape-contract', computed_shapes=[sh, other])
                    output_shapes = [sh[:-1] + [other[-1]]]
                else:
                    if op == 'FW_softmax' and (not sh or sh[-1] <= 0):
                        raise PrefixUnavailable('softmax-shape-contract')
                    output_shapes = [sh]
            elif op == 'BW_embedding':
                from Verdict import graph_to_lean as c
                from Verdict.runtime_world import _ordinary
                params, _ = _ordinary(view, n, c._get_node_params)
                computed = {t.tid for row in rows for t in row['outs']}
                if any(t.tid not in computed for t in ins[:2]):
                    raise PrefixUnavailable('unsupported-producer-input', op=op)
                grad, ids, weight = (ss[t.tid] for t in ins)
                kw = dict(view.node_kwargs(n))
                if (set(kw) - {'start', 'stop', 'padding_idx', '__consts'}
                        or type(kw.get('start')) is not int or kw['start'] != 0
                        or type(kw.get('stop')) is not int
                        or kw.get('padding_idx') is not None
                        or kw.get('__consts', []) != [] or params):
                    raise PrefixUnavailable('bw-embedding-source-params')
                if (len(weight) != 2 or min(weight) <= 0 or kw['stop'] != weight[0]
                        or grad != ids + [weight[1]]):
                    raise PrefixUnavailable('bw-embedding-shape-contract', computed_shapes=[grad, ids, weight])
                if ins[1].tid not in integer_ids:
                    raise PrefixUnavailable('bw-embedding-index-domain')
                output_shapes = [weight.copy()]
            elif op == 'BW_div':
                # Source ports remain [g, original x], although bw_div uses g.
                # Neither operand may be replaced by an initial shape premise.
                from Verdict import graph_to_lean as c
                from Verdict.runtime_world import _ordinary
                params, _ = _ordinary(view, n, c._get_node_params)
                computed = {t.tid for row in rows for t in row['outs']}
                if any(t.tid not in computed for t in ins):
                    raise PrefixUnavailable('unsupported-producer-input', op=op)
                grad, sh = (ss[t.tid] for t in ins)
                kw = dict(view.node_kwargs(n)); consts = kw.get('__consts', [])
                if (set(kw) - {'rounding_mode', '__consts'} or kw.get('rounding_mode') is not None
                        or not isinstance(consts, (list, tuple)) or len(consts) != 1
                        or type(consts[0]) not in (int, float) or not consts[0] > 0
                        or params != [consts[0]] or any(type(p) is not int for p in params)):
                    raise PrefixUnavailable('bw-div-source-params')
                if grad != sh:
                    raise PrefixUnavailable('bw-div-shape-contract', computed_shapes=[grad, sh])
                output_shapes = [sh.copy()]
            elif op == 'BW_softmax':
                # Raw BW ports are [g, original FW input x], NOT [g, y].
                # Denote recomputes softmax(x) before the weighted row reduction.
                computed = {t.tid for row in rows for t in row['outs']}
                if any(t.tid not in computed for t in ins):
                    raise PrefixUnavailable('unsupported-producer-input', op=op)
                grad, sh = (ss[t.tid] for t in ins)
                kw = dict(view.node_kwargs(n)); dim = kw.get('dim')
                if (set(kw) - {'dim', 'dtype', '__consts'} or kw.get('dtype') is not None
                        or kw.get('__consts', []) != [] or type(dim) is not int
                        or not sh or not -len(sh) <= dim < len(sh)
                        or (dim + len(sh) if dim < 0 else dim) != len(sh)-1):
                    raise PrefixUnavailable('bw-softmax-source-params')
                if sh[-1] <= 0 or grad != sh:
                    raise PrefixUnavailable('bw-softmax-shape-contract', computed_shapes=[grad, sh])
                output_shapes = [sh.copy()]
            elif op == 'BW_matmul':
                # batchedMatmulBwd uses a shared flat batch offset, not Torch
                # broadcasting. All three values must come from earlier steps.
                computed = {t.tid for row in rows for t in row['outs']}
                if any(t.tid not in computed for t in ins):
                    raise PrefixUnavailable('unsupported-producer-input', op=op)
                if dict(view.node_kwargs(n)) not in ({}, {'__consts': []}):
                    raise PrefixUnavailable('bw-matmul-source-params')
                grad, sh, other = (ss[t.tid] for t in ins)
                if (len(sh) not in (2, 3, 4) or len(other) != len(sh)
                        or sh[:-2] != other[:-2] or sh[-1] != other[-2]
                        or grad != sh[:-1] + [other[-1]]):
                    raise PrefixUnavailable('bw-matmul-shape-contract', computed_shapes=[grad, sh, other])
                output_shapes = [sh.copy(), other.copy()]
            elif op == 'BW_transpose':
                from Verdict import graph_to_lean as c
                from Verdict.runtime_world import _ordinary
                params, _ = _ordinary(view, n, c._get_node_params)
                computed = {t.tid for row in rows for t in row['outs']}
                if any(t.tid not in computed for t in ins):
                    raise PrefixUnavailable('unsupported-producer-input', op=op)
                grad, sh = (ss[t.tid] for t in ins)
                kw = view.node_kwargs(n)
                axes = [kw.get('dim0'), kw.get('dim1')]
                if (not sh or any(type(d) is not int or not -len(sh) <= d < len(sh) for d in axes)):
                    raise PrefixUnavailable('bw-transpose-source-params')
                axes = [d + len(sh) if d < 0 else d for d in axes]
                if params != axes:
                    raise PrefixUnavailable('bw-transpose-source-params')
                target = sh.copy(); a, b = axes
                target[a], target[b] = target[b], target[a]
                if grad != target:
                    raise PrefixUnavailable('bw-transpose-shape-contract', computed_shapes=[grad, sh])
                output_shapes = [sh.copy()]
            elif op == 'BW_contiguous':
                # Dense logical gradient values only; x is still a computed read.
                computed = {t.tid for row in rows for t in row['outs']}
                if any(t.tid not in computed for t in ins):
                    raise PrefixUnavailable('unsupported-producer-input', op=op)
                grad, sh = (ss[t.tid] for t in ins)
                if dict(view.node_kwargs(n)) not in ({}, {'__consts': []}):
                    raise PrefixUnavailable('bw-contiguous-source-params')
                if grad != sh:
                    raise PrefixUnavailable('bw-contiguous-shape-contract', computed_shapes=[grad, sh])
                output_shapes = [sh.copy()]
            elif op == 'BW_view':
                # Backward kwargs retain the ORIGINAL forward shape request.
                # Lowered params instead encode the inverse output shape. Neither
                # is authority for x: both operands must already be computed.
                from Verdict import graph_to_lean as c
                from Verdict.runtime_world import _ordinary
                params, _ = _ordinary(view, n, c._get_node_params)
                computed = {t.tid for row in rows for t in row['outs']}
                if any(t.tid not in computed for t in ins):
                    raise PrefixUnavailable('unsupported-producer-input', op=op)
                grad, sh = (ss[t.tid] for t in ins)
                kw = view.node_kwargs(n)
                requested = kw.get('size')
                if ('shape' in kw or not isinstance(requested, (tuple, list))
                        or not requested or any(type(d) is not int or d < -1 for d in requested)
                        or requested.count(-1) > 1):
                    raise PrefixUnavailable('bw-view-source-params')
                target = list(requested)
                if -1 in target:
                    known = prod(d for d in target if d != -1)
                    if known <= 0 or prod(sh) % known:
                        raise PrefixUnavailable('bw-view-product-contract')
                    target[target.index(-1)] = prod(sh) // known
                if prod(sh) != prod(grad) or prod(target) != prod(sh):
                    raise PrefixUnavailable('bw-view-product-contract')
                if target != grad:
                    raise PrefixUnavailable('bw-view-source-params')
                if params != sh:
                    raise PrefixUnavailable('computed-source-shape-mismatch')
                output_shapes = [sh.copy()]
            elif op == 'BW_sum':
                output_shapes = [ss[ins[1].tid]]
            elif op == 'FW_sum':
                # Denote's existing full-reduction scalar representation.
                output_shapes = [[1]]
            elif op in ('FW_contiguous', 'FW_gelu'):
                output_shapes = [ss[ins[0].tid]]
            elif op == 'BW_multiref':
                sh = ss[ins[0].tid]
                if any(ss[t.tid] != sh for t in ins):
                    raise PrefixUnavailable('bw-multiref-shape-contract', computed_shapes=[ss[t.tid] for t in ins])
                output_shapes = [sh.copy()]
            elif op == 'BW_gelu':
                grad, sh = (ss[t.tid] for t in ins)
                if grad != sh:
                    raise PrefixUnavailable('bw-gelu-shape-contract', computed_shapes=[grad, sh])
                output_shapes = [sh.copy()]
            elif op == 'BW_add':
                grad, sh, other = (ss[t.tid] for t in ins)
                size = max(len(sh), len(other))
                aligned = list(zip([1]*(size-len(sh))+sh, [1]*(size-len(other))+other))
                if (any(a <= 0 or b <= 0 or (a != b and a != 1 and b != 1) for a, b in aligned)
                        or grad != [max(a, b) for a, b in aligned]):
                    raise PrefixUnavailable('bw-add-broadcast-contract', computed_shapes=[grad, sh, other])
                output_shapes = [sh.copy(), other.copy()]
            elif op == 'BW_layernorm':
                grad, sh, gamma, beta = (ss[t.tid] for t in ins)
                if (len(sh) not in (2, 3) or sh[-1] <= 0 or grad != sh
                        or gamma != [sh[-1]] or beta != [sh[-1]]):
                    raise PrefixUnavailable('bw-layernorm-shape-contract',
                                            computed_shapes=[grad, sh, gamma, beta])
                output_shapes = [sh.copy(), gamma.copy(), beta.copy()]
            elif op == 'BW_linear':
                grad, sh, weight = (ss[t.tid] for t in ins)
                if (len(sh) not in (2, 3) or len(weight) != 2
                        or sh[-1] != weight[1] or grad != sh[:-1] + [weight[0]]):
                    raise PrefixUnavailable('bw-linear-shape-contract',
                                            computed_shapes=[grad, sh, weight])
                output_shapes = [sh.copy(), weight.copy()]
            elif op == 'FW_linear':
                sh, weight = (ss[t.tid] for t in ins)
                if len(sh) not in (2, 3) or len(weight) != 2 or sh[-1] != weight[1]:
                    raise PrefixUnavailable('linear-shape-contract')
                output_shapes = [sh[:-1] + [weight[0]]]
            elif op == 'FW_layernorm':
                sh = ss[ins[0].tid]
                if not sh or any(ss[t.tid] != [sh[-1]] for t in ins[1:]):
                    raise PrefixUnavailable('layernorm-shape-contract')
                output_shapes = [sh]
            elif op == 'FW_add':
                sh = ss[ins[0].tid]
                if len(ins) == 2:
                    other = ss[ins[1].tid]; size = max(len(sh), len(other))
                    sh = [max(a, b) for a, b in zip([1]*(size-len(sh))+sh, [1]*(size-len(other))+other)]
                output_shapes = [sh]
            else:
                output_shapes = [ss[ins[0].tid]] * len(outs)
            for t, sh in zip(outs, output_shapes):
                if sh != list(view.tensor_shape(t)):
                    raise PrefixUnavailable('computed-source-shape-mismatch', tid=t.tid, computed_shape=sh, source_shape=list(view.tensor_shape(t)))
                ss[t.tid] = sh
            ids_preserved = (op in ('ChunkPrim', 'FW_contiguous', 'FW_view', 'FW_reshape', 'FW_transpose', 'FW_multiref')
                             and ins[0].tid in integer_ids)
            integer_ids.difference_update(t.tid for t in outs)
            if op == 'DATALOADER':
                integer_ids.update(p['tid'] for p in feeds[i]['ports']
                                   if all(type(v) is int and v >= 0 for v in p['values']))
            elif ids_preserved:
                integer_ids.update(t.tid for t in outs)
            rows.append(dict(index=i, op=op, ins=ins, outs=outs, scope=scope,
                             input_shapes=[ss[t.tid] for t in ins], output_shapes=output_shapes, params=params))
            shapes, initial = ss, ii
        except PrefixUnavailable as exc:
            frontier = dict(exc.details, index=i, source_index=i, execution_index=j, op=op)
            break
    if not any(r['op'] in ('AllToAllPrim', 'CROSS_DP_WRED') for r in rows):
        return '', dict(frontier or dict(status='prefix-proof-unavailable', reason='no-supported-guard'),
                        prefix_nodes=[r['index'] for r in rows], frontier=frontier,
                        whole_world_option_success=False)
    return _render(label, rows, feeds, initial, frontier, structured=structured, seeds=seeds)


def _render(label, rows, feeds, initial, frontier, *, structured=False, seeds=None):
    stem = label + ('Prefix' if seeds is None else 'SeededPrefix'); lines = []; names = []; guards = []; steps = []
    groups = []; definitions = []; opaque = []; group_start = 0
    def definition(text):
        definitions.append(text)
        lines.append(text)
    def group(final=False):
        nonlocal group_start
        groups.append(ProofGroup('\n'.join(lines), len(definitions) + len(names) - group_start,
                                 tuple(opaque), final))
        lines.clear(); definitions.clear(); opaque.clear(); group_start = len(names)
    values = {tid: f'(init {tid})' for tid in initial}; writers = {}; shape_proofs = {}
    seed_ids = {} if seeds is None else {row['tid']: q for q, row in enumerate(seeds)}
    values.update({tid: 'unitSeed' for tid in seed_ids})
    shape_proofs.update({tid: 'unitSeed_shape' for tid in seed_ids})
    initial_store = 'init' if seeds is None else f'({label}InitialWithSeeds init)'
    initial_reads = {}
    read_certificates = {}
    def state(j): return f'({stem}State_{j} init)'
    def theorem(name, args, proof):
        names.append(name)
        lines.extend([f'theorem {name} {args} := {proof}', f'#print axioms {name}'])
    def writes(a, b):
        # Preserve every port in execution order, including duplicate writes.
        # A typed literal avoids hundreds of pending HAppend/OfNat instances.
        return f'({[t.tid for row in rows[a:b] for t in row["outs"]]} : List Tid)'
    def no_write(a, b):
        return f'{stem}Skip_{a}' if b == a + 1 else f'{stem}NoWrite_{a}_{b}'
    def read_intervals(start, end):
        while end > start:
            width = end & -end
            while width > end - start:
                width //= 2
            if width == 2:
                width = 1
            yield end - width, end
            end -= width
    def frame_term(start, end):
        if end - start != 2:
            return f'({no_write(start, end)} init)'
        return f'(prefixFrame_trans _ _ _ _ _ {frame_term(start, start+1)} {frame_term(start+1, end)})'
    certificates = set()
    def certify(start, end):
        if end - start <= 2 or (start, end) in certificates:
            return
        middle = (start + end) // 2
        certify(start, middle); certify(middle, end)
        # Preserve the ordered footprint, including every output and overwrite.
        footprint = writes(start, end)
        theorem(no_write(start, end),
            f'(init : Store) (tid : Tid) (h : tid ∉ {footprint}) : {state(end)} tid = {state(start)} tid',
            f'by\n  exact prefixFrame_trans _ _ _ _ _ {frame_term(start, middle)} {frame_term(middle, end)} tid h')
        group()
        certificates.add((start, end))
    advance = f'(fun row s => stepWithInputs {label}Graph ({label}Scope row.1) ({label}Peers row.1) s row.1 row.2)'
    args = f'(init : Store) (hInitShapes : {stem}InitShapes init)'
    goal = ' ∧ '.join(f'(init {p["tid"]}).shape = {p["shape"]}' for p in initial.values()) or 'True'
    definition(f'def {stem}InitShapes (init : Store) : Prop := {goal}')
    definition(f'def {stem}State_0 (init : Store) : Store := {initial_store}')
    for q, (tid, p) in enumerate(initial.items()):
        name = f'{stem}InitialShape_{q}'
        # InitShapes is the original right-associated conjunction. Project only
        # the demanded component instead of destructing all premises each time.
        projection = 'hInitShapes' + '.2' * q + ('.1' if q < len(initial) - 1 else '')
        theorem(name, f'{args} : (init {tid}).shape = {p["shape"]}',
                f'by\n  exact {projection}')
        shape_proofs[tid] = f'{name} init hInitShapes'
        if seeds is not None:
            read = f'{stem}InitialRead_{q}'
            theorem(read, f'(init : Store) : {state(0)} {tid} = init {tid}',
                f'{label}InitialWithSeeds_frame init {tid} (by decide)')
            initial_reads[tid] = f'{read} init'
            group()
    for tid, q in seed_ids.items():
        initial_reads[tid] = f'{label}InitialWithSeeds_seed_{q} init'
    group()
    for j, row in enumerate(rows):
        i, op, ins, outs, scope = (row[k] for k in ('index','op','ins','outs','scope'))
        node = f'{label}Node_{i}'; prev = state(j); nxt = state(j+1)
        # Emit only demanded intervals, before the unchanged atomic step group.
        for t in ins:
            stop = (read_certificates[t.tid][0] if t.tid in read_certificates else
                    writers[t.tid][0] + 1 if t.tid in writers else 0)
            for start, end in read_intervals(stop, j):
                certify(start, end)
        reads = []
        for p, t in enumerate(ins):
            name = f'{stem}Read_{j}_{p}'; reads.append(f'{name} init')
            stop = writers[t.tid][0] + 1 if t.tid in writers else 0
            anchor = (f'{writers[t.tid][1]} init' if t.tid in writers else
                      initial_reads[t.tid] if seeds is not None else None)
            # Full emitted Tid, and only the current ordered writer version.
            # An overwrite below invalidates this entry, including every port.
            if t.tid in read_certificates:
                stop, anchor = read_certificates[t.tid]
            proof = anchor if anchor is not None else 'rfl'
            for start, end in reversed(list(read_intervals(stop, j))):
                proof = f'prefixRead ({no_write(start, end)} init) ({proof})'
            theorem(name, f'(init : Store) : {prev} {t.tid} = {values[t.tid]}', proof)
            read_certificates[t.tid] = (j, f'{name} init')
        v = [values[t.tid] for t in ins]; actual = [f'({prev} {t.tid})' for t in ins]
        def expressions(xs):
            if op == 'DATALOADER': return [f'{node}_port{p["port"]}' for p in feeds[i]['ports']]
            if op == 'FW_embedding': return [f'fw_embedding {xs[0]} {xs[1]}']
            if op == 'BW_embedding': return [f'bw_embedding {xs[0]} {xs[1]} {xs[2]}']
            if op == 'CROSS_DP_WRED': return [f'cross_dp_wred [{", ".join(xs)}]']
            if op == 'AllReducePrim': return [f'allReducePrim {len(scope.ranks)} {scope.local_index} [{", ".join(xs)}]']
            if op == 'ReduceScatterPrim': return [f'reduceScatterPrimDimN {scope.params[0]} {len(scope.ranks)} {scope.local_index} [{", ".join(xs)}]']
            if op == 'AllGatherPrim': return [f'allGatherPrimDimN {scope.params[0]} {len(scope.ranks)} {scope.local_index} [{", ".join(xs)}]']
            if op == 'BW_view': return [f'fw_view {row["params"]} {xs[0]}']
            if op in ('FW_view', 'FW_reshape'): return [f'fw_view {row["params"]} {xs[0]}']
            if op in ('FW_transpose', 'BW_transpose'): return [f'transposeAxes {row["params"][0]} {row["params"][1]} {xs[0]}']
            if op == 'FW_matmul': return [f'fw_matmul {xs[0]} {xs[1]}']
            if op == 'BW_matmul': return [f'(batchedMatmulBwd {xs[0]} {xs[1]} {xs[2]}).{p}' for p in (1, 2)]
            if op == 'FW_div': return [f'fw_div (({row["params"][0]} : Nat) : Scalar) {xs[0]}']
            if op == 'BW_div': return [f'bw_div (({row["params"][0]} : Nat) : Scalar) {xs[0]}']
            if op == 'BW_sum': return [f'bw_sum {xs[0]} {xs[1]}']
            if op == 'FW_sum': return [f'fw_sum {xs[0]}']
            # Tensor has no storage/stride fields: contiguous is value identity.
            if op in ('FW_contiguous', 'BW_contiguous'): return [xs[0]]
            if op == 'FW_gelu': return [f'fw_gelu {xs[0]}']
            if op == 'FW_softmax': return [f'fw_softmax {xs[0]}']
            if op == 'BW_softmax': return [f'bw_softmax {xs[0]} {xs[1]}']
            if op == 'BW_layernorm': return [f'(bw_layernorm {xs[0]} {xs[1]} {xs[2]} {xs[3]}).{p}' for p in ('1', '2.1', '2.2')]
            if op == 'BW_multiref': return [f'tensorSum [{", ".join(xs)}]']
            if op == 'BW_gelu': return [f'bw_gelu {xs[0]} {xs[1]}']
            if op == 'BW_add': return [f'(bw_add2 {xs[0]} {xs[1]} {xs[2]}).{p}' for p in (1, 2)]
            if op == 'BW_linear': return [f'(bw_linear {xs[0]} {xs[1]} {xs[2]}).{p}' for p in (1, 2)]
            if op == 'FW_linear': return [f'fw_linear {xs[0]} {xs[1]}']
            if op == 'FW_layernorm': return [f'fw_layernorm {xs[0]} {xs[1]} {xs[2]}']
            if op == 'ChunkPrim': return [f'chunkPrimDimN {scope.dim} {len(scope.ranks)} {scope.local_index} {xs[0]}']
            if op == 'AllToAllPrim': return [f'AllToAllSourceFaithful.tensor {len(scope.ranks)} {scope.local_index} {scope.params[0]} {scope.params[1]} [{", ".join(xs)}]']
            if op == 'FW_add': return [xs[0] if len(xs)==1 else f'elemwiseAdd {xs[0]} {xs[1]}']
            return [xs[0]] * len(outs)
        pure, computed = expressions(v), expressions(actual)
        for p, value in enumerate(pure):
            definition(f'def {stem}Value_{j}_{p} (init : Store) : Tensor := {value}')
        feed = f'(some {node}_feed)' if op == 'DATALOADER' else 'none'
        update = f'storeSet {prev} ['+', '.join(f'({t.tid}, {value})' for t, value in zip(outs, computed))+']'
        if op == 'DATALOADER':
            update = f'storeSet {prev} {node}_feed'
            proof = f'by\n  exact {node}_scoped_step {prev}'
        elif op == 'AllToAllPrim':
            rs = list(scope.ranks); dim, odim = scope.params; out, = outs
            guard = f'{stem}Guard_{j}'
            theorem(guard, f'{args} : AllToAllSourceFaithful.NodeContract {rs} ({label}Peers {node}) {prev} {node} {dim} {odim} {out.tid}',
                    f'by\n  refine ⟨rfl, rfl, rfl, rfl, ?_⟩\n  refine ⟨by decide, rfl, {row["input_shapes"][0]}, ?_, by decide, by decide, by decide, by decide⟩\n  simp [{node}, '+', '.join(reads+[shape_proofs[t.tid] for t in ins])+']')
            guards.append(dict(index=i, source_index=i, execution_index=j, theorem=guard, state=f'{stem}State_{j}', input_tids=[t.tid for t in ins], operand_shapes=row['input_shapes'], output_tid=out.tid, output_shape=row['output_shapes'][0]))
            update = f'AllToAllSourceFaithful.localStep {rs} {prev} {node} {dim} {odim}'
            proof = (f'by\n  change (AllToAllSourceFaithful.step {label}Graph (some {rs}) ({label}Peers {node}) {prev} {node}).toOption = _\n'
                     f'  rw [AllToAllSourceFaithful.step_valid _ _ _ _ _ {dim} {odim} {out.tid} (by decide) ({guard} init hInitShapes)]\n  rfl')
        elif op == 'CROSS_DP_WRED':
            rs = list(scope.ranks); guard = f'{stem}Guard_{j}'
            theorem(guard, f'{args} : WredContract {rs} ({label}Peers {node}) {prev} {node}',
                    'by\n  refine ⟨rfl, rfl, rfl, rfl, by decide, ?_⟩\n'
                    f'  simp only [{node}, List.headD_cons, List.mem_cons, List.not_mem_nil, or_false]\n'
                    '  intro tid ht\n  rcases ht with ' + ' | '.join('rfl' for _ in ins) + '\n' +
                    '\n'.join('  · rfl' if p == 0 else
                              f'  · rw [{reads[p]}, {reads[0]}]\n'
                              f'    exact ({shape_proofs[t.tid]}).trans ({shape_proofs[ins[0].tid]}).symm'
                              for p, t in enumerate(ins)))
            guards.append(dict(index=i, source_index=i, execution_index=j, theorem=guard, state=f'{stem}State_{j}', input_tids=[t.tid for t in ins], operand_shapes=row['input_shapes'], output_tid=outs[0].tid, output_shape=row['output_shapes'][0]))
            proof = (f'by\n  change wredStep {label}Graph (some {rs}) ({label}Peers {node}) {prev} {node} = _\n'
                     f'  rw [wredStep, if_pos ⟨by decide, {guard} init hInitShapes⟩]\n  rfl')
        elif op in ('ChunkPrim', 'AllGatherPrim', 'ReduceScatterPrim', 'AllReducePrim'):
            rs = list(scope.ranks)
            proof = (f'by\n  change GroupScopedEval.step {label}Graph (.group (some {rs})) {prev} {node} = _\n'
                     f'  rw [GroupScopedEval.step_scoped _ _ _ {rs} (by decide) (by rfl)]\n  rfl')
        else:
            proof = 'by\n  change some (applyNode _ _ _) = _\n  rfl'
        definition(f'def {stem}State_{j+1} (init : Store) : Store := {update}')
        condition = op in ('AllToAllPrim', 'CROSS_DP_WRED')
        theorem(f'{stem}Step_{j}', f'{args if condition else "(init : Store)"} : stepWithInputs {label}Graph ({label}Scope {node}) ({label}Peers {node}) {prev} {node} {feed} = some {nxt}', proof)
        steps.append(f'{stem}Step_{j} init'+(' hInitShapes' if condition else ''))
        wrappers = (f'  dsimp only [{node}_feed]\n' if op == 'DATALOADER' else
                    f'  dsimp only [AllToAllSourceFaithful.localStep, {node}, List.zip, List.zipWith]\n'
                    if op == 'AllToAllPrim' else '')
        theorem(f'{stem}Skip_{j}',
                f'(init : Store) (tid : Tid) (h : tid ∉ {[t.tid for t in outs]}) : {nxt} tid = {prev} tid',
                f'by\n  unfold {stem}State_{j+1}\n' + wrappers +
                f'  exact storeSet_eq_of_not_mem_fst _ _ _ (by simpa only [List.map] using h)')
        input_shapes = [shape_proofs[t.tid] for t in ins]
        for p, (t, value, sh) in enumerate(zip(outs, computed, row['output_shapes'])):
            vn = f'{stem}Value_{j}_{p}'; on = f'{stem}Written_{j}_{p}'; sn = f'{stem}Shape_{j}_{p}'
            theorem(on, f'(init : Store) : {nxt} {t.tid} = {vn} init',
                    f'by\n  unfold {stem}State_{j+1}\n' + wrappers +
                    f'  simp only [storeSet, List.find?, List.map, Nat.reduceEqDiff, decide_true, decide_false, {vn}'+(', '+', '.join(reads) if reads else '')+'] <;> rfl')
            # Project shape through this operator only. Never simplify a nested
            # value graph: real-width normalization/linear arithmetic is costly
            # even though it is irrelevant to this theorem.
            shape_start = f'by\n  unfold {vn}\n'
            if op in ('FW_view', 'FW_reshape', 'BW_view', 'FW_sum'):
                shape_proof = '  rfl'
            elif op in ('BW_multiref', 'CROSS_DP_WRED'):
                shape_proof = ('  rw [tensorSum_shape]\n'
                               f'  exact {input_shapes[0]}')
            elif op == 'BW_add':
                shape_proof = f'  exact {input_shapes[p+1]}'
            elif op == 'BW_gelu':
                shape_proof = f'  exact {input_shapes[1]}'
            elif op == 'BW_sum':
                shape_proof = f'  exact {input_shapes[1]}'
            elif op in ('FW_transpose', 'BW_transpose'):
                shape_proof = ('  change listSwapAt _ _ _ = _\n'
                               f'  rw [{input_shapes[0]}]\n  rfl')
            elif op == 'FW_matmul':
                shape_proof = ('  unfold fw_matmul batchedMatmul\n'
                               f'  rw [{input_shapes[0]}, {input_shapes[1]}]\n  rfl')
            elif op == 'BW_matmul':
                operands = f'{v[0]} (transpose2d {v[2]})' if p == 0 else f'(transpose2d {v[1]}) {v[0]}'
                shape_proof = (f'  change (batchedMatmul {operands}).shape = _\n'
                               '  unfold batchedMatmul transpose2d\n'
                               f'  rw [{input_shapes[0]}, {input_shapes[2 if p == 0 else 1]}]\n  rfl')
            elif op == 'BW_embedding':
                shape_proof = f'  exact {input_shapes[2]}'
            elif op in ('FW_div', 'BW_div', 'FW_contiguous', 'BW_contiguous', 'FW_gelu'):
                shape_proof = f'  exact {input_shapes[0]}'
            elif op == 'BW_softmax':
                shape_proof = ('  unfold bw_softmax softmaxBwd softmaxBwdFromOutput softmax\n'
                               f'  rw [{input_shapes[1]}]\n  rfl')
            elif op == 'FW_softmax':
                shape_proof = ('  unfold fw_softmax softmax\n'
                               f'  split <;> exact {input_shapes[0]}')
            elif op == 'FW_layernorm':
                shape_proof = ('  rw [SourceScopedPrefix.layernorm_shape]\n'
                               f'  exact {input_shapes[0]}')
            elif op == 'BW_layernorm':
                xshape = row['input_shapes'][1]
                role = ('dx', 'dw', 'db')[p]
                shape_proof = (f'  rw [bw_layernorm_{role}_shape {" ".join(v)} {xshape[-1]} {list(reversed(xshape[:-1]))} '
                               f'(by rw [{input_shapes[1]}]; rfl)]\n'
                               f'  exact {input_shapes[p+1]}')
            elif op == 'BW_linear':
                grad, xshape, weight = row['input_shapes']
                dims = grad + [xshape[-1]] if len(grad) == 3 else [xshape[0], xshape[1], weight[0]]
                lemma = 'bw_linear_' + ('3d_' if len(grad) == 3 else '') + ('fst' if p == 0 else 'snd') + '_shape'
                shape_proof = f'  exact {lemma} {" ".join(map(str, dims))} {" ".join(v)} ' + ' '.join(f'({h})' for h in input_shapes)
            elif op == 'FW_linear':
                dims = row['input_shapes'][0] + [row['input_shapes'][1][0]]
                lemma = 'fw_linear_3d_shape' if len(dims) == 4 else 'SourceScopedPrefix.linear_shape_2d'
                shape_proof = f'  exact {lemma} {" ".join(map(str, dims))} {" ".join(v)} ' + ' '.join(f'({h})' for h in input_shapes)
            elif op == 'AllReducePrim':
                shape_proof = (f'  rw [allReducePrim_shape _ _ _ {v[0]} rfl]\n'
                               f'  exact {input_shapes[0]}')
            elif op == 'AllGatherPrim':
                dim, = scope.params
                shape_proof = (f'  exact allGatherPrimDimN_shape {dim} {len(scope.ranks)} '
                               f'[{", ".join(v)}] {row["input_shapes"][0]} ({input_shapes[0]})')
            elif op == 'ReduceScatterPrim':
                shape_proof = (f'  unfold reduceScatterPrimDimN\n'
                               f'  apply chunkPrimDimN_shape {scope.params[0]} {len(scope.ranks)} '
                               f'{scope.local_index} _ {row["input_shapes"][0]}\n'
                               f'  · rw [allReducePrim_shape _ _ _ {v[0]} rfl]\n'
                               f'    exact {input_shapes[0]}\n'
                               f'  · decide')
            elif op == 'ChunkPrim':
                shape_proof = (f'  exact chunkPrimDimN_shape {scope.dim} {len(scope.ranks)} '
                               f'{scope.local_index} {v[0]} {row["input_shapes"][0]} '
                               f'({input_shapes[0]}) (by decide)')
            elif op == 'FW_multiref' or (op == 'FW_add' and len(ins) == 1):
                shape_proof = f'  exact {input_shapes[0]}'
            else:
                shape_defs = []
                if op == 'DATALOADER':
                    shape_defs += [f'{node}_port{p}', 'Tensor.mkShape']
                elif op == 'FW_embedding':
                    shape_defs += ['fw_embedding_shape', 'lastD'] + input_shapes
                elif op == 'FW_add':
                    shape_defs += ['elemwiseAdd', 'Tensor.mkShape', 'outShape2'] + input_shapes
                elif op == 'AllToAllPrim':
                    shape_start += '  rw [AllToAllSourceFaithful.tensor_shape _ _ _ _ _ _ (by decide)]\n'
                    shape_defs = input_shapes[:1]
                shape_proof = '  simp [' + ', '.join(shape_defs) + ']'
            theorem(sn, f'{args} : ({vn} init).shape = {sh}', shape_start + shape_proof)
            # Later proof elaboration must use the named read/shape facts, not
            # recursively evaluate normalization or matrix entries. Local only:
            # the generated value definitions and exported statements are unchanged.
            lines.append(f'attribute [local irreducible] {vn}')
            opaque.append(vn)
            values[t.tid] = f'({vn} init)'; writers[t.tid] = (j, on); shape_proofs[t.tid] = f'{sn} init hInitShapes'
            read_certificates.pop(t.tid, None)
        lines.append(f'attribute [local irreducible] {stem}State_{j+1}')
        opaque.append(f'{stem}State_{j+1}')
        group()

    selected = [r['index'] for r in rows]; length = len(rows); final = state(length)
    # Certificates share the exact existing computed Store endpoints.  Their
    # request lists are proof-only; the canonical graph and schedule stay intact.
    # A balanced append tree bounds assembly without re-expanding earlier runs.
    def requests(a, b): return f'{stem}Requests_{a}_{b}'
    def run_name(a, b): return f'{stem}Run_{a}_{b}'
    def interval(a, b):
        req = requests(a, b)
        if b - a <= RUN_STEP_BUDGET:
            items = ', '.join(f'({label}Node_{i}, ' +
                (f'some {label}Node_{i}_feed' if i in feeds else 'none') + ')'
                for i in selected[a:b])
            definition(f'def {req} : List InputRequest := [{items}]')
            # Simplify the bounded leaf bottom-up. Repeated rw searches start at
            # outer steps and repeatedly compare concrete node/scope expressions
            # before reaching the innermost matching computed Store.
            rules = ', '.join(steps[q] for q in range(a, b))
            proof = (f'by\n  simp only [{req}, runUsing, List.foldl_cons, '
                     f'List.foldl_nil, Option.bind_some, {rules}]')
            if a == b:
                proof = f'by\n  rfl'
        else:
            middle = a + (b - a) // 2
            interval(a, middle); interval(middle, b)
            definition(f'def {req} : List InputRequest := {requests(a, middle)} ++ {requests(middle, b)}')
            proof = (f'by\n  unfold {req}\n'
                     f'  rw [SourceScopedPrefix.runUsing_append, {run_name(a, middle)} init hInitShapes]\n'
                     f'  exact {run_name(middle, b)} init hInitShapes')
        theorem(run_name(a, b), f'{args} : runUsing {advance} {req} (some {state(a)}) = some {state(b)}', proof)
        group()
    if RUN_STEP_BUDGET < 1:
        raise ValueError('run step budget must be positive')
    interval(0, length)
    theorem(stem+'RequestsCoverage',
            f': {label}InputRequests.take {length} = {requests(0, length)}', 'by\n  rfl')
    group()
    run = f'runUsing {advance} ({label}InputRequests.take {length}) (some {initial_store})'
    theorem(stem+'Success', f'{args} : {run} = some {final}',
            f'by\n  rw [{stem}RequestsCoverage]\n  exact {run_name(0, length)} init hInitShapes')
    out = rows[-1]['outs'][-1]; sh = shapes_out = rows[-1]['output_shapes'][-1]
    theorem(stem+'Output', f'(init : Store) : {final} {out.tid} = {values[out.tid]}', f'{writers[out.tid][1]} init')
    theorem(stem+'OutputShape', f'{args} : ({final} {out.tid}).shape = {sh}', f'by\n  rw [{stem}Output]\n  exact {shape_proofs[out.tid]}')
    theorem(stem+'Frame', f'{args} (tid : Tid) (ht : ∀ row ∈ {label}InputRequests.take {length}, tid ∉ row.1.outs) : {final} tid = {initial_store} tid',
            f'SourceScopedPrefix.frame {label}Graph {label}Scope {label}Peers _ {initial_store} {final} tid ht ({stem}Success init hInitShapes)')
    denote = label + ('DenoteWithInputs' if seeds is None else 'SeededDenoteWithInputs')
    entry_unfold = '' if seeds is None else f'  unfold {label}SeededDenoteWithInputs\n'
    theorem(stem+'Continuation', f'{args} : {denote} init = runUsing {advance} ({label}InputRequests.drop {length}) (some {final})',
            f'by\n{entry_unfold}  rw [{label}DenoteWithInputs_entry]\n  exact SourceScopedPrefix.continuation _ _ {length} {initial_store} {final} ({stem}Success init hInitShapes)')
    group(final=True)
    text = groups if structured else _HEADER + '\n'.join(g.text for g in groups) + _FOOTER
    return text, dict(status='conditional-prefix-emitted', prefix_nodes=selected,
        prefix_length=length, boundary_index=guards[-1]['index'], guards=guards, frontier=frontier,
        initial_premises=list(initial.values()), output_tid=out.tid, output_shape=shapes_out,
        kernel_checks=names, kernel_checked=False, whole_world_option_success=False, external_adapter_proved=False)
