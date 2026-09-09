"""Bind observed initialized parameters to original source fullrefs.

Exact CPU tensor equality is current-run evidence, not a Lean Store-value
inhabitant or a proof of the cross-world initial relation.
"""


def validate(sm, pm, raw_sm, raw_pm, actuals, reference, sources):
    import re
    from Verdict.runtime_lineage import _Index
    from trainverify.runtime_source_authority import _rank_reducers
    from scripts.gpt_batch_runtime import exact, shard
    from Verdict.runtime_seed_feed import same
    bindings = []; globals_ = {}
    for label, view, raw in [('sm', sm, raw_sm), ('pm', pm, raw_pm)]:
        index = _Index(view, raw)
        world = view.W.runtime_ndevs
        if len(actuals[label]) != world or set(sources[label]) != set(range(world)):
            raise ValueError('parameter observation rank inventory mismatch')
        parents = {}
        for cell in raw:
            if str(cell.opname).split('.')[-1] in ('FW_embedding', 'FW_linear', 'FW_layernorm'):
                for ref, ir in zip(cell.inputs, cell._input_irs):
                    if ir.is_param():
                        if ref.rank != cell.rank:
                            raise ValueError('initial parameter fullref owner mismatch')
                        if tuple(ref) in parents and parents[tuple(ref)] != ir.parent.tid:
                            raise ValueError('ambiguous raw parameter parent')
                        parents[tuple(ref)] = ir.parent.tid
        refs = {ref: meta for ref, meta in index.meta.items()
                if meta[4] and not meta[5] and ref not in index.writers}
        for rank, actual in enumerate(actuals[label]):
            _, maps, _ = _rank_reducers(sources[label][rank], rank, world)
            expected = {n: dict(orig_name=m['name'], shape=m['full_shape'],
                               slicers=[[a,b,None] for a,b in m['indmap']], val_chunks=m['chunks'])
                        for n,m in maps.items()}
            if not same(actual.get('metadata'), expected) or set(actual.get('initialized', {})) != set(maps):
                raise ValueError('parameter observations differ from original generated fullmap')
            rank_refs = {ref: meta for ref, meta in refs.items() if ref[1] == rank}
            consumed = set()
            for name, m in maps.items():
                match = re.fullmatch(r'.+_([0-9]+)', name)
                if match is None or type(m['chunks']) is not int or m['chunks'] != 1:
                    raise ValueError('unsupported parameter identity/value partition')
                candidates = [(ref, meta) for ref, meta in rank_refs.items()
                              if ref[3] == int(match[1])]
                if len(candidates) != 1:
                    raise ValueError('parameter must have one original initial fullref')
                ref, meta = candidates[0]
                if (m['parent_tid'] != parents[ref] or ref[0] != ('s' if label == 'sm' else 'p') or ref[2:] != (-1, int(match[1]), 0)
                        or (meta[0], meta[1], meta[2], meta[3]) !=
                        (m['name'], tuple(m['full_shape']), tuple(map(tuple,m['indmap'])), (0,1))):
                    raise ValueError('parameter source identity/placement/fullref mismatch')
                if ref in consumed:
                    raise ValueError('duplicate parameter initialization binding')
                consumed.add(ref)
                exact(actual['initialized'][name], shard(reference['state'][m['name']], expected[name]))
                full = tuple((0,d) for d in m['full_shape'])
                if label == 'sm':
                    if meta[2] != full or m['name'] in globals_:
                        raise ValueError('ambiguous or sliced global parameter')
                    globals_[m['name']] = ref
                if m['name'] not in globals_:
                    raise ValueError('missing original SM parameter')
                bindings.append(dict(world=label, rank=rank, ref=list(ref), tid=index.refs[ref].tid,
                    sm_ref=list(globals_[m['name']]), runtime_name=name, logical_name=m['name'],
                    parent_tid=m['parent_tid'], full_shape=m['full_shape'], bounds=m['indmap'],
                    value_part=[0,1], shape=list(actual['initialized'][name].shape)))
            if consumed != set(rank_refs):
                raise ValueError('incomplete raw parameter observation coverage')
    return dict(status='current-run-parameter-values-validated', bindings=bindings,
                kernel_value_proved=False, proof_admissible=False, torch_refinement=False)
