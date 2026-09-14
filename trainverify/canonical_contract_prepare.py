"""Pinned, manifest-driven canonical reference preparation; never executes Lean."""
import hashlib
from trainverify.artifact_tools import digest_value, keys, require, strict_json


class PinnedInputs:
    """Consume the same bytes that were hashed, preserving original identities."""
    def __init__(self, layout):
        self.layout = layout
        self.bound = {}
        self.cache = {}

    def read(self, pin):
        keys(pin, ('path', 'sha256'), 'input pin')
        digest_value(pin['sha256'])
        path = self.layout.resolve(pin['path'])
        if pin['path'] not in self.cache:
            self.cache[pin['path']] = path.read_bytes()
        data = self.cache[pin['path']]
        require(hashlib.sha256(data).hexdigest() == pin['sha256'], 'input hash mismatch: ' + pin['path'])
        self.bound[pin['path']] = dict(sha256=pin['sha256'], resolved=str(path))
        return data

    def json(self, pin):
        return strict_json(self.read(pin))


import re
from trainverify.artifact_tools import lean_name, render_joint


def norm(text):
    text = re.sub(r'\s+', ' ', text).strip()
    # Alpha-normalize only the closed local-shape quantifier, not free names.
    return re.sub(r'\(∀ (\w+) ∈ (\[[^\]]*\]), \1\.shape = (\[[0-9, ]+\])\)',
                  lambda m: '(∀ y ∈ '+m[2]+', y.shape = '+m[3]+')', text)


def names(source):
    result = re.findall(r'^[ \t]*theorem ([\w\']+)\b', source, re.M)
    require(len(result) == len(set(result)), 'duplicate source theorem')
    return result


def declarations(source):
    """Deliberately restricted generated-source grammar, not a Lean parser."""
    result = {}
    for name in names(source):
        match = re.search(r'^theorem '+re.escape(name)+r'\s+(.*?)\s:=\s*(.*?)(?=^(?:theorem|def|noncomputable def|end|#|run_cmd)\b|\Z)', source, re.M | re.S)
        require(match is not None, 'unsupported declaration: '+name)
        header, proof = match.groups()
        result[name] = (header, proof.removeprefix('by\n'))
    return result


def signature(header):
    if header.lstrip().startswith(':'):
        return '', header.lstrip()[1:].strip()
    require(') :\n' in header, 'unsupported conditional signature')
    binders, proposition = header.split(') :\n', 1)
    return binders+')', proposition.strip()


def substitute(text, mapping):
    return re.sub(r'\b(?:'+ '|'.join(map(re.escape, mapping)) +r')\b', lambda m: mapping[m[0]], text)


def joint_signature(rows):
    source = render_joint(rows, 'Placeholder')
    return signature(declarations(source)['projectionFrontierJoint'][0])


def full_proposition(row):
    require(row['theorem'] == row['facts_theorem'], 'facts declaration identity mismatch')
    _, clause = joint_signature([row])
    g, local = row['global_shape'], row['local_shape']
    expected = list(g)
    d, t = row['dimensions']['D'], row['dimensions']['T']
    require(g[0] % d == 0, 'DP divisibility')
    expected[0] //= d
    require(len(row['ranks']) == t and len(set(row['ranks'])) == t, 'rank cover')
    if row['layout'] == 'sharded':
        axis = row['gather_axis']
        require(axis > 0 and expected[axis] % t == 0, 'TP divisibility/axis')
        expected[axis] //= t
    require(expected == local, 'global/local shape mismatch')
    return clause[1:-1]


def variants(proposition):
    # The accepted sources differ only in parentheses around a terminal forall.
    result = {norm(proposition), norm('('+proposition+')')}
    if ' ∧ (∀ y ∈ ' in proposition and proposition.endswith(')'):
        result.add(norm(proposition.rsplit(' ∧ (∀ y ∈ ', 1)[0]+' ∧ ∀ y ∈ '+proposition.rsplit(' ∧ (∀ y ∈ ', 1)[1][:-1]))
    return result


def extend_joint(old, source, detail, namespace, seed, stage, previous):
    lean_name(namespace)
    keys(seed, ('anchor', 'instance', 'prelude', 'arguments', 'read_worlds'), 'seed recipe')
    keys(seed['arguments'], ('s', 'p', 't', 'q', 'hs', 'hp', 'hvalues'), 'seed argument mapping')
    keys(seed['read_worlds'], ('sm', 'pm'), 'read world mapping')
    keys(stage, ('pair', 'cumulative'), 'stage pair names')
    for name in [seed['anchor'], seed['instance'], previous, *stage.values()]: lean_name(name)
    olddecl, newdecl = declarations(old), declarations(source)
    require('namespace '+namespace+'\n' in old and 'namespace '+namespace+'\n' in source, 'namespace mismatch')
    ending = 'end '+namespace+'\n'
    require(old.count(ending) >= 1, 'old namespace boundary')
    oldbody, tail = old.rsplit(ending, 1)
    require(not tail.strip() or tail.startswith('run_cmd do\n'), 'unsupported old observer suffix')
    binders, conclusion = joint_signature(detail['frontier_units'])
    args = seed['arguments']
    arguments = ' '.join(args[k] for k in ('s', 'p', 't', 'q', 'hs', 'hp', 'hvalues'))
    require(seed['anchor'] in olddecl and seed['instance'] in olddecl, 'missing seed anchor')
    anchorbind, anchorprop = signature(olddecl[seed['anchor']][0])
    require(norm(anchorbind) == norm(binders), 'seed anchor conditional binders mismatch')
    require(norm(olddecl[seed['instance']][0]) == ': '+norm(substitute(anchorprop, {'t': args['t'], 'q': args['q']})), 'seed final-state mapping mismatch')
    require(olddecl[seed['instance']][1].rstrip() == (seed['prelude']+'  exact '+seed['anchor']+' '+arguments).rstrip(), 'seed proof/arguments mapping mismatch')
    for world, expected in [('sm', ('s', 't', 'hs')), ('pm', ('p', 'q', 'hp'))]:
        row = seed['read_worlds'][world]
        keys(row, ('initial', 'final', 'hypothesis', 'run'), 'read mapping')
        require((row['initial'], row['final'], row['hypothesis']) == expected, 'unknown read mapping')
        lean_name(row['run'])
        i, f, h = expected
        require('('+h+' : '+row['run']+' '+i+' = some '+f+')' in norm(binders), 'read run not bound to old declaration')
    freshrows = detail['reads'] + detail['units']
    declared = [r['theorem'] for r in freshrows]
    require(len(declared) == len(set(declared)) and set(declared) == set(newdecl), 'reads/units source census mismatch')
    frontier = detail['frontier_units']
    fnames = [r['theorem'] for r in frontier]
    require(len(fnames) == len(set(fnames)), 'duplicate frontier')
    carried = detail['retained_units'] + [r['source_boundary'] for r in detail['deferred_units']]
    require(set(fnames) == {r['theorem'] for r in detail['units']+carried}, 'missing retained/deferred frontier')
    for row in frontier:
        prop = full_proposition(row)
        name = row['theorem']
        if name in newdecl:
            b, p = signature(newdecl[name][0])
            require(norm(b) == norm(binders) and norm(p) in variants(prop), 'new complete value signature mismatch: '+name)
        else:
            require('audit_'+name in olddecl, 'missing old carry: '+name)
            require(norm(olddecl['audit_'+name][0]) in {': '+v for v in variants(substitute(prop, {'t': args['t'], 'q': args['q']}))}, 'old carry complete signature mismatch: '+name)
    addition = ''
    def theorem(name, header, proof):
        nonlocal addition
        require(name not in olddecl and name not in declarations(addition), 'old/new theorem overwrite: '+name)
        addition += 'theorem '+name+' '+header+' := by\n'+proof+'\n#print axioms '+name+'\n'
    for row in freshrows:
        name = row['theorem']
        b, p = signature(newdecl[name][0])
        if row in detail['units']:
            require(norm(b) == norm(binders), 'extra unit premises')
            mapping, callargs = {'t': args['t'], 'q': args['q']}, arguments
        else:
            require(row['world'] in seed['read_worlds'], 'unknown read world')
            w = seed['read_worlds'][row['world']]
            require(norm(b) == '(s t : Store) (h : '+w['run']+' s = some t)', 'extra read premises')
            mapping = {'t': args[w['final']]}
            callargs = ' '.join(args[w[k]] for k in ('initial', 'final', 'hypothesis'))
        theorem('audit_'+name, ':\n    '+substitute(p, mapping), seed['prelude']+'  exact '+name+' '+callargs)
    def pair(name, prop, proof):
        theorem(name, binders+' :\n    '+prop, '  exact '+proof)
        theorem(name+'_inhabited', ':\n    '+substitute(prop, {'t': args['t'], 'q': args['q']}), seed['prelude']+'  exact '+name+' '+arguments)
    pair(stage['pair'], conclusion, '⟨'+', '.join(r['facts_theorem']+' s p t q hs hp hvalues' for r in frontier)+'⟩')
    require(previous in olddecl, 'missing previous cumulative theorem')
    prevbind, prevprop = signature(olddecl[previous][0])
    require(norm(prevbind) == norm(binders), 'previous cumulative premises mismatch')
    pair(stage['cumulative'], '('+prevprop+') ∧\n    ('+conclusion+')', '⟨'+previous+' s p t q hs hp hvalues, '+stage['pair']+' s p t q hs hp hvalues⟩')
    result = oldbody+addition+ending
    require(names(result)[:len(olddecl)] == list(olddecl), 'old joint census changed')
    return result


def replace_first_import(source, expected, replacement):
    lean_name(expected); lean_name(replacement)
    require(source.startswith('import '+expected+'\n'), 'wrong first import/reference source')
    return 'import '+replacement+'\n'+source.split('\n', 1)[1]


def check_kernel(reader, pin, source, targets=None):
    receipt = reader.json(pin)
    require(type(receipt['inner_exit']) is int and receipt['inner_exit'] == 0, 'reference kernel failed')
    require(receipt['source'] == source['path'] and receipt['source_sha256'] == source['sha256'], 'wrong kernel reference source')
    for field in ('source', 'object'):
        reader.read(dict(path=receipt[field], sha256=receipt[field+'_sha256']))
    require(bool(receipt['dependency_objects']), 'missing reference dependencies')
    for path, digest in receipt['dependency_objects'].items(): reader.read(dict(path=path, sha256=digest))
    if targets is not None:
        require(set(receipt['axioms']) == set(targets), 'independent kernel declaration census mismatch')
        for axioms in receipt['axioms'].values():
            require(type(axioms) is list and len(axioms) == len(set(axioms)) and set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}, 'reference axioms mismatch')
    return receipt


def prepare(layout, recipe_pin, output):
    """Prepare all stages after complete preflight. No actual/capture/Lean API."""
    import json
    from pathlib import Path
    from trainverify.artifact_tools import absolute
    from trainverify.artifact_contracts import dump_contracts, preserve_old, validate_manifest
    reader = PinnedInputs(layout)
    recipe = reader.json(recipe_pin)
    keys(recipe, ('version', 'namespace', 'base_module', 'base', 'seed', 'previous', 'stages'), 'preparation recipe')
    require(type(recipe['version']) is int and recipe['version'] == 1, 'recipe version')
    ns = lean_name(recipe['namespace'])+'.'
    module = lean_name(recipe['base_module'])
    base = recipe['base']
    keys(base, ('receipt', 'preparation', 'complete', 'full_records', 'joint_records', 'joint_source', 'world'), 'baseline recipe')
    destination = absolute(output)
    if destination.exists(): raise FileExistsError(str(destination))
    receipt = reader.json(base['receipt'])
    oldprep = reader.json(base['preparation'])
    complete = reader.json(base['complete'])
    full = reader.json(base['full_records']); oldjointtypes = reader.json(base['joint_records'])
    joint = reader.read(base['joint_source']).decode()
    old_joint = joint
    world = reader.json(base['world'])
    require(complete['verified'] is True, 'baseline not accepted')
    for key in ('full_records', 'joint_records'):
        require(complete['files'].get(base[key]['path']) == base[key]['sha256'], 'baseline record provenance mismatch')
    for path, digest in complete['files'].items(): reader.read(dict(path=path, sha256=digest))
    require(oldprep['outputs'].get(base['joint_source']['path']) == base['joint_source']['sha256'], 'baseline joint source provenance mismatch')
    public, private = list(oldprep['public_targets']), list(oldprep['private_targets'])
    require(set(full) == set(public+private) and len(full) == len(public)+len(private), 'old full inventory mismatch')
    require(all(n.startswith('_private.'+module+'.') for n in private), 'private internal names changed')
    oldtargets = [ns+n for n in names(joint)]
    require(oldtargets == oldprep['joint_targets'] and set(oldtargets) == set(oldjointtypes), 'old joint record/source census mismatch')
    require(complete['full_contracts'] == len(full) and complete['joint_theorems'] == len(oldjointtypes), 'baseline complete census mismatch')
    preserve_old(full, full); preserve_old(oldjointtypes, oldjointtypes)
    modules = receipt['proof_bundle']['modules']
    require(len({m['module'] for m in modules}) == len(modules), 'duplicate baseline module')
    entries = [m for m in modules if m['module'] == module]
    require(len(entries) == 1 and [ns+n for n in entries[0]['theorems']] == public, 'published public census mismatch')
    entrysource = None
    for m in modules:
        rel = Path(m['file'])
        require(not rel.is_absolute() and '..' not in rel.parts and str(rel) == m['file'], 'invalid published module path')
        p = str(Path(base['receipt']['path']).parent/rel)
        text = reader.read(dict(path=p, sha256=m['source_sha256'])).decode()
        if m['module'] == module:
            require(names(text) == m['theorems'], 'published source declaration census mismatch')
            entrysource = text
    for field, oldfield in [('world_fullrefs', 'fullrefs'), ('execution_order', 'execution_order')]:
        require(world[field] == receipt[oldfield], 'baseline world binding mismatch: '+field)
    files = {'baseline/full-types.json': reader.read(base['full_records']),
             'baseline/joint-types.json': reader.read(base['joint_records']),
             'baseline/Joint.lean': reader.read(base['joint_source']),
             'baseline/'+module+'.lean': entrysource.encode()}
    previous = recipe['previous']
    require(type(recipe['stages']) is list and bool(recipe['stages']), 'empty stage recipe')
    stage_reports = []
    module_names = {module}
    for stage in recipe['stages']:
        keys(stage, ('source', 'detail', 'world', 'kernel', 'joint_source', 'joint_kernel', 'first_import', 'module', 'pair', 'cumulative'), 'stage recipe')
        reference = lean_name(stage['module'])
        require(reference not in module_names, 'reference module overwrite')
        module_names.add(reference)
        source = reader.read(stage['source']).decode(); detail = reader.json(stage['detail'])
        w = reader.json(stage['world'])
        for field in ('world_fullrefs', 'execution_order', 'bound'):
            require(w[field] == world[field], 'reference world/initial binding mismatch: '+field)
        new = [ns+n for n in names(source)]
        require(new and not set(new)&set(public), 'new declarations overwrite old public')
        check_kernel(reader, stage['kernel'], stage['source'], new)
        acceptedjoint = reader.read(stage['joint_source']).decode()
        check_kernel(reader, stage['joint_kernel'], stage['joint_source'])
        b, p = joint_signature(detail['frontier_units'])
        require(norm(declarations(acceptedjoint)['projectionFrontierJoint'][0]) == norm(b+' :\n    '+p), 'independent accepted joint full signature mismatch')
        reference_source = replace_first_import(source, stage['first_import'], module)
        files['reference/'+reference+'.lean'] = reference_source.encode()
        joint = extend_joint(joint, source, detail, recipe['namespace'], recipe['seed'], {k: stage[k] for k in ('pair', 'cumulative')}, previous)
        public += new
        targets = [ns+n for n in names(joint)]
        fullmanifest = validate_manifest(dict(version=1, targets=public+private, axiom_queries=public+private))
        jointmanifest = validate_manifest(dict(version=1, targets=targets, axiom_queries=targets))
        observer = dump_contracts([], jointmanifest, emit_axioms=False)
        files['reference/'+reference+'Joint.lean'] = (replace_first_import(joint, recipe['base_module'], reference)+observer).encode()
        files['reference/'+reference+'Contracts.lean'] = dump_contracts([reference], fullmanifest).encode()
        files['manifests/'+reference+'-full.json'] = (json.dumps(fullmanifest, indent=2)+'\n').encode()
        files['manifests/'+reference+'-joint.json'] = (json.dumps(jointmanifest, indent=2)+'\n').encode()
        stage_reports.append(dict(module=reference, new_targets=new, counts=dict(public=len(public), full=len(public+private), joint=len(targets)),
                                  reads=len(detail['reads']), units=len(detail['units']), frontier_units=len(detail['frontier_units']),
                                  frontier=detail['frontier_units'], retained=detail['retained_units'], deferred=detail['deferred_units']))
        module, previous = reference, stage['cumulative']
    oldprefix = old_joint.rsplit('end '+recipe['namespace']+'\n', 1)[0]
    require(joint.startswith(oldprefix), 'old namespace body not byte preserved')
    report = dict(mode='reference-only-prepared', kernel_verified=False, proof_admissible=False,
                  actual_read=False, capture_executed=False, recipe=recipe_pin, config_sha256=layout.config_sha256,
                  old_full_preserved=len(full), old_joint_preserved=len(oldjointtypes),
                  old_joint_body_sha256=hashlib.sha256(oldprefix.encode()).hexdigest(), old_joint_body_byte_preserved=True,
                  counts=stage_reports[-1]['counts'], stages=stage_reports, bound_files=reader.bound,
                  outputs={p: hashlib.sha256(data).hexdigest() for p, data in files.items()},
                  scope='Pinned accepted-reference preparation only. Baseline records and source retained; no new Expr comparison, kernel run, candidate acceptance or Torch refinement.')
    # Exclusive directory claim, validations before writes, receipt last. Failed
    # I/O may leave an incomplete owned directory, never a success manifest.
    destination.mkdir(parents=False, exist_ok=False)
    for relative, data in files.items():
        target = destination/relative
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as stream: stream.write(data)
    with (destination/'preparation.json').open('x') as stream: json.dump(report, stream, indent=2); stream.write('\n')
    return report


def main(argv=None):
    import argparse
    from trainverify.artifact_tools import Configuration, emit
    parser = argparse.ArgumentParser(description=__doc__)
    for flag in ('config', 'recipe', 'recipe-sha256', 'out'): parser.add_argument('--'+flag, required=True)
    args = parser.parse_args(argv)
    try:
        report = prepare(Configuration.load(args.config), dict(path=args.recipe, sha256=args.recipe_sha256), args.out)
        emit({k: report[k] for k in ('mode', 'counts', 'old_full_preserved', 'old_joint_preserved', 'kernel_verified')})
        return 0
    except (ValueError, OSError, KeyError, TypeError, UnicodeError) as exc:
        emit(dict(status='REJECTED', error=str(exc), kernel_verified=False))
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
