"""Full Lean Expr contracts from independent operator-owned target manifests.

Exact repr strings, including private internal names, binders and universes.
No compiler-derived census, name normalization or theorem pretty printing.
"""
import re
import json
from trainverify.artifact_tools import _AXIOMS, keys, require, strict_json, lean_name
from trainverify.artifact_lean import _parse_axiom_record, _stdout_lines


def contract_name(name):
    # Numeric components occur in private internal names; never rewrite them.
    require(type(name) is str and re.fullmatch(
        r"[A-Za-z_][A-Za-z0-9_']*(?:\.(?:[A-Za-z_][A-Za-z0-9_']*|0|[1-9][0-9]*))*", name) is not None,
        'invalid exact Lean contract name')
    return name


def validate_manifest(manifest):
    keys(manifest, ('version', 'targets', 'axiom_queries'), 'target manifest')
    require(type(manifest['version']) is int and manifest['version'] == 1, 'unsupported manifest version')
    for field in ('targets', 'axiom_queries'):
        values = manifest[field]
        require(type(values) is list and bool(values), 'explicit nonempty ' + field + ' required')
        for name in values:
            contract_name(name)
        require(len(values) == len(set(values)), 'duplicate manifest ' + field)
    require(set(manifest['targets']) <= set(manifest['axiom_queries']), 'contract target lacks axiom query')
    return manifest


def parse_contracts(text, manifest):
    validate_manifest(manifest)
    contracts, axioms = {}, {}
    lines = _stdout_lines(text)
    for line in lines:
        kind, sep, payload = line.partition('|')
        if sep and kind in ('CONTRACT_JSON', 'AXIOMS_JSON'):
            row = strict_json(payload)
        else:
            # Explicit support for existing joint sources; not a stdout filter.
            name, values = _parse_axiom_record(line, lines)
            kind, row = 'AXIOMS_JSON', dict(name=name, axioms=values)
        fields = ('name', 'level_params', 'type') if kind == 'CONTRACT_JSON' else ('name', 'axioms')
        keys(row, fields, 'Lean record')
        name = contract_name(row['name'])
        if kind == 'CONTRACT_JSON':
            require(name not in contracts, 'duplicate contract target: ' + name)
            require(all(type(row[k]) is str and bool(row[k].strip()) for k in ('level_params', 'type')),
                    'empty or malformed full Expr')
            contracts[name] = row['level_params'] + '|' + row['type']
        else:
            require(name not in axioms, 'duplicate axiom query: ' + name)
            values = row['axioms']
            require(type(values) is list and all(type(x) is str for x in values), 'invalid axiom list')
            require(len(values) == len(set(values)) and set(values) <= _AXIOMS, 'unsupported or duplicate Lean axioms')
            axioms[name] = values
    require(set(contracts) == set(manifest['targets']), 'full Expr target inventory mismatch')
    require(set(axioms) == set(manifest['axiom_queries']), 'axiom query inventory mismatch')
    return dict(contracts=contracts, axioms=axioms)


def dump_contracts(imports, manifest, *, emit_axioms=True):
    """Render a standalone probe or appendable run_cmd block (imports=[]).

    emit_axioms=False supports sources already printing the explicit axiom
    query list; parse_contracts still requires that entire list exactly once.
    """
    validate_manifest(manifest)
    require(type(imports) is list and len(imports) == len(set(imports)), 'explicit distinct imports required')
    for module in imports:
        lean_name(module)
    require(type(emit_axioms) is bool, 'emit_axioms must be bool')
    source = ''.join('import ' + name + '\n' for name in imports)
    source += 'run_cmd do\n'
    source += '  for s in ' + json.dumps(manifest['targets']) + ' do\n'
    source += '    let info ← Lean.getConstInfo s.toName\n'
    source += '    let row := Lean.Json.mkObj [("name", Lean.toJson s),\n'
    source += '      ("level_params", Lean.toJson ((repr info.levelParams).pretty)),\n'
    source += '      ("type", Lean.toJson ((repr info.type).pretty))]\n'
    source += '    Lean.logInfo m!"CONTRACT_JSON|{row.compress}"\n'
    if emit_axioms:
        source += '  for s in ' + json.dumps(manifest['axiom_queries']) + ' do\n'
        source += '    let axs ← Lean.collectAxioms s.toName\n'
        source += '    let row := Lean.Json.mkObj [("name", Lean.toJson s),\n'
        source += '      ("axioms", Lean.toJson (axs.toList.map toString))]\n'
        source += '    Lean.logInfo m!"AXIOMS_JSON|{row.compress}"\n'
    return source


def run_contracts(config, source, expected, outdir, manifest, timeout=120, module=None):
    """Check exact prepared source with the existing bounded direct-Lean runner.

    Preparation and independent reference authority remain caller obligations.
    Only this new entry point selects the full-Expr parser; run_lean is unchanged.
    """
    import hashlib
    from trainverify.artifact_lean import _run_lean
    # Freeze the explicit inventory so callbacks cannot observe later mutation.
    manifest = strict_json(json.dumps(validate_manifest(manifest)))
    metadata = dict(profile='full-expr-v1', manifest=manifest,
                    manifest_sha256=hashlib.sha256(json.dumps(manifest, sort_keys=True,
                        separators=(',', ':')).encode()).hexdigest())
    return _run_lean(config, source, expected, outdir, manifest['axiom_queries'], timeout, module,
                     lambda text: parse_contracts(text, manifest), contract_name, metadata)


def _records(records):
    require(type(records) is dict and bool(records), 'nonempty full Expr records required')
    for name, value in records.items():
        contract_name(name)
        require(type(value) is str and '|' in value and all(x.strip() for x in value.split('|', 1)),
                'malformed full Expr record: ' + name)


def preserve_old(old, new):
    """Accepted legacy {exact_name: level_repr + "|" + type_repr} is a subset."""
    _records(old)
    _records(new)
    require(set(old) <= set(new), 'old full contracts dropped')
    for name, value in old.items():
        require(new[name] == value, 'old complete Expr/binder/universe changed: ' + name)
    return len(old)


def compare_contracts(reference, candidate, manifest, old):
    """Compare independently obtained records, not provenance or source authority.

    Callers must bind reference/candidate/old bytes independently. This pure
    comparison cannot establish how the operator obtained those inputs.
    """
    validate_manifest(manifest)
    for side in (reference, candidate):
        keys(side, ('contracts', 'axioms'), 'parsed contracts')
        _records(side['contracts'])
        require(set(side['contracts']) == set(manifest['targets']), 'full Expr target inventory mismatch')
        require(type(side['axioms']) is dict and set(side['axioms']) == set(manifest['axiom_queries']),
                'axiom query inventory mismatch')
        for values in side['axioms'].values():
            require(type(values) is list and all(type(x) is str for x in values), 'invalid axiom list')
            require(len(values) == len(set(values)) and set(values) <= _AXIOMS, 'unsupported or duplicate Lean axioms')
        preserve_old(old, side['contracts'])
    require(reference == candidate, 'reference/candidate complete Expr or axioms differ')
    return dict(status='equal', checked_contracts=len(manifest['targets']),
                checked_queries=len(manifest['axiom_queries']), preserved_contracts=len(old),
                proof_admissible=False, whole_capture_witness=False)


def main(argv=None):
    """Separate CLI; artifact_tools' existing commands and parser are unchanged."""
    import argparse
    import hashlib
    from trainverify.artifact_tools import Configuration, absolute, digest_value, emit, sha256
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    commands = {}
    for name in ('render', 'check', 'compare'):
        p = sub.add_parser(name)
        for flag in ('config', 'manifest', 'manifest-sha256'):
            p.add_argument('--' + flag, required=True)
        p.add_argument('--output')
        commands[name] = p
    p = commands['render']
    p.add_argument('--import', dest='imports', action='append', default=[])
    p.add_argument('--expr-only', action='store_true')
    p.add_argument('--source-output', required=True)
    p = commands['check']
    for flag in ('source', 'sha256', 'out-dir'):
        p.add_argument('--' + flag, required=True)
    p.add_argument('--module')
    p.add_argument('--timeout', type=int, default=120)
    p = commands['compare']
    for flag in ('reference-stdout', 'reference-sha256', 'candidate-stdout',
                 'candidate-sha256', 'old-records', 'old-sha256'):
        p.add_argument('--' + flag, required=True)
    args = parser.parse_args(argv)
    try:
        config = Configuration.load(args.config)
        manifest = validate_manifest(config.read_json(args.manifest, args.manifest_sha256))
        if args.command == 'render':
            source = dump_contracts(args.imports, manifest, emit_axioms=not args.expr_only)
            target = absolute(args.source_output)
            with target.open('x') as stream:
                stream.write(source)
            report = dict(status='rendered', source=str(target), source_sha256=sha256(target),
                          manifest=args.manifest, manifest_sha256=args.manifest_sha256,
                          kernel_checked=False, proof_admissible=False)
        elif args.command == 'check':
            report = run_contracts(config, args.source, args.sha256, args.out_dir, manifest,
                                   args.timeout, args.module)
        else:
            def read_stdout(path, digest):
                digest_value(digest)
                data = config.resolve(path).read_bytes()
                require(hashlib.sha256(data).hexdigest() == digest, 'stdout hash mismatch: ' + path)
                return parse_contracts(data.decode('utf-8'), manifest)
            reference = read_stdout(args.reference_stdout, args.reference_sha256)
            candidate = read_stdout(args.candidate_stdout, args.candidate_sha256)
            old = config.read_json(args.old_records, args.old_sha256)
            report = compare_contracts(reference, candidate, manifest, old)
            report.update(reference_stdout=args.reference_stdout, reference_sha256=args.reference_sha256,
                          candidate_stdout=args.candidate_stdout, candidate_sha256=args.candidate_sha256,
                          old_records=args.old_records, old_sha256=args.old_sha256,
                          manifest=args.manifest, manifest_sha256=args.manifest_sha256,
                          kernel_checked=False,
                          scope='Pinned record equality only; kernel/source/dependency authority is separate.')
        emit(report, args.output)
        return 0
    except (ValueError, OSError, UnicodeError) as exc:
        emit(dict(status='failed', error=str(exc), proof_admissible=False))
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
