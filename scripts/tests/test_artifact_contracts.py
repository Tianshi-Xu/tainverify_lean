"""Strict full-Expr contracts, independent manifests and legacy preservation."""
import importlib.util
import json
import os
from pathlib import Path
import pytest

PRIVATE = '_private.Demo.0.Demo.hidden'
MANIFEST = {'version': 1, 'targets': ['Demo.id', PRIVATE],
            'axiom_queries': ['Demo.id', PRIVATE]}


def api():
    assert importlib.util.find_spec('trainverify.artifact_contracts'), 'full Expr checker missing'
    from trainverify import artifact_contracts
    return artifact_contracts


def wire(name, levels='[]', expr='Lean.Expr.const `True []', axioms=None):
    return 'CONTRACT_JSON|' + json.dumps({'name': name, 'level_params': levels, 'type': expr}) + '\n' + \
        'AXIOMS_JSON|' + json.dumps({'name': name, 'axioms': axioms or []}) + '\n'


def test_exact_expr_private_and_universe_roundtrip():
    subject = api()
    expr = 'Lean.Expr.forallE `x\n  (Lean.Expr.sort (Lean.Level.param `u)) | binder'
    parsed = subject.parse_contracts(wire('Demo.id', '[`u]', expr) + wire(PRIVATE), MANIFEST)
    assert parsed['contracts'] == {'Demo.id': '[`u]|' + expr, PRIVATE: '[]|Lean.Expr.const `True []'}
    assert parsed['axioms'] == {'Demo.id': [], PRIVATE: []}


@pytest.mark.parametrize('mutation', [
    'unknown-prefix', 'duplicate-contract', 'duplicate-axiom', 'missing',
    'replacement', 'unknown-axiom', 'duplicate-axiom-value', 'extra-field',
    'duplicate-json-key', 'blank-line', 'trailing-noise', 'empty-type',
], ids=str)
def test_strict_stdout_rejection(mutation):
    good = wire('Demo.id') + wire(PRIVATE)
    alternatives = {
        'unknown-prefix': good.replace('CONTRACT_JSON', 'BOGUS', 1),
        'duplicate-contract': good + good.splitlines()[0] + '\n',
        'duplicate-axiom': good + good.splitlines()[1] + '\n',
        'missing': wire('Demo.id'),
        'replacement': good.replace(PRIVATE, '_private.Demo.1.hidden'),
        'unknown-axiom': wire('Demo.id', axioms=['sorryAx']) + wire(PRIVATE),
        'duplicate-axiom-value': wire('Demo.id', axioms=['propext', 'propext']) + wire(PRIVATE),
        'extra-field': good.replace('"type":', '"ignored": 1, "type":', 1),
        'duplicate-json-key': good.replace('"name":', '"name": "other", "name":', 1),
        'blank-line': good + '\n',
        'trailing-noise': good + 'warning: not a contract\n',
        'empty-type': wire('Demo.id', expr='') + wire(PRIVATE),
    }
    with pytest.raises(ValueError): api().parse_contracts(alternatives[mutation], MANIFEST)


@pytest.mark.parametrize('manifest', [
    {'version': True, 'targets': ['Demo.id'], 'axiom_queries': ['Demo.id']},
    {'version': 1, 'targets': [], 'axiom_queries': ['Demo.id']},
    {'version': 1, 'targets': ['Demo.id', 'Demo.id'], 'axiom_queries': ['Demo.id']},
    {'version': 1, 'targets': ['Demo.id'], 'axiom_queries': []},
    {'version': 1, 'targets': ['Demo.id'], 'axiom_queries': ['Demo.id', 'Demo.id']},
    {'version': 1, 'targets': ['Demo.id'], 'axiom_queries': ['Other']},
    {'version': 1, 'targets': ['Demo.id\n'], 'axiom_queries': ['Demo.id']},
    {'version': 1, 'targets': ['Demo.id'], 'axiom_queries': ['Demo.id'], 'discovered': True},
], ids=['bool-version', 'empty', 'duplicate', 'no-axioms', 'duplicate-query', 'uncovered', 'invalid-name', 'extra-key'])
def test_independent_manifest_rejection(manifest):
    with pytest.raises(ValueError): api().parse_contracts(wire('Demo.id'), manifest)


def test_compare_independent_sides_and_preserve_legacy_values():
    subject = api()
    reference = subject.parse_contracts(wire('Demo.id') + wire(PRIVATE), MANIFEST)
    candidate = subject.parse_contracts(wire(PRIVATE) + wire('Demo.id'), MANIFEST)
    old = {PRIVATE: reference['contracts'][PRIVATE]}
    result = subject.compare_contracts(reference, candidate, MANIFEST, old)
    assert result['status'] == 'equal'
    assert result['checked_contracts'] == 2 and result['preserved_contracts'] == 1
    assert result['proof_admissible'] is False


@pytest.mark.parametrize('mutation', ['binder', 'universe', 'private-name', 'drop', 'axiom', 'old-change', 'old-drop'])
def test_compare_rejects_changed_or_removed_contracts(mutation):
    subject = api()
    reference = subject.parse_contracts(wire('Demo.id') + wire(PRIVATE), MANIFEST)
    candidate = json.loads(json.dumps(reference))
    old = {PRIVATE: reference['contracts'][PRIVATE]}
    if mutation == 'binder': candidate['contracts']['Demo.id'] += ' changed binder'
    elif mutation == 'universe': candidate['contracts']['Demo.id'] = candidate['contracts']['Demo.id'].replace('[]', '[`u]', 1)
    elif mutation == 'private-name': candidate['contracts']['_private.Demo.1.hidden'] = candidate['contracts'].pop(PRIVATE)
    elif mutation == 'drop': del candidate['contracts'][PRIVATE]
    elif mutation == 'axiom': candidate['axioms']['Demo.id'] = ['propext']
    elif mutation == 'old-change':
        reference['contracts'][PRIVATE] += ' coherent change'
        candidate['contracts'][PRIVATE] = reference['contracts'][PRIVATE]
    elif mutation == 'old-drop': old['Demo.old'] = '[]|Lean.Expr.const `True []'
    with pytest.raises(ValueError): subject.compare_contracts(reference, candidate, MANIFEST, old)


def test_joint_print_axioms_with_expr_only_dump():
    subject = api()
    source = subject.dump_contracts(['Lean'], MANIFEST, emit_axioms=False)
    assert 'collectAxioms' not in source
    text = wire('Demo.id').splitlines()[0] + '\n' + wire(PRIVATE).splitlines()[0] + '\n'
    text += "'Demo.id' depends on axioms: [propext]\n"
    text += "'" + PRIVATE + "' does not depend on any axioms\n"
    parsed = subject.parse_contracts(text, MANIFEST)
    assert parsed['axioms'] == {'Demo.id': ['propext'], PRIVATE: []}
    with pytest.raises(ValueError): subject.parse_contracts(text + wire('Demo.id').splitlines()[1], MANIFEST)
    with pytest.raises(ValueError): subject.parse_contracts(text.replace('propext', 'foreignAxiom'), MANIFEST)


def test_print_axiom_query_preserves_prime_name():
    name = "Demo.fact'"
    manifest = dict(version=1, targets=[name], axiom_queries=[name])
    text = wire(name).splitlines()[0] + "\n'Demo.fact'' does not depend on any axioms\n"
    assert api().parse_contracts(text, manifest)['axioms'] == {name: []}


def test_independent_axiom_superset_is_explicit():
    manifest = dict(MANIFEST, axiom_queries=MANIFEST['axiom_queries'] + ['Demo.extra'])
    extra = 'AXIOMS_JSON|{"name":"Demo.extra","axioms":[]}\n'
    assert api().parse_contracts(wire('Demo.id') + wire(PRIVATE) + extra, manifest)['axioms']['Demo.extra'] == []
    with pytest.raises(ValueError): api().parse_contracts(wire('Demo.id') + wire(PRIVATE), manifest)


def test_dump_explicit_manifest_not_compiler_census():
    subject = api()
    source = subject.dump_contracts(['Lean'], MANIFEST)
    assert 'Lean.getConstInfo' in source
    assert 'repr info.levelParams' in source and 'repr info.type' in source
    assert 'Lean.collectAxioms' in source
    assert PRIVATE in source and 'getEnv' not in source
    assert subject.dump_contracts([], MANIFEST).startswith('run_cmd do')


@pytest.mark.skipif(not os.environ.get('TV_CONTRACT_LEAN'), reason='explicit pinned Lean required')
def test_real_lean_dump_receipt_and_independent_comparison(tmp_path):
    subject = api()
    from trainverify.artifact_tools import Configuration, sha256
    lean = Path(os.environ['TV_CONTRACT_LEAN'])
    stdlib = lean.parent.parent / 'lib/lean'
    work = Path(os.environ.get('TV_CONTRACT_CHECKS', str(tmp_path)))
    work.mkdir(parents=True, exist_ok=True)
    bindings = work / 'bindings.json'
    bindings.write_text(json.dumps({str(stdlib / 'Lean.olean'): sha256(stdlib / 'Lean.olean')}))
    layout = work / 'layout.json'
    layout.write_text(json.dumps(dict(version=1, relocations=[],
        binding_sets=[dict(path=str(bindings), sha256=sha256(bindings), field=[], base=None)],
        lean=dict(executable=str(lean), sha256=sha256(lean), paths=[str(stdlib)]))))
    config = Configuration.load(layout)
    manifest = {'version': 1, 'targets': ['Demo.id', '_private.Demo.0.Demo.hidden'],
                'axiom_queries': ['Demo.id', '_private.Demo.0.Demo.hidden']}
    reports = []
    # Independently authored definitions, same module identity for private names.
    bodies = [
        'universe u\nnamespace Demo\ntheorem id {α : Sort u} (x : α) : x = x := rfl\n'
        'private theorem hidden : True := True.intro\nend Demo\n',
        'universe u\nnamespace Demo\ntheorem id {α : Sort u} (x : α) : x = x := Eq.refl x\n'
        'private theorem hidden : True := by trivial\nend Demo\n',
    ]
    for side, body in zip(('reference', 'candidate'), bodies):
        source = work / (side + '.lean')
        legacy_check = (
            'run_cmd do\n'
            '  let info ← Lean.getConstInfo `Demo.id\n'
            '  let old ← (m!"{repr info.levelParams}|{repr info.type}").toString\n'
            '  let current := (repr info.levelParams).pretty ++ "|" ++ (repr info.type).pretty\n'
            '  unless old == current do throwError "legacy Expr representation changed"\n')
        source.write_text('import Lean\n' + body + legacy_check + subject.dump_contracts([], manifest))
        if side == 'reference':
            report = subject.run_contracts(config, str(source), sha256(source), work / side,
                                           manifest, timeout=60, module='Demo')
        else:
            manifest_path = work / 'targets.json'; manifest_path.write_text(json.dumps(manifest))
            assert subject.main(['check', '--config', str(layout), '--source', str(source),
                '--sha256', sha256(source), '--out-dir', str(work / side), '--module', 'Demo',
                '--manifest', str(manifest_path), '--manifest-sha256', sha256(manifest_path),
                '--timeout', '60']) == 0
            report = json.loads((work / side / 'result.json').read_text())
        assert report['status'] == 'checked' and report['kernel_checked'] is True
        for key in ('source', 'object', 'log', 'stdout', 'stderr'):
            assert sha256(report[key]) == report[key + '_sha256']
        assert report['dependency_objects'] == {str(stdlib / 'Lean.olean'): sha256(stdlib / 'Lean.olean')}
        assert report['manifest'] == manifest and report['command'][1] == '-j1'
        assert report['proof_admissible'] is False
        assert json.loads((work / side / 'result.json').read_text()) == report
        reports.append(report)
    parsed = [{k: r[k] for k in ('contracts', 'axioms')} for r in reports]
    assert parsed[0] == parsed[1]
    assert 'Lean.Expr.forallE' in parsed[0]['contracts']['Demo.id']
    old = {'_private.Demo.0.Demo.hidden': parsed[0]['contracts']['_private.Demo.0.Demo.hidden']}
    comparison = subject.compare_contracts(*parsed, manifest, old)
    (work / 'comparison.json').write_text(json.dumps(comparison, indent=2))
    assert comparison['preserved_contracts'] == 1


def test_cli_render_compare_pins_and_legacy(tmp_path, capsys):
    subject = api()
    from scripts.tests.test_artifact_tools import fixture
    from trainverify.artifact_tools import sha256
    config, _, _, _ = fixture(tmp_path)
    manifest = tmp_path / 'targets.json'; manifest.write_text(json.dumps(MANIFEST))
    base = ['--config', str(config), '--manifest', str(manifest), '--manifest-sha256', sha256(manifest)]
    source = tmp_path / 'Contracts.lean'
    assert subject.main(['render', *base, '--import', 'Lean', '--source-output', str(source)]) == 0
    assert source.read_text() == subject.dump_contracts(['Lean'], MANIFEST)
    reference = tmp_path / 'reference.log'; reference.write_text(wire('Demo.id') + wire(PRIVATE))
    candidate = tmp_path / 'candidate.log'; candidate.write_text(wire(PRIVATE) + wire('Demo.id'))
    old = tmp_path / 'old.json'; old.write_text(json.dumps({PRIVATE: '[]|Lean.Expr.const `True []'}))
    output = tmp_path / 'comparison.json'
    args = ['compare', *base, '--reference-stdout', str(reference), '--reference-sha256', sha256(reference),
            '--candidate-stdout', str(candidate), '--candidate-sha256', sha256(candidate),
            '--old-records', str(old), '--old-sha256', sha256(old)]
    assert subject.main([*args, '--output', str(output)]) == 0
    report = json.loads(output.read_text())
    assert report['status'] == 'equal' and report['kernel_checked'] is False
    assert report['reference_sha256'] == sha256(reference)
    candidate.write_text(candidate.read_text() + 'noise\n')
    rejected = tmp_path / 'must-not-exist.json'
    assert subject.main([*args, '--output', str(rejected)]) == 1
    assert not rejected.exists()
    assert 'hash mismatch' in capsys.readouterr().out


@pytest.mark.skipif(not os.environ.get('TV_CONTRACT_LEAN'), reason='explicit pinned Lean required')
@pytest.mark.parametrize('case', ['unknown-stdout', 'unknown-axiom', 'missing-target'])
def test_real_lean_rejects_invalid_contract_evidence(tmp_path, case):
    subject = api()
    from trainverify.artifact_tools import Configuration, sha256
    lean = Path(os.environ['TV_CONTRACT_LEAN'])
    stdlib = lean.parent.parent / 'lib/lean'
    base = Path(os.environ.get('TV_CONTRACT_CHECKS', str(tmp_path)))
    work = base / case; work.mkdir(parents=True, exist_ok=False)
    bindings = work / 'bindings.json'
    bindings.write_text(json.dumps({str(stdlib / 'Lean.olean'): sha256(stdlib / 'Lean.olean')}))
    config = Configuration(dict(version=1, relocations=[],
        binding_sets=[dict(path=str(bindings), sha256=sha256(bindings), field=[], base=None)],
        lean=dict(executable=str(lean), sha256=sha256(lean), paths=[str(stdlib)])))
    manifest = dict(version=1, targets=['Demo.fact'], axiom_queries=['Demo.fact'])
    body = 'theorem Demo.fact : True := True.intro\n'
    if case == 'unknown-stdout': body += '#eval IO.println "unanticipated stdout"\n'
    elif case == 'unknown-axiom': body = 'axiom Demo.foreign : True\ntheorem Demo.fact : True := Demo.foreign\n'
    elif case == 'missing-target': body = 'theorem Demo.other : True := True.intro\n'
    source = work / 'Input.lean'
    source.write_text('import Lean\n' + body + subject.dump_contracts([], manifest))
    with pytest.raises(ValueError):
        subject.run_contracts(config, str(source), sha256(source), work / 'check', manifest, 60, 'Demo')
    report = json.loads((work / 'check/result.json').read_text())
    assert report['status'] == 'failed' and report.get('kernel_checked') is not True
    assert report['proof_admissible'] is False
    assert sha256(report['stdout']) == report['stdout_sha256']
    assert sha256(report['log']) == report['log_sha256']


def test_new_runner_rejects_before_creating_outputs(tmp_path):
    subject = api()
    from scripts.tests.test_artifact_tools import fixture
    from trainverify.artifact_tools import Configuration
    config_path, _, _, _ = fixture(tmp_path)
    source = tmp_path / 'source.lean'; source.write_text('import Lean\n')
    out = tmp_path / 'must-not-exist'
    with pytest.raises(ValueError, match='source hash mismatch'):
        subject.run_contracts(Configuration.load(config_path), str(source), '0' * 64, out, MANIFEST)
    assert not out.exists()
    duplicate = dict(MANIFEST, targets=['Demo.id', 'Demo.id'])
    with pytest.raises(ValueError, match='duplicate'):
        subject.run_contracts(None, 'unread', '0' * 64, out, duplicate)
    assert not out.exists()


def test_axiom_only_parser_stays_strict():
    from trainverify.artifact_lean import parse_axioms
    with pytest.raises(ValueError, match='unexpected Lean output'):
        parse_axioms(wire('Demo.id'), ['Demo.id'])
