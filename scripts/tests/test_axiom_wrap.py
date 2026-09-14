"""Regression for Lean's normal multiline #print axioms output."""
import json
import os
from pathlib import Path
import pytest
from trainverify.artifact_lean import parse_axioms
from trainverify.artifact_contracts import parse_contracts

NAME = 'TrainVerify.Denote.RuntimeWorld.frontierScoreMatmulRead_sm_1304'
# Verbatim first record of reference-kernel/matmul/stdout.log (Lean 4.32.2).
WRAPPED = ("'TrainVerify.Denote.RuntimeWorld.frontierScoreMatmulRead_sm_1304' depends on axioms: [propext,\n"
           " Classical.choice,\n Quot.sound]\n")
VALUES = ['propext', 'Classical.choice', 'Quot.sound']


def expr(name=NAME):
    return 'CONTRACT_JSON|' + json.dumps(dict(name=name, level_params='[]',
        type='Lean.Expr.const `True []')) + '\n'


def parse(text, mode):
    if mode == 'axiom-only':
        return parse_axioms(text, [NAME])
    manifest = dict(version=1, targets=[NAME], axiom_queries=[NAME])
    return parse_contracts(expr() + text, manifest)['axioms']


@pytest.mark.parametrize('mode', ['axiom-only', 'mixed'])
def test_verbatim_real_wrapped_record(mode):
    assert parse(WRAPPED, mode) == {NAME: VALUES}


@pytest.mark.parametrize('mode', ['axiom-only', 'mixed'])
@pytest.mark.parametrize('mutation', [
    'unknown', 'contract-inside', 'axiom-json-inside', 'blank-inside',
    'space-line-inside', 'leading-blank', 'trailing-blank', 'trailing-space',
    'trailing-noise', 'after-bracket', 'duplicate', 'missing', 'extra-query',
    'unclosed', 'no-comma', 'trailing-comma', 'foreign', 'duplicate-value',
    'unindented', 'control-separator',
])
def test_wrapped_records_fail_closed(mode, mutation):
    bad = {
        'unknown': WRAPPED.replace(' Classical.choice,', ' warning: ignored'),
        'contract-inside': WRAPPED.replace(' Classical.choice,', expr().rstrip('\n')),
        'axiom-json-inside': WRAPPED.replace(' Classical.choice,', 'AXIOMS_JSON|{"name":"Other","axioms":[]}'),
        'blank-inside': WRAPPED.replace(' Classical.choice,', '\n Classical.choice,'),
        'space-line-inside': WRAPPED.replace(' Classical.choice,', ' \n Classical.choice,'),
        'leading-blank': '\n' + WRAPPED,
        'trailing-blank': WRAPPED + '\n',
        'trailing-space': WRAPPED + ' ',
        'trailing-noise': WRAPPED + 'unexpected\n',
        'after-bracket': WRAPPED.replace(']', '] ignored'),
        'duplicate': WRAPPED + WRAPPED,
        'missing': '',
        'extra-query': WRAPPED + "'Other' does not depend on any axioms\n",
        'unclosed': WRAPPED.replace(']', ''),
        'no-comma': WRAPPED.replace('propext,', 'propext'),
        'trailing-comma': WRAPPED.replace('Quot.sound]', 'Quot.sound,]'),
        'foreign': WRAPPED.replace('Quot.sound', 'sorryAx'),
        'duplicate-value': WRAPPED.replace('Quot.sound', 'propext'),
        'unindented': WRAPPED.replace('\n Classical', '\nClassical'),
        'control-separator': WRAPPED.replace('\n', '\v'),
    }[mutation]
    with pytest.raises(ValueError):
        parse(bad, mode)


@pytest.mark.parametrize('mode', ['axiom-only', 'mixed'])
@pytest.mark.parametrize('padding', ['\n', ' ', '\n \n'])
def test_single_line_record_does_not_hide_boundary_noise(mode, padding):
    text = "'" + NAME + "' does not depend on any axioms\n"
    with pytest.raises(ValueError):
        parse(padding + text, mode)
    with pytest.raises(ValueError):
        parse(text + padding, mode)


@pytest.mark.parametrize('values', [
    '[propext, Classical.choice, Quot.sound]',
    '[propext,\n Classical.choice, Quot.sound]',
    '[propext, Classical.choice,\n Quot.sound]',
    '[propext,\n  Classical.choice,\n  Quot.sound]',
])
@pytest.mark.parametrize('mode', ['axiom-only', 'mixed'])
def test_standard_list_layouts(values, mode):
    assert parse("'" + NAME + "' depends on axioms: " + values, mode) == {NAME: VALUES}


def test_mixed_wrapped_private_prime_and_json_order():
    private = "_private.Demo.0.Demo.hidden'"
    manifest = dict(version=1, targets=[private, NAME], axiom_queries=[private, NAME, 'Other'])
    text = WRAPPED.replace(NAME, private) + expr(private) + expr()
    text += 'AXIOMS_JSON|{"name":"Other","axioms":[]}\n' + WRAPPED
    parsed = parse_contracts(text, manifest)
    assert parsed['axioms'] == {private: VALUES, NAME: VALUES, 'Other': []}
    # Axiom-only retains its narrower identifier domain.
    with pytest.raises(ValueError):
        parse_axioms(WRAPPED.replace(NAME, private), [private])
    for bad in ['_private.Demo.00.hidden', '_private.Demo.-1.hidden']:
        with pytest.raises(ValueError):
            parse_contracts(text.replace(private, bad),
                dict(version=1, targets=[bad, NAME], axiom_queries=[bad, NAME, 'Other']))


@pytest.mark.skipif(not os.environ.get('TV_CONTRACT_LEAN'), reason='explicit pinned Lean required')
@pytest.mark.parametrize('mode', ['axiom-only', 'mixed'])
def test_real_lean_normal_long_name_wrap(tmp_path, mode):
    from trainverify.artifact_lean import run_lean
    from trainverify.artifact_contracts import dump_contracts, run_contracts
    from trainverify.artifact_tools import Configuration, sha256
    lean = Path(os.environ['TV_CONTRACT_LEAN'])
    stdlib = lean.parent.parent / 'lib/lean'
    base = Path(os.environ.get('TV_CONTRACT_CHECKS', str(tmp_path)))
    work = base / ('wrapped-' + mode)
    work.mkdir(parents=True, exist_ok=False)
    bindings = work / 'bindings.json'
    bindings.write_text(json.dumps({str(stdlib / 'Lean.olean'): sha256(stdlib / 'Lean.olean')}))
    config = Configuration(dict(version=1, relocations=[],
        binding_sets=[dict(path=str(bindings), sha256=sha256(bindings), field=[], base=None)],
        lean=dict(executable=str(lean), sha256=sha256(lean), paths=[str(stdlib)])))
    manifest = dict(version=1, targets=[NAME], axiom_queries=[NAME])
    source = work / 'Wrapped.lean'
    # Default pretty-print width; no synthetic stdout or pp.width override.
    body = ('import Lean\ntheorem ' + NAME + ' (p : Prop) : p ∨ ¬p := Classical.em p\n'
            '#print axioms ' + NAME + '\n')
    if mode == 'mixed':
        body += dump_contracts([], manifest, emit_axioms=False)
    source.write_text(body)
    if mode == 'axiom-only':
        report = run_lean(config, str(source), sha256(source), work / 'check', [NAME], 60, 'Wrapped')
    else:
        report = run_contracts(config, str(source), sha256(source), work / 'check', manifest, 60, 'Wrapped')
    assert report['status'] == 'checked' and report['inner_exit'] == 0
    assert report['kernel_checked'] is True and report['axioms'] == {NAME: VALUES}
    stdout = Path(report['stdout']).read_text()
    assert stdout.startswith(WRAPPED)
    if mode == 'mixed':
        assert 'Lean.Expr.forallE' in report['contracts'][NAME]
    for key in ('source', 'object', 'stdout', 'stderr', 'log'):
        assert sha256(report[key]) == report[key + '_sha256']
    assert report['command'][1] == '-j1' and report['lean_num_threads'] == 1
    assert json.loads((work / 'check/result.json').read_text()) == report
