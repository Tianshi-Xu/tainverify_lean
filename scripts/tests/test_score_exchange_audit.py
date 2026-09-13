"""Narrow independent raw audit tests; captures are trusted local inputs only."""
import importlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import hashlib
import pickle

import pytest


def api():
    assert importlib.util.find_spec('trainverify.score_exchange_audit') is not None, 'missing independent raw audit public module'
    return importlib.import_module('trainverify.score_exchange_audit')


def test_public_check_rejects_scope_under_optimization():
    module = api()
    assert callable(module.check_raw)
    assert module.REPORT_VERSION == 1
    # A minimal empty census exercises the final scope guard, not an earlier
    # missing-key rejection. Explicit exit status remains active under -O.
    probe = '''
from trainverify.score_exchange_audit import check_raw
old = dict(frontier_units=[], units=[])
new = dict(frontier_units=[], retained_units=[], deferred_units=[], units=[], reads=[],
           consumed_frontier_indices=[], proof_admissible=True, kernel_value_proved=False,
           public_complete=False, torch_refinement=False)
try:
    check_raw([], [], old, new, dict(source_hashes={}))
except ValueError as exc:
    if 'scope' not in str(exc):
        raise SystemExit(str(exc))
else:
    raise SystemExit('scope guard disappeared under -O')
'''
    result = subprocess.run([sys.executable, '-O', '-c', probe], capture_output=True, text=True)
    assert result.returncode == 0, result.stdout + result.stderr


def configuration(tmp_path, relocations=()):
    from trainverify.artifact_tools import Configuration
    path = tmp_path / 'config.json'
    path.write_text(json.dumps(dict(version=1, relocations=list(relocations),
        binding_sets=[dict(path='/logical/bindings.json', sha256='0' * 64, field=[], base=None)], lean=None)))
    return Configuration.load(path)


@pytest.mark.parametrize('bad_file', ['sm/capture.pkl', 'sm/capture.json', 'pm/capture.pkl', 'pm/capture.json'])
@pytest.mark.parametrize('fault', ['malformed', 'mismatch', 'missing'])
def test_all_four_pins_precede_any_pickle(tmp_path, bad_file, fault):
    module = api()
    assert callable(getattr(module, 'load_worlds', None)), 'missing authenticated world loader'
    marker = tmp_path / 'pickle-executed'

    class Malicious:
        def __reduce__(self):
            return Path.touch, (marker,)

    payloads = {'sm/capture.pkl': pickle.dumps(Malicious()), 'sm/capture.json': b'{}',
                'pm/capture.pkl': pickle.dumps(None), 'pm/capture.json': b'{}'}
    pins = {}
    for name, data in payloads.items():
        path = tmp_path / name
        path.parent.mkdir(exist_ok=True)
        path.write_bytes(data)
        pins['/logical/' + name] = hashlib.sha256(data).hexdigest()
    if fault == 'missing':
        del pins['/logical/' + bad_file]
    else:
        pins['/logical/' + bad_file] = 'invalid-digest' if fault == 'malformed' else '0' * 64
    config = configuration(tmp_path, [dict(kind='directory', source='/logical', target=str(tmp_path))])
    with pytest.raises(ValueError, match='SHA256|hash mismatch|missing capture pin'):
        module.load_worlds(config, pins, '/logical/sm', '/logical/pm')
    assert not marker.exists(), 'an earlier authenticated pickle ran before all four payloads were authenticated'


def test_actual_saved_raw_and_candidate_corruptions(tmp_path, monkeypatch):
    import copy
    detail_root = os.environ.get('TRAINVERIFY_SCORE_EXCHANGE_DETAIL_ROOT')
    capture_root = os.environ.get('TRAINVERIFY_CAPTURE_ROOT')
    if not detail_root or not capture_root:
        pytest.skip('set trusted local score-exchange detail and capture roots')
    module = api()
    detail_root, capture_root = Path(detail_root), Path(capture_root)
    world = json.loads((detail_root / 'world-binding.json').read_bytes())
    old = json.loads((detail_root / 'score-matmul-detail.json').read_bytes())
    new = json.loads((detail_root / 'detail.json').read_bytes())
    config = configuration(tmp_path)
    sm, pm = module.load_worlds(config, world['source_hashes'], capture_root / 'global-b2', capture_root / 'p2-r4')

    def forbidden_read(*args, **kwargs):
        raise AssertionError('pure check must not read world paths')

    with monkeypatch.context() as guard:
        guard.setattr(Path, 'read_bytes', forbidden_read)
        report = module.check_raw(sm, pm, old, new, world)
    assert report['passed'] is True
    assert report['version'] == 1
    assert {key: report[key] for key in ('reads', 'units', 'frontier', 'retained', 'deferred')} == dict(reads=4, units=2, frontier=6, retained=2, deferred=2)
    assert report['new_capture'] is report['kernel'] is report['torch_refinement'] is False
    assert len(report['raw_capture_pins']) == 4
    assert len(report['synthetic_integer_layout_oracle']) == 2
    assert all(g['axis3_reconstruction'] and g['receiver_reversal_rejected'] and g['remote_peer_reversal_rejected'] for g in report['synthetic_integer_layout_oracle'])
    controls = []
    for fault, message in [('parent', 'parent shape/bounds'), ('shape', 'shape/parent name'),
                           ('peer', 'ordered peer ports'), ('receiver', 'ordered receiver'),
                           ('suffix', 'BW suffix'), ('division', 'division signature/scope'),
                           ('scope', 'raw diagnostic scope'), ('frontier', 'complete ordered frontier')]:
        candidate = copy.deepcopy(new)
        row = candidate['units'][0]
        if fault == 'parent':
            row['local_steps'][0]['inputs'][0]['parent_shape'][0] += 1
        elif fault == 'shape':
            row['local_steps'][0]['inputs'][0]['endpoint']['shape'][0] += 1
        elif fault == 'peer':
            row['local_steps'][0]['inputs'].reverse()
        elif fault == 'receiver':
            row['local_steps'][0]['local_index'] += 1
        elif fault == 'suffix':
            candidate['reads'][0]['operand_nonwrite_source_indices'] = []
        elif fault == 'division':
            row['downstream_consumers'][0]['value_proved'] = True
        elif fault == 'scope':
            candidate['torch_refinement'] = True
        else:
            candidate['frontier_units'].reverse()
        with pytest.raises(ValueError, match=message):
            module.check_raw(sm, pm, old, candidate, world)
        controls.append(fault)
    # This optional receipt belongs outside the source/evidence inputs.
    output = os.environ.get('TRAINVERIFY_SCORE_EXCHANGE_REPORT')
    if output:
        Path(output).write_text(json.dumps(dict(raw_check=report, rejected_controls=controls,
            raw_cells=dict(sm=len(sm), pm=len(pm))), indent=2) + '\n')
