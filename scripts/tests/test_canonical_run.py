"""Small real publication tests; compiler control-flow fixtures are NOT captures."""
import importlib
import importlib.util
import json
from dataclasses import replace

import pytest

from Verdict import runtime_world as world
from scripts.tests.test_runtime_world_aggregate_cap import bundle


def api():
    assert importlib.util.find_spec('trainverify.canonical_run') is not None, 'canonical observer missing'
    return importlib.import_module('trainverify.canonical_run')


def small_world():
    artifact = bundle()
    receipt = dict(artifact.receipt, public_complete=False, execution_complete=False,
                   source_defined_operations_are_torch_refinement=False,
                   execution_order={'sm': [1], 'pm': [2]}, fullrefs={'sm': [(1, 2)]})
    return replace(artifact, receipt=receipt)


@pytest.mark.parametrize('flag', ['public_complete', 'proof_admissible', 'execution_complete',
                                 'source_defined_operations_are_torch_refinement'])
def test_live_receipt_cannot_claim_public_completion(tmp_path, flag):
    artifact = small_world()
    artifact.receipt[flag] = True
    dest = tmp_path / 'published' / 'RuntimeWorld.lean'
    world.publish(artifact, dest)
    with pytest.raises(ValueError, match='flags'):
        api().readback(dest, artifact.receipt, artifact.lean, artifact.supporting_sources)


@pytest.mark.parametrize('mutation', ['bool', 'float', 'order', 'missing', 'changed', 'extra', 'imports'])
def test_readback_rejects_corruption(tmp_path, mutation):
    artifact = small_world()
    dest = tmp_path / 'published' / 'RuntimeWorld.lean'
    world.publish(artifact, dest)
    receipt_path = dest.parent / 'world-receipt.json'
    row = json.loads(receipt_path.read_text())
    if mutation == 'bool': row['execution_order']['sm'] = [True]
    elif mutation == 'float': row['execution_order']['sm'] = [1.0]
    elif mutation == 'order': row['proof_bundle']['dependency_order'].reverse()
    elif mutation == 'imports': row['proof_bundle']['modules'][-1]['imports'].pop()
    elif mutation == 'missing': (dest.parent / next(iter(artifact.supporting_sources))).unlink()
    elif mutation == 'changed': dest.write_text(dest.read_text() + '--changed\n')
    elif mutation == 'extra': (dest.parent / 'Other.lean').write_text('')
    receipt_path.write_text(json.dumps(row))
    with pytest.raises((ValueError, FileNotFoundError)):
        api().readback(dest, artifact.receipt, artifact.lean, artifact.supporting_sources)


def test_real_world_publication_wire_readback(tmp_path):
    run = api()
    artifact = small_world()
    dest = tmp_path / 'published' / 'RuntimeWorld.lean'
    world.publish(artifact, dest)
    checked = run.readback(dest, artifact.receipt, artifact.lean, artifact.supporting_sources)
    assert checked['published'] is True
    assert checked['public_complete'] is False
    assert checked['torch_refinement'] is False
    assert checked['source_bytes'] == sum(len(s.encode()) for s in [artifact.lean, *artifact.supporting_sources.values()])


def control_flow(tmp_path, mode='ok', local_bundle=False):
    """Mock ONLY heavy compiler/render/bind; publication and budget are real."""
    from types import SimpleNamespace
    from Verdict.runtime_lineage import RuntimeLineageBlocked
    from Verdict import graph_to_lean
    run = api()
    assert hasattr(run, 'observe'), 'complete compiler observer missing'
    artifact = small_world()
    values = [{}, {}, [], {}, {}, artifact.receipt['execution_order']]
    before = [id(x) for x in values]
    contents_before = json.dumps(values, sort_keys=True)
    detail = {'proof_admissible': False, 'kernel_value_proved': False,
              'public_complete': False, 'torch_refinement': False, 'rows': [(1, 2)]}
    stage = SimpleNamespace(__name__='Verdict.runtime_fixture', render=lambda *a: ('-- stage\n', detail))
    initial = SimpleNamespace(bind=lambda *a: values[4], _proof_bundle=world._proof_bundle)
    feed = SimpleNamespace(bind=lambda *a, **k: artifact)
    world_proxy = SimpleNamespace(render=lambda *a: artifact, publish=world.publish)
    world_proxy._proof_bundle = world._proof_bundle
    if local_bundle: del initial._proof_bundle
    received = []
    def stage_render(*args):
        received.append(args)
        return '-- stage\n', detail
    stage.render = stage_render
    def attach(current, sm, pm, parameters, lineages, validation):
        bound = initial.bind(sm, pm, parameters, lineages, validation)
        if mode != 'missing-stage':
            stage.render(sm, pm, lineages, validation, bound, current.receipt['execution_order'])
        receipt = dict(current.receipt, fixture=detail)
        text = current.lean
        if mode == 'budget': text += '--' + ' ' * graph_to_lean.GENERATED_LEAN_SOURCE_LIMIT + '\n'
        owner = world_proxy if local_bundle else initial
        receipt['proof_bundle'] = owner._proof_bundle(text, current.supporting_sources)
        return replace(current, lean=text, receipt=receipt)
    initial.attach = attach
    def main():
        print('compiler fixture: NOT an actual capture')
        __import__('os').write(1, b'native fixture log\n')
        if mode == 'wrong-exception': raise RuntimeError(run.EXPECTED_BLOCK)
        if mode == 'wrong-message': raise RuntimeLineageBlocked('different', {})
        current = world_proxy.render(values[0], values[1], [], [])
        current = feed.bind(current, values[0], values[1])
        current = initial.attach(current, values[0], values[1], {}, values[2], values[3])
        if mode != 'no-publish': world_proxy.publish(current, tmp_path / 'published' / 'RuntimeWorld.lean')
        if mode == 'generated':
            (tmp_path / 'GeneratedData.lean').write_text('bad')
        raise RuntimeLineageBlocked(run.EXPECTED_BLOCK, {'world_definitions': current.receipt})
    owner = world_proxy if local_bundle else initial
    originals = [initial.attach, initial.bind, owner._proof_bundle, feed.bind, world_proxy.render, world_proxy.publish, stage.render]
    compiler = SimpleNamespace(main=main)
    state = run.observe(compiler, initial, feed, world_proxy,
                        [(stage, {'module': stage.__name__, 'receipt_key': 'fixture'})],
                        tmp_path, ['graph_to_lean'], lambda: None)
    assert originals == [initial.attach, initial.bind, owner._proof_bundle, feed.bind, world_proxy.render, world_proxy.publish, stage.render]
    assert before == [id(x) for x in values]
    assert contents_before == json.dumps(values, sort_keys=True)
    for args in received:
        assert all(a is b for a, b in zip(args, values, strict=True))
    return state


def test_complete_compiler_control_flow_and_hooks_restored(tmp_path):
    state = control_flow(tmp_path)
    assert state['passed'] is True
    assert state['published'] is True
    assert state['public_complete'] is False
    assert state['torch_refinement'] is False
    assert state['compiler_exit'] == 1
    assert state['exception']['message'] == api().EXPECTED_BLOCK
    assert (tmp_path / 'observation.json').is_file()
    assert 'NOT an actual capture' in (tmp_path / 'generator.log').read_text()
    assert 'native fixture log' in (tmp_path / 'generator.log').read_text()


@pytest.mark.parametrize('mode', ['wrong-exception', 'wrong-message', 'no-publish', 'missing-stage', 'generated'])
def test_control_flow_never_accepts_other_failures(tmp_path, mode):
    state = control_flow(tmp_path, mode)
    assert state['passed'] is False
    assert state['public_complete'] is False
    assert state['torch_refinement'] is False


def test_sealed_manifest_complete_cover_and_import_ownership(tmp_path):
    from types import SimpleNamespace
    run = api()
    assert hasattr(run, 'verify_source'), 'sealed source authentication missing'
    root = tmp_path / 'source'
    (root / 'Verdict').mkdir(parents=True)
    (root / 'Verdict' / 'runtime_fixture.py').write_text('# fixture\n')
    manifest = dict(version=1, root=str(root), baseline_commit='a' * 40,
                    files={'Verdict/runtime_fixture.py': run.sha256(root / 'Verdict' / 'runtime_fixture.py')}, symlinks={})
    run.verify_source(root, manifest, 'a' * 40)
    local = SimpleNamespace(__file__=str(root / 'Verdict' / 'runtime_fixture.py'))
    run.verify_imports(root, manifest, {'Verdict.runtime_fixture': local})
    foreign = SimpleNamespace(__file__=str(tmp_path / 'runtime_fixture.py'))
    with pytest.raises(ValueError, match='import'):
        run.verify_imports(root, manifest, {'Verdict.runtime_fixture': foreign})
    for mutation in ['missing', 'changed', 'extra']:
        target = root / 'Verdict' / 'runtime_fixture.py'
        if mutation == 'missing': target.unlink()
        elif mutation == 'changed': target.write_text('# changed\n')
        else:
            target.write_text('# fixture\n')
            (root / 'extra').write_text('uncovered')
        with pytest.raises(ValueError, match='source'):
            run.verify_source(root, manifest, 'a' * 40)


def test_input_pin_drift_and_complete_rank_inventory(tmp_path):
    run = api()
    assert hasattr(run, 'input_identity'), 'input identity authentication missing'
    from types import SimpleNamespace
    seed = {}
    for field in ['sm_capture', 'pm_capture', 'sm_run', 'pm_run']:
        folder = tmp_path / field
        folder.mkdir()
        seed[field] = str(folder)
        for name in (['capture.pkl', 'capture.json'] if 'capture' in field else ['receipt.json']):
            (folder / name).write_text('{}')
    rank = tmp_path / 'rank'
    rank.mkdir()
    (rank / 'gencode0.py').write_text('# rank\n')
    seedpath = tmp_path / 'seed.json'
    seedpath.write_text(json.dumps(seed))
    batch = tmp_path / 'batch.json'
    batch.write_text('{}')
    paths = [seedpath, batch, rank / 'gencode0.py'] + [p for field in ['sm_capture', 'pm_capture'] for p in __import__('pathlib').Path(seed[field]).iterdir()]
    recipe = dict(pins={str(p): run.sha256(p) for p in paths}, seed_bundle=str(seedpath),
                  batch_authority=str(batch), rank_code_directory=str(rank))
    config = SimpleNamespace(resolve=lambda p: __import__('pathlib').Path(p), verify=lambda: None,
                             read_json=lambda p, h: json.loads(__import__('pathlib').Path(p).read_text()))
    identity = run.input_identity(config, recipe)
    run.verify_inputs(config, recipe, identity)
    from pathlib import Path
    moved = tmp_path / 'relocated.pkl'
    moved.write_text('{}')
    logical = str(Path(seed['sm_capture']) / 'capture.pkl')
    config.resolve = lambda p: moved if str(p) == logical else Path(p)
    with pytest.raises(ValueError, match='capture.*relocation'):
        run.input_identity(config, recipe)
    config.resolve = lambda p: Path(p)
    (rank / 'extra.py').write_text('# unexpected\n')
    with pytest.raises(ValueError, match='rank'):
        run.verify_inputs(config, recipe, identity)
    (rank / 'extra.py').unlink()
    (__import__('pathlib').Path(seed['pm_run']) / 'receipt.json').write_text('{"drift":true}')
    with pytest.raises(ValueError, match='input'):
        run.verify_inputs(config, recipe, identity)
    batch.write_text('changed')
    with pytest.raises(ValueError): run.input_identity(config, recipe)


def test_bookkeeping_recheck_does_not_rerun(tmp_path, monkeypatch):
    state = control_flow(tmp_path)
    assert state['passed']
    row = json.loads((tmp_path / 'observation.json').read_text())
    monkeypatch.setattr(world, 'publish', lambda *a: pytest.fail('must not republish'))
    assert api().check_observation(tmp_path, row, lambda: None)['published']
    def drift(): raise ValueError('input drift')
    with pytest.raises(ValueError, match='input drift'):
        api().check_observation(tmp_path, row, drift)
    row['compiler_exit'] = True
    with pytest.raises(ValueError, match='exception'):
        api().check_observation(tmp_path, row, lambda: None)


def test_namespace_imports_and_backend_ownership(tmp_path):
    from types import SimpleNamespace
    run = api()
    root = tmp_path / 'source'
    (root / 'trainverify').mkdir(parents=True)
    (root / 'Verdict' / 'nnscaler_backend').mkdir(parents=True)
    (root / 'trainverify' / 'observer.py').write_text('# tool\n')
    (root / 'Verdict' / 'nnscaler_backend' / '__init__.py').write_text('')
    (root / 'scripts').mkdir()
    (root / 'scripts' / 'helper.py').write_text('')
    manifest = run.tree_identity(root)
    namespace = SimpleNamespace(__file__=None, __path__=[str(root / 'trainverify'), str(root / 'trainverify')])
    run.verify_imports(root, manifest, {'trainverify': namespace})
    run.verify_imports(root, manifest, {'torch.ops': SimpleNamespace(__file__='_ops.py')})
    with pytest.raises(ValueError, match='import'):
        run.verify_imports(root, manifest, {'trainverify': SimpleNamespace(__file__=None, __path__=[str(tmp_path)])})
    with pytest.raises(ValueError, match='import'):
        run.verify_imports(root, manifest, {'nnscaler_backend': SimpleNamespace(__file__=str(tmp_path / '__init__.py'))})
    with pytest.raises(ValueError, match='import'):
        run.verify_imports(root, manifest, {'scripts': SimpleNamespace(__file__=None, __path__=[str(tmp_path)])})


def test_observation_binds_command_for_offline_recheck(tmp_path):
    command = tmp_path / 'command.json'
    command.write_text('{"fixture":true}\n')
    state = control_flow(tmp_path)
    assert state['passed']
    observation = json.loads((tmp_path / 'observation.json').read_text())
    assert observation.get('command_sha256') == api().sha256(command)
    assert 'post_imports' in observation


@pytest.mark.parametrize('mutation', ['partial', 'order', 'scalar', 'peer-order'])
def test_offline_stage_inventory_is_not_partial(tmp_path, mutation):
    assert control_flow(tmp_path)['passed']
    row = json.loads((tmp_path / 'observation.json').read_text())
    if mutation == 'partial': row['stages'].clear()
    elif mutation == 'order': row['top_stages'] = ['other', 'fixture']
    elif mutation == 'scalar': row['stages']['fixture'][0]['detail']['rows'][0][0] = True
    else: row['stages']['fixture'][0]['detail']['rows'][0].reverse()
    with pytest.raises(ValueError): api().check_observation(tmp_path, row, lambda: None)


def test_cli_help_exposes_run_and_recheck():
    run = api()
    assert hasattr(run, 'main'), 'CLI missing'
    with pytest.raises(SystemExit) as exc: run.main(['--help'])
    assert exc.value.code == 0


@pytest.mark.parametrize('local_bundle', [False, True])
def test_first_budget_failure_retains_complete_unpublished_payload(tmp_path, local_bundle):
    state = control_flow(tmp_path, 'budget', local_bundle=local_bundle)
    assert state['passed'] is False
    assert state['published'] is False
    assert not (tmp_path / 'published').exists()
    payload = json.loads((tmp_path / 'diagnostic' / 'first-refused-bundle.json').read_text())
    assert payload['published'] is False
    assert payload['args'][1] == small_world().supporting_sources
    assert payload['args'][0].startswith(small_world().lean)
    with pytest.raises(ValueError, match='byte limit'):
        world._proof_bundle(*payload['args'], **payload['kwargs'])


def test_real_portable_renderer_publish_and_readback(tmp_path):
    from scripts.tests.test_runtime_scoped_prefix import collective_world
    inputs = tmp_path / 'inputs'
    inputs.mkdir()
    artifact = collective_world(inputs, 2, chain=True)
    dest = tmp_path / 'published' / 'RuntimeWorld.lean'
    world.publish(artifact, dest)
    assert api().readback(dest, artifact.receipt, artifact.lean, artifact.supporting_sources)['published']


def test_recheck_cli_preserves_original_evidence_without_rerun(tmp_path, monkeypatch):
    run = api()
    command = tmp_path / 'command.json'
    command.write_text(json.dumps({'out': str(tmp_path)}))
    assert control_flow(tmp_path)['passed']
    observation = tmp_path / 'observation.json'
    before = {p.name: p.read_bytes() for p in [command, observation, tmp_path / 'generator.log', tmp_path / 'run-result.json']}
    # Only external-source preflight is replaced in this control-flow fixture.
    monkeypatch.setattr(run, '_prepare', lambda c: ([{'receipt_key': 'fixture'}], {}, lambda: None))
    monkeypatch.setattr(run, 'observe', lambda *a: pytest.fail('must not rerun'))
    args = ['recheck', '--run-dir', str(tmp_path), '--command-sha256', run.sha256(command),
            '--observation-sha256', run.sha256(observation), '--output', str(tmp_path / 'rechecked.json')]
    assert run.main(args) == 0
    assert json.loads((tmp_path / 'rechecked.json').read_text())['bookkeeping_only'] is True
    assert all((tmp_path / name).read_bytes() == content for name, content in before.items())
    assert run.main(args) == 2  # no clobber


def test_run_cli_real_preflight_mock_compiler_failure(tmp_path, monkeypatch):
    """Real CLI/config/manifests, deliberately mocked compiler; NOT capture."""
    from pathlib import Path
    from Verdict import graph_to_lean
    run = api()
    seed = {}
    for field in ('sm_capture', 'pm_capture', 'sm_run', 'pm_run'):
        path = tmp_path / field
        path.mkdir()
        seed[field] = str(path)
        for name in (('capture.pkl', 'capture.json') if 'capture' in field else ('run.json',)):
            (path / name).write_text('{}')
    rank = tmp_path / 'rank'
    rank.mkdir()
    (rank / 'gencode0.py').write_text('# fixture\n')
    seedpath = tmp_path / 'seed.json'
    seedpath.write_text(json.dumps(seed))
    batch = tmp_path / 'batch.json'
    batch.write_text('{}')
    files = [seedpath, batch, rank / 'gencode0.py'] + [p for field in ('sm_capture', 'pm_capture') for p in Path(seed[field]).iterdir()]
    recipe = dict(version=1, pins={str(p): run.sha256(p) for p in files}, seed_bundle=str(seedpath),
                  batch_authority=str(batch), rank_code_directory=str(rank))
    recipepath = tmp_path / 'recipe.json'
    recipepath.write_text(json.dumps(recipe))
    layout = tmp_path / 'layout.json'
    layout.write_text(json.dumps(dict(version=1, relocations=[], lean=None,
        binding_sets=[dict(path=str(recipepath), sha256=run.sha256(recipepath), field=['pins'], base=None)])))
    root = Path(run.__file__).resolve().parents[1]
    manifest = tmp_path / 'source.json'
    manifest.write_text(json.dumps(dict(version=1, root=str(root), baseline_commit='a' * 40, **run.tree_identity(root))))
    stages = tmp_path / 'stages.json'
    stages.write_text(json.dumps(dict(version=1, stages=[dict(module='Verdict.runtime_frontier_middle_exchange_values',
                                                             receipt_key='frontier_middle_exchange_values')])))
    entered = []
    def main():
        entered.append(True)
        raise RuntimeError('fixture compiler error: NOT capture')
    monkeypatch.setattr(graph_to_lean, 'main', main)
    out = tmp_path / 'run'
    args = ['run', '--config', str(layout), '--recipe', str(recipepath), '--recipe-sha256', run.sha256(recipepath),
            '--source-manifest', str(manifest), '--source-manifest-sha256', run.sha256(manifest),
            '--expected-commit', 'a' * 40, '--stages', str(stages), '--stages-sha256', run.sha256(stages), '--out', str(out)]
    assert run.main(args) == 2
    assert entered == [True]
    observation = json.loads((out / 'observation.json').read_text())
    command = json.loads((out / 'command.json').read_text())
    assert observation['command_sha256'] == run.sha256(out / 'command.json')
    assert observation['exception']['message'] == 'fixture compiler error: NOT capture'
    assert command['compiler_argv'][-2:] == ['--module', 'Never.GeneratedData']
    assert json.loads((out / 'runtime-seed.json').read_text()) == seed
    assert not (out / 'published').exists()
    assert run.main(args) == 2  # never rerun into an existing directory
    assert entered == [True]


def test_sealed_source_symlinks_and_commit_types_fail_closed(tmp_path):
    run = api()
    root = tmp_path / 'source'
    root.mkdir()
    (root / 'data.py').write_text('# data\n')
    (root / 'alias.py').symlink_to('data.py')
    manifest = dict(version=1, root=str(root), baseline_commit='a' * 40, **run.tree_identity(root))
    run.verify_source(root, manifest, 'a' * 40)
    with pytest.raises(ValueError): run.verify_source(root, manifest, 'a' * 39)
    manifest['version'] = True
    with pytest.raises(ValueError): run.verify_source(root, manifest, 'a' * 40)
    (root / 'alias.py').unlink()
    (root / 'alias.py').symlink_to(tmp_path / 'elsewhere')
    with pytest.raises(ValueError): run.tree_identity(root)
