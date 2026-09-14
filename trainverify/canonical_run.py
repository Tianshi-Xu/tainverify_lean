"""Observe a complete saved-capture compiler run; never confer public authority.

Operator-owned manifests/configuration are trust roots. This is not a sandbox
against concurrent same-user mutation. No fragment replacement or budget knob.
"""
import hashlib
import json
import os
import re
import sys
import time
import traceback
from contextlib import ExitStack, contextmanager, redirect_stdout, redirect_stderr
from pathlib import Path
from unittest.mock import patch

from trainverify.artifact_tools import emit, require, sha256, strict_json

EXPECTED_BLOCK = ('runtime-world-render/public-adapter: world definitions rendered; '
                  'scoped dependent chain/input adapter/DP mathematics unavailable; values unproved')
_STAGE_FLAGS = ('proof_admissible', 'kernel_value_proved', 'public_complete', 'torch_refinement')


def snapshot(value):
    return strict_json(wire(value))


@contextmanager
def _native_log(log):
    """Keep native library/subprocess output alongside Python compiler logs."""
    saved = [os.dup(fd) for fd in (1, 2)]
    try:
        sys.stdout.flush(); sys.stderr.flush()
        for fd in (1, 2): os.dup2(log.fileno(), fd)
        yield
    finally:
        log.flush()
        for fd, old in zip((1, 2), saved):
            os.dup2(old, fd)
            os.close(old)


def _check_calls(observation):
    """Validate optional new call evidence; old top-level-only logs still work."""
    if 'calls' not in observation and 'call_counts' not in observation:
        return
    calls, counts = observation.get('calls'), observation.get('call_counts')
    require(type(calls) is list and bool(calls) and type(counts) is dict, 'missing call evidence')
    active, tops, actual = [], [], {}
    for index, row in enumerate(calls):
        require(type(row) is dict and type(row.get('call_id')) is int
                and row['call_id'] == index, 'call ID mismatch')
        end = row.get('end_call_id')
        require(type(end) is int and index < end <= len(calls), 'call interval mismatch')
        while active and active[-1]['end_call_id'] <= index:
            active.pop()
        parent = row.get('parent_call_id')
        require(type(row.get('depth')) is int and row['depth'] == len(active)
                and ((not active and parent is None) or (active and type(parent) is int
                     and parent == active[-1]['call_id'] and end <= active[-1]['end_call_id'])),
                'call parent/depth mismatch')
        name = row.get('name')
        require(name in ('render', 'bind', 'attach', 'publish')
                and (not active or name == 'render'), 'unexpected nested lifecycle call')
        require(row.get('status') == 'returned' and 'exception' not in row, 'unsuccessful observed call')
        args, kwargs, result = row.get('arg_ids'), row.get('kwarg_ids'), row.get('result_id')
        require(type(args) is list and type(kwargs) is dict and type(result) is int and result > 0
                and all(type(v) is int and v > 0 for v in [*args, *kwargs.values()]), 'call object IDs malformed')
        actual[name] = actual.get(name, 0) + 1
        if not active:
            tops.append(row)
        active.append(row)
    require(wire(actual) == wire(counts), 'call count mismatch')
    require([row['name'] for row in tops] == observation['events'], 'call lifecycle mismatch')
    for previous, current in zip(tops, tops[1:]):
        require(bool(current['arg_ids']) and current['arg_ids'][0] == previous['result_id'],
                'call world identity mismatch')


def check_observation(out, observation, verify):
    """Bookkeeping only: no compiler, attachment or render invocation."""
    from Verdict.runtime_lineage import RuntimeLineageBlocked
    verify()
    require(not observation['observer_errors'], 'observer errors: ' + str(observation['observer_errors']))
    exc = observation['exception']
    require(observation['compiler_exit'] == 1 and type(observation['compiler_exit']) is int
            and exc == dict(type=RuntimeLineageBlocked.__module__ + '.' + RuntimeLineageBlocked.__qualname__,
                            message=EXPECTED_BLOCK), 'unexpected compiler exit/exception')
    require(observation['events'] == ['render', 'bind', 'attach', 'publish'], 'incomplete canonical render/bind/attach/publish')
    _check_calls(observation)
    require(observation['six_identity_checked'] is True, 'missing six-object authority observation')
    require(observation['top_stages'] == observation['expected_stages'], 'stage membership/order mismatch')
    payload = observation['attached']
    for key in observation['expected_stages']:
        rows = observation['stages'].get(key, [])
        require(bool(rows), 'missing stage: ' + key)
        for row in rows:
            require(wire(row['detail']) == wire(payload['receipt'].get(key)), 'stage detail mismatch: ' + key)
            require(all(row['detail'].get(flag) is False for flag in _STAGE_FLAGS), 'stage flags must remain false')
    require(wire(observation['blocked_receipt']['world_definitions']) == wire(payload['receipt']), 'blocked world receipt mismatch')
    require(not any(Path(out).rglob('GeneratedData.lean')), 'unexpected public GeneratedData')
    require(sha256(Path(out) / 'generator.log') == observation['log_sha256'], 'generator log drift')
    if 'command_sha256' in observation:
        require(sha256(Path(out) / 'command.json') == observation['command_sha256'], 'command identity drift')
    return readback(Path(out) / 'published' / 'RuntimeWorld.lean', **payload)


def observe(compiler, initial, feed, world, stages, out, argv, verify):
    """Call originals without modifying arguments/results/exceptions or budgets.

    Modules are explicit to allow small control-flow unit tests. The CLI imports
    and authenticates the actual compiler modules; it exposes no mock hook.
    Observation errors are deferred until the real compiler finishes, including
    attachment. Recursive predecessor calls are observed, not forced each-once.
    """
    out = Path(out)
    observation = dict(events=[], calls=[], call_counts={}, stages={}, top_stages=[], expected_stages=[s['receipt_key'] for _, s in stages],
                       observer_errors=[], six_identity_checked=False, compiler_exit=None, exception=None)
    if (out / 'command.json').exists():
        observation['command_sha256'] = sha256(out / 'command.json')
    live = dict(depth=0, attaching=False, calls=[])
    def watch(action):
        try:
            action()
        except Exception as exc:
            observation['observer_errors'].append(type(exc).__name__ + ': ' + str(exc))
    def event(name):
        if len(live['calls']) == 1:
            observation['events'].append(name)
    def tracked(name, original):
        """Separate compiler lifecycle from nested authority re-renders.

        Entry-ordered call IDs retain parent identity even when completion is
        recursive. Never overwrite the compiler's top-level world with a child.
        """
        def call(*args, **kwargs):
            active = live['calls']
            row = dict(call_id=len(observation['calls']), name=name,
                       parent_call_id=active[-1]['call_id'] if active else None,
                       depth=len(active), arg_ids=[id(x) for x in args],
                       kwarg_ids={k: id(v) for k, v in kwargs.items()}, status='entered')
            observation['calls'].append(row)
            counts = observation['call_counts']
            counts[name] = counts.get(name, 0) + 1
            active.append(row)
            try:
                result = original(*args, **kwargs)
                row.update(status='returned', result_id=id(result))
                return result
            except BaseException as exc:
                row.update(status='raised', exception=dict(
                    type=type(exc).__module__ + '.' + type(exc).__qualname__, message=str(exc)))
                raise
            finally:
                row['end_call_id'] = len(observation['calls'])
                active.pop()
        return call
    render_original, feed_original = world.render, feed.bind
    attach_original, bind_original, publish_original = initial.attach, initial.bind, world.publish
    # This source imports _proof_bundle locally inside attach; patch its owner,
    # not a nonexistent initial global. A future global alias is also supported.
    owner = initial if hasattr(initial, '_proof_bundle') else world
    bundle_original = owner._proof_bundle
    def render(*args, **kwargs):
        result = render_original(*args, **kwargs)
        if len(live['calls']) == 1:
            live['rendered'] = result
        event('render')
        return result
    def feed_bind(*args, **kwargs):
        watch(lambda: require(args[0] is live.get('rendered'), 'bind did not receive rendered world'))
        result = feed_original(*args, **kwargs)
        live['fed'] = result
        event('bind')
        return result
    def bind(*args, **kwargs):
        result = bind_original(*args, **kwargs)
        def record():
            a = live['attach_args']
            expected = (a[1], a[2], a[3], a[4], a[5])
            require(not kwargs and len(args) == 5 and all(x is y for x, y in zip(args, expected)),
                    'initial bind object identity mismatch')
            live['six'] = (a[1], a[2], a[4], a[5], result, a[0].receipt['execution_order'])
            observation['six_ids'] = [id(x) for x in live['six']]
        watch(record)
        return result
    def attach(*args, **kwargs):
        live['attach_args'] = args
        watch(lambda: require(not kwargs and len(args) == 6 and args[0] is live.get('fed'), 'attach world identity mismatch'))
        live['attaching'] = True
        try:
            result = attach_original(*args, **kwargs)
        finally:
            live['attaching'] = False
        live['attached'] = result
        watch(lambda: observation.update(attached=snapshot(dict(receipt=result.receipt, lean=result.lean,
                                                                supporting_sources=result.supporting_sources))))
        event('attach')
        return result
    def publish(*args, **kwargs):
        watch(lambda: require(args[0] is live.get('attached') and Path(args[1]) == out / 'published' / 'RuntimeWorld.lean',
                              'publish did not receive complete attached world/destination'))
        result = publish_original(*args, **kwargs)
        event('publish')
        return result
    def bundle(*args, **kwargs):
        try:
            return bundle_original(*args, **kwargs)
        except BaseException as exc:
            if live['attaching'] and type(exc) is ValueError and re.fullmatch(
                    r'world bundle generated Lean source exceeds [0-9]+ byte limit: [0-9]+ bytes total', str(exc)):
                def preserve():
                    target = out / 'diagnostic' / 'first-refused-bundle.json'
                    if not target.exists():
                        emit(dict(args=args, kwargs=kwargs, error=str(exc), published=False, proof_admissible=False),
                             target, print_report=False)
                watch(preserve)
            raise
    def stage_wrapper(module, spec):
        original = module.render
        key = spec['receipt_key']
        def call(*args, **kwargs):
            top = live['depth'] == 0
            def identity():
                require(live['attaching'] and not kwargs and len(args) == 6
                        and all(x is y for x, y in zip(args, live['six'], strict=True)), 'stage six-object identity mismatch')
                observation['six_identity_checked'] = True
            watch(identity)
            live['depth'] += 1
            try:
                result = original(*args, **kwargs)
            finally:
                live['depth'] -= 1
            def record():
                text, detail = result
                observation['stages'].setdefault(key, []).append(dict(detail=snapshot(detail),
                    source_sha256=hashlib.sha256(text.encode('utf-8')).hexdigest()))
                if top: observation['top_stages'].append(key)
            watch(record)
            return result
        return call
    started = time.monotonic()
    with (out / 'generator.log').open('x', buffering=1) as log:
        with _native_log(log), redirect_stdout(log), redirect_stderr(log), ExitStack() as stack:
            for module, name, replacement in [(world, 'render', tracked('render', render)), (feed, 'bind', tracked('bind', feed_bind)),
                    (initial, 'attach', tracked('attach', attach)), (initial, 'bind', bind), (world, 'publish', tracked('publish', publish)),
                    (owner, '_proof_bundle', bundle)]:
                stack.enter_context(patch.object(module, name, replacement))
            for module, spec in stages:
                stack.enter_context(patch.object(module, 'render', stage_wrapper(module, spec)))
            stack.enter_context(patch.object(sys, 'argv', argv))
            try:
                compiler.main()
                observation['compiler_exit'] = 0
            except BaseException as exc:
                observation['compiler_exit'] = exc.code if isinstance(exc, SystemExit) and type(exc.code) is int else 1
                observation['exception'] = dict(type=type(exc).__module__ + '.' + type(exc).__qualname__, message=str(exc))
                if hasattr(exc, 'receipt'):
                    watch(lambda: observation.update(blocked_receipt=snapshot(exc.receipt)))
                traceback.print_exc()
    observation['seconds'] = time.monotonic() - started
    observation['log_sha256'] = sha256(out / 'generator.log')
    watch(lambda: observation.update(post_imports=verify()))
    # Preserve immutable original evidence BEFORE fallible bookkeeping.
    emit(observation, out / 'observation.json', print_report=False)
    report = dict(passed=False, published=False, public_complete=False, torch_refinement=False, kernel_checked=False,
                  compiler_exit=observation['compiler_exit'], exception=observation['exception'], seconds=observation['seconds'])
    try:
        report.update(check_observation(out, observation, verify), passed=True)
    except Exception as exc:
        report['error'] = type(exc).__name__ + ': ' + str(exc)
        report['publication_observed'] = 'publish' in observation['events']
    emit(report, out / 'run-result.json', print_report=False)
    return report


def wire(value):
    """Compare exact JSON scalars, retaining array order and normalizing tuples."""
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False)


def readback(destination, receipt, lean, supporting_sources):
    """Recompute the production closed inventory and read every published byte."""
    from Verdict import runtime_world as world
    destination = Path(destination)
    require(all(receipt.get(flag) is False for flag in ('proof_admissible', 'public_complete',
            'execution_complete', 'source_defined_operations_are_torch_refinement')), 'world flags must remain false')
    expected = dict(receipt, proof_bundle=world._proof_bundle(lean, supporting_sources, destination.name))
    actual = strict_json((destination.parent / 'world-receipt.json').read_bytes())
    require(wire(actual) == wire(expected), 'published receipt mismatch')
    sources = {destination.name: lean, **supporting_sources}
    require({p.name for p in destination.parent.iterdir()} == set(sources) | {'world-receipt.json'},
            'published membership mismatch')
    for name, text in sources.items():
        path = destination.parent / name
        require(not path.is_symlink() and path.read_bytes() == text.encode('utf-8'), 'published source mismatch: ' + name)
    return dict(published=True, public_complete=False, torch_refinement=False, kernel_checked=False,
                source_bytes=sum(len(text.encode('utf-8')) for text in sources.values()))


def tree_identity(root):
    """Exact regular-file bytes and internal symlink spellings; no exclusions."""
    root = Path(root)
    require(root.is_dir() and not root.is_symlink(), 'source/input root must be a real directory')
    files, links = {}, {}
    for path in sorted(root.rglob('*')):
        name = str(path.relative_to(root))
        if path.is_symlink():
            require(path.resolve().is_relative_to(root.resolve()) and path.resolve().is_file(), 'source/input external or directory symlink')
            links[name] = str(path.readlink())
        elif path.is_file(): files[name] = sha256(path)
        else: require(path.is_dir(), 'source/input special file')
    return dict(files=files, symlinks=links)


def verify_source(root, manifest, commit):
    from trainverify.artifact_tools import absolute, digest_value, keys
    root = absolute(str(root))
    keys(manifest, ('version', 'root', 'baseline_commit', 'files', 'symlinks'), 'source manifest')
    require(type(manifest['version']) is int and manifest['version'] == 1, 'source manifest version')
    require(type(commit) is str and re.fullmatch('[0-9a-f]{40}', commit) is not None, 'source baseline commit format')
    require(manifest['baseline_commit'] == commit and manifest['root'] == str(root), 'source baseline/root mismatch')
    require(type(manifest['files']) is dict and bool(manifest['files']) and type(manifest['symlinks']) is dict, 'source manifest coverage')
    for value in manifest['files'].values(): digest_value(value)
    require(wire(tree_identity(root)) == wire({k: manifest[k] for k in ('files', 'symlinks')}), 'source membership/hash drift')


def verify_imports(root, manifest, modules=None):
    """Check all loaded local namespaces, including bare Verdict imports."""
    root = Path(root).resolve()
    modules = sys.modules if modules is None else modules
    bare = {Path(p).stem for p in manifest['files'] if p.startswith('Verdict/') and p.count('/') == 1 and p.endswith('.py')}
    packages = {'Verdict', 'trainverify'}
    for name in manifest['files']:
        parts = Path(name).parts
        if name.endswith('.py') and len(parts) > 1:
            packages.add(parts[0])
        if name.endswith('/__init__.py'):
            if len(parts) == 2: packages.add(parts[0])
            elif len(parts) == 3 and parts[0] == 'Verdict': packages.add(parts[1])
    loaded = {}
    for name, module in list(modules.items()):
        filename = getattr(module, '__file__', None)
        owned = name.split('.')[0] in packages or name in bare
        if not filename:
            if owned:
                paths = [Path(p).resolve() for p in getattr(module, '__path__', [])]
                candidates = [base.joinpath(*name.split('.')) for base in (root, root / 'Verdict')]
                allowed = {p for p in candidates if any(f.startswith(str(p.relative_to(root)) + '/') for f in manifest['files'])}
                require(bool(paths) and set(paths) <= allowed,
                        'import namespace belongs to wrong source root: ' + name)
                loaded[name] = dict(namespace_paths=[str(p) for p in paths])
            continue
        # Native/dynamic packages (e.g. torch.ops) use synthetic relative names,
        # not source imports from the current working directory.
        if not owned and not Path(filename).is_absolute(): continue
        path = Path(filename).resolve()
        if not owned and not path.is_relative_to(root): continue
        require(path.is_relative_to(root), 'import belongs to wrong source root: ' + name)
        rel = str(path.relative_to(root))
        require(rel in manifest['files'] and sha256(path) == manifest['files'][rel], 'import source is not pinned: ' + name)
        loaded[name] = dict(path=str(path), sha256=manifest['files'][rel])
    return loaded


def input_identity(config, recipe):
    from trainverify.artifact_tools import absolute, digest_value
    config.verify()
    pins = recipe['pins']
    require(type(pins) is dict and bool(pins), 'input pins required')
    resolved = {}
    for path, digest in pins.items():
        absolute(path); digest_value(digest)
        current = config.resolve(path)
        require(sha256(current) == digest, 'input pin hash mismatch: ' + path)
        require(str(current) not in resolved, 'input relocation alias collision')
        resolved[str(current)] = digest
    require(recipe['seed_bundle'] in pins and recipe['batch_authority'] in pins, 'input seed/batch must be pinned')
    seed = config.read_json(recipe['seed_bundle'], pins[recipe['seed_bundle']])
    require(set(seed) == {'sm_capture', 'pm_capture', 'sm_run', 'pm_run'}, 'input seed fields mismatch')
    for field in ('sm_capture', 'pm_capture'):
        for name in ('capture.pkl', 'capture.json'):
            logical = str(absolute(seed[field]) / name)
            require(logical in pins, 'input capture pair is not pinned')
            require(config.resolve(logical) == config.resolve(seed[field]) / name,
                    'input capture file/directory relocation mismatch')
    rank = config.resolve(recipe['rank_code_directory'])
    rankpins = {p for p in resolved if Path(p).parent == rank and p.endswith('.py')}
    require(bool(rankpins) and {str(p) for p in rank.glob('*.py')} == rankpins, 'rank-code inventory mismatch')
    auxiliary = {field: tree_identity(config.resolve(seed[field])) for field in ('sm_run', 'pm_run')}
    return dict(pins=resolved, seed={k: str(config.resolve(v)) for k, v in seed.items()}, auxiliary=auxiliary,
                rank_code_directory=str(rank), batch_authority=str(config.resolve(recipe['batch_authority'])))


def verify_inputs(config, recipe, identity):
    require(wire(input_identity(config, recipe)) == wire(identity), 'input identity drift')


def _pinned_json(path, digest):
    from trainverify.artifact_tools import absolute, digest_value
    path = absolute(path)
    digest_value(digest)
    require(sha256(path) == digest, 'pinned JSON mismatch: ' + str(path))
    return strict_json(path.read_bytes())


def _stages(data):
    from trainverify.artifact_tools import keys
    keys(data, ('version', 'stages'), 'stage configuration')
    require(type(data['version']) is int and data['version'] == 1, 'stage configuration version')
    rows = data['stages']
    require(type(rows) is list and bool(rows), 'explicit expected stages required')
    for row in rows:
        keys(row, ('module', 'receipt_key'), 'stage')
        require(type(row['module']) is str and re.fullmatch(r'Verdict\.runtime_[A-Za-z0-9_]+', row['module']) is not None,
                'invalid stage module')
        require(type(row['receipt_key']) is str and re.fullmatch('[A-Za-z0-9_]+', row['receipt_key']) is not None,
                'invalid stage receipt key')
    for key in ('module', 'receipt_key'):
        require(len({r[key] for r in rows}) == len(rows), 'duplicate expected stage')
    return rows


def _prepare(command):
    """Authenticate operator roots; returned verifier also checks subsequent drift."""
    from trainverify.artifact_tools import Configuration
    root = Path(command['root'])
    require(Path(__file__).resolve().parents[1] == root, 'observer imported from wrong root')
    manifest = _pinned_json(command['source_manifest'], command['source_manifest_sha256'])
    verify_source(root, manifest, command['expected_commit'])
    config = Configuration.load(command['config'])
    require(config.config_sha256 == command['config_sha256'], 'configuration drift')
    recipe = config.read_json(command['recipe'], command['recipe_sha256'])
    require(type(recipe['version']) is int and recipe['version'] == 1, 'recipe version')
    specs = _stages(_pinned_json(command['stages'], command['stages_sha256']))
    identity = input_identity(config, recipe)
    if 'input_identity' in command:
        require(wire(command['input_identity']) == wire(identity), 'input identity drift')
    def verify():
        require(sha256(command['config']) == command['config_sha256'], 'configuration drift')
        for key in ('source_manifest', 'stages'):
            _pinned_json(command[key], command[key + '_sha256'])
        config.read_json(command['recipe'], command['recipe_sha256'])
        verify_source(root, manifest, command['expected_commit'])
        verify_inputs(config, recipe, identity)
        require(sha256(command['python']) == command['python_sha256'], 'Python executable drift')
        if 'runtime_seed_sha256' in command:
            require(sha256(Path(command['out']) / 'runtime-seed.json') == command['runtime_seed_sha256'], 'derived seed drift')
        return verify_imports(root, manifest)
    return specs, identity, verify


def main(argv=None):
    import argparse
    import importlib
    from trainverify.artifact_tools import absolute
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action', required=True)
    run = sub.add_parser('run', help='execute original saved-capture compiler through publication')
    for flag in ('config', 'recipe', 'recipe-sha256', 'source-manifest', 'source-manifest-sha256',
                 'expected-commit', 'stages', 'stages-sha256', 'out'):
        run.add_argument('--' + flag, required=True)
    repair = sub.add_parser('recheck', help='read existing exact run; never rerun compiler')
    for flag in ('run-dir', 'command-sha256', 'observation-sha256', 'output'):
        repair.add_argument('--' + flag, required=True)
    args = parser.parse_args(argv)
    try:
        sys.dont_write_bytecode = True
        if args.action == 'recheck':
            out = absolute(args.run_dir)
            command = _pinned_json(str(out / 'command.json'), args.command_sha256)
            require(command['out'] == str(out), 'run root identity mismatch')
            specs, identity, verify = _prepare(command)
            observation = _pinned_json(str(out / 'observation.json'), args.observation_sha256)
            require(observation['expected_stages'] == [s['receipt_key'] for s in specs], 'expected stage configuration drift')
            require(observation['command_sha256'] == args.command_sha256, 'observation/command binding mismatch')
            report = dict(check_observation(out, observation, verify), passed=True, bookkeeping_only=True,
                          command_sha256=args.command_sha256, observation_sha256=args.observation_sha256)
            emit(report, args.output)
            return 0
        root = Path(__file__).resolve().parents[1]
        out = absolute(args.out)
        require(not out.resolve().is_relative_to(root), 'output must be outside source root')
        out.parent.mkdir(parents=True, exist_ok=True)
        out.mkdir(exist_ok=False)
        command = {k: v for k, v in vars(args).items() if k != 'action'}
        command.update(root=str(root), config_sha256=sha256(args.config), python=str(Path(sys.executable).resolve()),
                       python_sha256=sha256(sys.executable), invocation=sys.argv, out=str(out))
        try:
            specs, identity, verify = _prepare(command)
            command['input_identity'] = identity
            emit(identity['seed'], out / 'runtime-seed.json', print_report=False)
            command['runtime_seed_sha256'] = sha256(out / 'runtime-seed.json')
            compiler_argv = ['graph_to_lean', '--sm-pkl', str(Path(identity['seed']['sm_capture']) / 'capture.pkl'),
                '--pm-pkl', str(Path(identity['seed']['pm_capture']) / 'capture.pkl'),
                '--verifier-cache-dir', str(out / 'capture-cache'),
                '--runtime-rank-code-directory', identity['rank_code_directory'],
                '--runtime-batch-authority', identity['batch_authority'],
                '--runtime-input-handoff', identity['seed']['pm_run'], '--runtime-seed-bundle', str(out / 'runtime-seed.json'),
                '--runtime-world-definitions-out', str(out / 'published' / 'RuntimeWorld.lean'),
                '--out', str(out / 'unpublished' / 'GeneratedData.lean'), '--module', 'Never.GeneratedData']
            command['compiler_argv'] = compiler_argv
            # No historical controller imports; only the authenticated source root.
            with patch.object(sys, 'path', [str(root), str(root / 'Verdict'), *sys.path]):
                compiler, initial, feed, world = [importlib.import_module('Verdict.' + name) for name in
                    ('graph_to_lean', 'runtime_initial_relations', 'runtime_input_feed', 'runtime_world')]
                stages = [(importlib.import_module(spec['module']), spec) for spec in specs]
                command['imports'] = verify()
                emit(command, out / 'command.json', print_report=False)
                report = observe(compiler, initial, feed, world, stages, out, compiler_argv, verify)
            emit(report)
            return 0 if report['passed'] else 2
        except BaseException as exc:
            if not (out / 'command.json').exists(): emit(command, out / 'command.json', print_report=False)
            emit(dict(passed=False, public_complete=False, torch_refinement=False, error=type(exc).__name__ + ': ' + str(exc)),
                 out / 'preflight-error.json', print_report=False)
            raise
    except (ValueError, OSError, KeyError, TypeError, AttributeError, ImportError) as exc:
        print(json.dumps(dict(passed=False, error=type(exc).__name__ + ': ' + str(exc))))
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
