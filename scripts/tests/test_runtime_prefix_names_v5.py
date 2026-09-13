"""Opt-in finite exact identifiers; canonical bytes remain the authority."""
import pytest
from Verdict import runtime_prefix as p

MODULE = 'TrainVerifyRuntimePrefixNamesV5'
IMPORT = f'import {MODULE}\n'
CODES = {'stepWithInputs': 'pT', 'decide_false': 'pD', 'decide_true': 'pC'}


def sample(stem='arbitraryPrefix'):
    return ('import TrainVerifyRuntimePrefixSupport\n' + p._HEADER
            + f'def {stem}InitShapes (init : Store) := True\n'
            + ''.join(f'theorem {stem}Step_{i} (init : Store) '
                      f'(hInitShapes : {stem}InitShapes init) : True := by\n'
                      '  simp only [stepWithInputs, Nat.reduceEqDiff, decide_false, decide_true, '
                      'AllToAllSourceFaithful.localStep]\n'
                      f'#print axioms {stem}Step_{i}\n' for i in range(12))
            + p._FOOTER)


def test_opt_in_roundtrip_and_profitable_selection():
    for stem in ('arbitraryPrefix', 'other_17Prefix'):
        source = sample(stem)
        old = p.compact_names(source, names_v4=True)
        assert p.compact_names(source, names_v4=True, names_v5=False) == old
        encoded = p.compact_names(source, names_v4=True, names_v5=True)
        assert f'prefix_names_v5 {stem} ! where\n' in encoded
        assert encoded.count(IMPORT) == 1
        assert 'pT, pE, pD, pC, pL' in encoded
        assert '(z_ : zS z)' in encoded
        assert p.expand_names(encoded) == source
        assert len(encoded.encode()) < len(old.encode())
        assert p.compact_names(encoded, names_v5=True) == encoded
        assert p.expand_names(encoded + '#check Outside.name\n') == source + '#check Outside.name\n'
        assert p.compact_names(source, names_v3=False, names_v5=True) == encoded
    for source in ('def shortPrefixRead_0 := 0\n',
                   'def shortPrefixRead_0 := stepWithInputs\n',
                   sample().replace('stepWithInputs', 'ordinaryStep')
                   .replace('decide_false', 'ordinaryFalse').replace('decide_true', 'ordinaryTrue')
                   .replace('arbitraryPrefixInitShapes', 'ordinaryShapes')):
        assert p.compact_names(source, names_v4=True, names_v5=True) == p.compact_names(source, names_v4=True)


@pytest.mark.parametrize('where', ['single', 'final_only', 'chunk', 'final', 'both', 'neither', 'mixed'])
def test_pack_support_exact_and_on_demand(where):
    body = sample().split(p._HEADER, 1)[1].split(p._FOOTER)[0]
    legacy = body.replace('arbitraryPrefixInitShapes', 'ordinaryShapes')
    for name in CODES:
        legacy = legacy.replace(name, 'ordinary' + name)
    if where in ('single', 'final_only'):
        groups = [p.ProofGroup(body, 1, (), final=where == 'final_only')]
    else:
        groups = [p.ProofGroup(body if where in ('chunk', 'both', 'mixed') else legacy, 50, ()),
                  p.ProofGroup(legacy, 50, ()),
                  p.ProofGroup(body if where in ('final', 'both') else legacy, 1, (), final=True)]
    entry, support = p.pack_proofs([groups], names_v3=True, names_v4=True, names_v5=True)
    old_entry, old_support = p.pack_proofs([groups], names_v3=True, names_v4=True)
    assert (MODULE + '.lean' in support) == (where != 'neither')
    if where != 'neither':
        assert support[p.NAMES_V5_FILE] == p.names_v5_source()
    assert p.pack_proofs([groups]) == p.pack_proofs([groups], names_v5=False)
    supports = {p.SUPPORT_FILE, p.NAMES_V3_FILE, p.NAMES_V4_FILE, MODULE + '.lean'}
    assert [n for n in support if n not in supports] == [n for n in old_support if n not in supports]
    for name, source in dict(support, Entry=entry).items():
        if name not in supports:
            assert p.expand_names(source) == p.expand_names(dict(old_support, Entry=old_entry)[name])
    for module in (p.NAMES_V3_MODULE, p.NAMES_V4_MODULE, MODULE):
        used = any(f'import {module}\n' in s for n, s in dict(support, Entry=entry).items() if n not in supports)
        assert (module + '.lean' in support) == used


@pytest.mark.parametrize('extra', [f'def {name} := 1\n' for name in ('zS', 'pT', 'pD', 'pC', 'pE', 'pL', 'z', 'pR')]
                         + ['def literal := "stepWithInputs"\n', '#check «stepWithInputs»\n',
                            '#check `stepWithInputs\n', '/- decide_false -/\n', IMPORT,
                            'import TrainVerifyRuntimePrefixNamesV5 Other\n', '#print  axioms foo\n'])
def test_collision_unsupported_original(extra):
    source = sample() + extra
    assert p.compact_names(source, names_v5=True) == source


@pytest.mark.parametrize('token', [name + suffix for name in ('stepWithInputs', 'decide_false', 'decide_true',
                                                             'arbitraryPrefixInitShapes', 'zS', 'pT', 'pD', 'pC')
                                   for suffix in ('.more', "'", '?', '!', '_more')]
                         + ['Other.stepWithInputs', 'Other.zS', 'αstepWithInputs'])
def test_exact_tokens_and_comments(token):
    extra = f'#check {token}\n-- stepWithInputs decide_false decide_true zS pT pD pC\n'
    source = sample() + extra
    encoded = p.compact_names(source, names_v5=True)
    assert 'prefix_names_v5 ' in encoded
    assert all(line in encoded for line in extra.splitlines())
    assert p.expand_names(encoded) == source


@pytest.mark.parametrize('stem', ['ordinary', 'pL', 'pE', 'zS', 'pT', 'pD', 'pC'])
@pytest.mark.parametrize('plus', ['', ' +', ' + +'])
@pytest.mark.parametrize('query', ['', ' !'])
@pytest.mark.parametrize('indent', [' ', '  '])
def test_legacy_domains_metadata_and_suffix(stem, plus, query, indent):
    body = 'def r_0 (zS pT pD pC : Nat) := (zS, pT, pD, pC)\n'
    block = ''.join(indent + line for line in body.splitlines(keepends=True))
    expected = body.replace('r_0', stem + 'Read_0')
    legacy = ''.join(import_ + f'{wrapper} {stem}{plus}{query} where\n' + block
                     for import_, wrapper in [('', 'prefix_names'),
                                              (p._NAMES_V3_IMPORT, 'prefix_names_v3'),
                                              (p._NAMES_V4_IMPORT, 'prefix_names_v4')])
    assert p.expand_names(legacy) == expected * 3
    v5 = IMPORT + f'prefix_names_v5 {stem}{plus}{query} where\n' + block
    # Token substitution must not touch stem metadata or identifiers containing aliases.
    assert p.expand_names(v5) == (f'def {stem}Read_0 ({stem}InitShapes stepWithInputs decide_false decide_true : Nat) := '
                                  f'({stem}InitShapes, stepWithInputs, decide_false, decide_true)\n')


@pytest.mark.parametrize('header', ['prefix_names_v6 ordinary where', 'prefix_names_v5 ordinary + + + where',
                                    'prefix_names_v5 ordinary ! + where', 'prefix_names_v5 ordinary !! where'])
def test_unknown_or_invalid_marker(header):
    with pytest.raises(ValueError, match='header'):
        p.expand_names(IMPORT + header + '\n def r_0 := 0\nprefix_names ordinary where\n def r_1 := 1\n')


@pytest.mark.parametrize('preamble', ['', IMPORT + IMPORT, IMPORT + '\n', p._NAMES_V4_IMPORT,
                                      'import TrainVerifyRuntimePrefixNamesV5 Other\n'])
def test_import_ownership(preamble):
    with pytest.raises(ValueError, match='import'):
        p.expand_names(preamble + 'prefix_names_v5 ordinary where\n def r_0 := zS\n')


HELPER = 'AllToAllSourceFaithful.localStep'
SIMPROC = 'Nat.reduceEqDiff'


def test_real_lean_identity_and_bad_expander_controls(tmp_path):
    """Opt-in isolated kernel probe: set TRAINVERIFY_NAMES_LEAN and LEAN_PATH.

    LEAN_PATH must contain built denote.Denote / AllToAllSourceFaithful /
    SourceScopedEval and dependencies. No lake build or shared object writes.
    Source copies use their actual module names, never runtime_prefix_names_v5.
    """
    import os
    import subprocess
    import hashlib
    import json
    from itertools import product
    lean = os.environ.get('TRAINVERIFY_NAMES_LEAN')
    if not lean:
        pytest.skip('set TRAINVERIFY_NAMES_LEAN and dependency LEAN_PATH for isolated Lean probe')
    root = tmp_path
    objects = root / 'objects'
    objects.mkdir()
    env = dict(os.environ, LEAN_NUM_THREADS='1',
               LEAN_PATH=str(objects) + ':' + os.environ.get('LEAN_PATH', ''))

    def compile_source(directory, module, source, *, ok=True, output=None):
        directory.mkdir(parents=True, exist_ok=True)
        path = directory / (module + '.lean')
        path.write_text(source)
        command = [lean, '-j1', '-DmaxHeartbeats=500000', '-o',
                   str((output or objects) / (module + '.olean')), str(path)]
        result = subprocess.run(command, cwd=directory, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)
        (directory / (module + '.log')).write_text(result.stdout)
        (directory / (module + '.json')).write_text(json.dumps(dict(
            command=command, cwd=str(directory), exit_code=result.returncode,
            source_sha256=hashlib.sha256(source.encode()).hexdigest(),
            expected_success=ok, lean_path=env['LEAN_PATH']), indent=2))
        assert (result.returncode == 0) == ok, result.stdout[:5000]
        if ok:
            assert 'sorry' not in result.stdout
        return result.stdout

    for module, source in ((p.SUPPORT_MODULE, p.support_source()),
                           (p.NAMES_V3_MODULE, p.names_v3_source()),
                           (p.NAMES_V4_MODULE, p.names_v4_source()),
                           (MODULE, p.names_v5_source())):
        compile_source(root, module, source)

    imports = ('import TrainVerifyRuntimePrefixNamesV3\n' + IMPORT
               + 'import TrainVerifyRuntimePrefixNamesV4\n'
               + 'import denote.AllToAllSourceFaithful\nimport denote.SourceScopedEval\n'
               + 'open Lean Elab Command TrainVerify.Denote TrainVerify.Denote.SourceScopedEval\n')
    audit = '''
elab "audit_decl " id:ident : command => do
  let n ← resolveGlobalConstNoOverload id
  let ci ← getConstInfo n
  logInfo m!"NAME {n} TYPE {repr ci.type} VALUE {repr (ci.value? (allowOpaque := true))}"
  let status ← liftCoreM <| getReducibilityStatus n
  logInfo m!"STATUS {n} {repr status}"
elab "audit_opacity" : command => do
  let names := PrefixOpacity.inventory.getState (← getEnv)
  for n in names do
    unless (← liftCoreM <| getReducibilityStatus n) == .irreducible do
      throwError "opacity not restored: {n}"
  logInfo m!"OPACITY {repr names}"
'''
    canonical, encoded = imports + audit, imports + audit
    configurations = list(product(['ordinary', 'pL', 'pE', 'zS', 'pT', 'pD', 'pC'], ['', ' +', ' + +'], ['', ' !'], [' ', '  ']))
    for i, (stem, plus, query, indent) in enumerate(configurations):
        prefix = f'namespace Case{i}\nnoncomputable section\n'
        # Aliases occur only in Syntax.ident; strings and comments must survive.
        body = (f'def {stem}InitShapes : Prop := True\n'
                f'theorem {stem}Shape_0 (h : {stem}InitShapes) : {stem}InitShapes := h\n'
                f'def {stem}Run_0 := @stepWithInputs\n'
                f'theorem {stem}Written_0 : (decide True, decide False) = (true, false) := by\n'
                '  simp only [decide_true, decide_false]\n'
                f'def {stem}State_0 : Nat := 7\n'
                f'attribute [local irreducible] {stem}State_0\n'
                f'record_prefix_opacity {stem}State_0\n'
                f'def {stem}Step_0 := @{HELPER}\n'
                f'theorem {stem}Read_0 : ((1 : Nat) = 2) = False := by\n'
                f'  simp only [{SIMPROC}]\n'
                f'#print axioms {stem}Read_0\n'
                'def literal : String := "pE pL zS pT pD pC"\n-- pE pL stay comments\n')
        compressed = (body.replace(stem + 'State_0', 's_0')
                      .replace(stem + 'Step_0', 't_0').replace(stem + 'Read_0', 'r_0')
                      .replace(HELPER, 'pL').replace(SIMPROC, 'pE'))
        for name, code in {stem + 'InitShapes': 'zS', stem + 'Shape_0': 'h_0',
                           stem + 'Run_0': 'u_0', stem + 'Written_0': 'w_0', **CODES}.items():
            compressed = compressed.replace(name, code)
        if query:
            compressed = compressed.replace('#print axioms ', '#a ')
        checks = (f'audit_decl {stem}InitShapes\naudit_decl {stem}Shape_0\n'
                  f'audit_decl {stem}Run_0\naudit_decl {stem}Written_0\n'
                  f'audit_decl {stem}State_0\naudit_decl {stem}Step_0\n'
                  f'audit_decl {stem}Read_0\naudit_decl literal\nend\nend Case{i}\n')
        canonical += prefix + body + checks
        encoded += prefix + f'prefix_names_v5 {stem}{plus}{query} where\n' + ''.join(
            indent + line for line in compressed.splitlines(keepends=True)) + checks
    # Old wrappers retain all new literal aliases, also as stem metadata.
    for i, wrapper in enumerate(['prefix_names', 'prefix_names_v3', 'prefix_names_v4']):
        body = 'def zSRead_0 (zS pT pD pC : Nat) := (zS, pT, pD, pC)\n'
        prefix = f'namespace Legacy{i}\n'
        checks = 'audit_decl zSRead_0\nend Legacy' + str(i) + '\n'
        canonical += prefix + body + checks
        encoded += prefix + wrapper + ' zS where\n def r_0 (zS pT pD pC : Nat) := (zS, pT, pD, pC)\n' + checks
    canonical += 'restore_prefix_opacity\naudit_opacity\n'
    encoded += 'restore_prefix_opacity\naudit_opacity\n'
    # Exercise the public encoder as well as the wider hand-written wrapper
    # domain. Local shadowing distinguishes unqualified from qualified Names.
    body = ('namespace PublicEncoder\n'
            + ''.join(f'def customPrefixRead_{i} (stepWithInputs decide_false decide_true : Nat) := '
                      '(stepWithInputs, decide_false, decide_true)\n' for i in range(12))
            + 'end PublicEncoder\n')
    public_encoded = p.compact_names(body, names_v5=True)
    assert public_encoded.startswith(IMPORT)
    checks = ''.join(f'audit_decl PublicEncoder.customPrefixRead_{i}\n' for i in range(12))
    canonical += body + checks
    encoded += public_encoded.removeprefix(IMPORT) + checks
    plain_log = compile_source(root / 'canonical', 'Probe', canonical)
    compact_log = compile_source(root / 'encoded', 'Probe', encoded)
    assert compact_log == plain_log  # exact declaration names/types/proofs/status/inventory
    assert 'does not depend on any axioms' in compact_log or 'depends on axioms:' in compact_log
    assert 'sorryAx' not in compact_log and 'Lean.trustCompiler' not in compact_log

    # Kill three plausible incorrect implementations with the same real probe.
    bad_name = p.names_v5_source().replace('`Nat.reduceEqDiff', 'Name.mkSimple "Nat.reduceEqDiff"')
    bad_stem = p.names_v5_source().replace('(args.set! 6 (expand stem (args[6]!)))', '(args.map (expand stem))')
    bad_init = p.names_v5_source().replace('stem ++ "InitShapes"', '"hardcodedPrefixInitShapes"')
    for label, broken in [('dotted-simple', bad_name), ('metadata-rewrite', bad_stem),
                          ('hardcoded-stem', bad_init)]:
        assert broken != p.names_v5_source()
        compile_source(root / label, MODULE, broken)
        compile_source(root / label, 'Probe', encoded, ok=False)
    compile_source(root, MODULE, p.names_v5_source())
    for i, header in enumerate(['prefix_names_v6 ordinary where',
                                'prefix_names_v5 ordinary + + + where',
                                'prefix_names_v5 ordinary ! + where']):
        compile_source(root / 'negative', f'Bad{i}', imports + header + '\n def r_0 := 0\n', ok=False)


def test_actual_refused_payload_net_bytes_and_full_roundtrip(tmp_path):
    """Diagnostic replay only, not fresh admission/publication/kernel evidence."""
    import hashlib
    import json
    import os
    import re
    from pathlib import Path
    source_dir = os.environ.get('TRAINVERIFY_NAMES_PAYLOAD')
    if not source_dir:
        pytest.skip('set TRAINVERIFY_NAMES_PAYLOAD to the complete refused payload')
    source_dir = Path(source_dir)
    refusal = json.loads((source_dir / 'refusal.json').read_text())
    names = refusal['files']
    assert len(names) == len(set(names)) == 131
    original = {name: (source_dir / name).read_bytes() for name in names}
    before = sum(map(len, original.values()))
    assert before == refusal['source_bytes'] == 2565116
    support_names = {p.SUPPORT_FILE, p.NAMES_V3_FILE, p.NAMES_V4_FILE, p.NAMES_V5_FILE}
    candidate = {}
    records = []
    for name, raw in original.items():
        if name in support_names:
            continue
        text = raw.decode('utf-8')
        if re.search(r'^prefix_names(?:_v[34])? ', text, re.M):
            canonical = p.expand_names(text)
            legacy = p.compact_names(canonical, names_v3=True, names_v4=True)
            encoded = p.compact_names(canonical, names_v3=True, names_v4=True, names_v5=True)
            if legacy != text:
                # The assembled entry contains notation strings outside its
                # prefix wrapper. Preserve its existing bytes on whole-file
                # unsupported fallback; never strip an existing representation.
                assert legacy == encoded == canonical
                encoded = text
            assert p.expand_names(encoded).encode() == canonical.encode()
        else:
            canonical, encoded = text, text
        candidate[name] = encoded.encode()
        records.append(dict(file=name, before=len(raw), after=len(candidate[name]),
                            before_sha256=hashlib.sha256(raw).hexdigest(),
                            after_sha256=hashlib.sha256(candidate[name]).hexdigest(),
                            canonical_sha256=hashlib.sha256(canonical.encode()).hexdigest(),
                            roundtrip=True))
    for module, source in [(p.SUPPORT_MODULE, p.support_source()),
                           (p.NAMES_V3_MODULE, p.names_v3_source()),
                           (p.NAMES_V4_MODULE, p.names_v4_source()),
                           (MODULE, p.names_v5_source())]:
        if any(f'import {module}\n'.encode() in s for s in candidate.values()):
            candidate[module + '.lean'] = source.encode()
    after = sum(map(len, candidate.values()))
    report = dict(before=before, after=after, net_saved=before-after,
                  strict_limit=2500000, margin=2500000-after,
                  original_count=len(original), candidate_count=len(candidate),
                  v5_files=sum(IMPORT.encode() in s for s in candidate.values()),
                  support_bytes={n:len(s) for n,s in candidate.items() if n in support_names},
                  unchanged_files=[n for n,s in candidate.items() if original.get(n) == s],
                  removed_support=sorted(set(original)-set(candidate)), records=records,
                  diagnostic_only=True, full_kernel_checked=False)
    (tmp_path / 'measurement.json').write_text(json.dumps(report, indent=2))
    replay = tmp_path / 'replay'
    replay.mkdir()
    for name, raw in candidate.items():
        (replay / name).write_bytes(raw)
    assert before-after >= 65117, report
    assert after < 2500000, report
