"""Finite, opt-in Nat simproc identifier vocabulary; no proof rewriting."""
import pytest
from Verdict import runtime_prefix as p

MODULE = 'TrainVerifyRuntimePrefixNamesV4'
IMPORT = f'import {MODULE}\n'
HELPER = 'AllToAllSourceFaithful.localStep'
SIMPROC = 'Nat.reduceEqDiff'


def sample(simproc=SIMPROC, helper=HELPER):
    return ('import TrainVerifyRuntimePrefixSupport\n\n' + p._HEADER
            + ''.join(f'def tinyPrefixStep_{i} (init : Store) :=\n'
                      f'  {helper} tinyPrefixState_0 init\n'
                      f'theorem tinyPrefixRead_{i} : (1 : Nat) ≠ 2 := by\n'
                      f'  simp only [{simproc}]\n'
                      f'#print axioms tinyPrefixRead_{i}\n' for i in range(12))
            + p._FOOTER)


def test_opt_in_finite_codec_roundtrip():
    source = sample()
    old = p.compact_names(source)
    encoded = p.compact_names(source, names_v4=True)
    assert 'prefix_names_v4 tinyPrefix ! where\n' in encoded
    assert encoded.count(IMPORT) == 1
    assert p._NAMES_V3_IMPORT not in encoded
    assert encoded.count('simp only [pE]') == 12
    assert encoded.count('pL s_0 z') == 12
    assert len(encoded.encode()) < len(old.encode())
    assert p.expand_names(encoded) == source
    assert p.compact_names(encoded, names_v4=True) == encoded
    assert p.expand_names(encoded + '#print axioms Outside.fact\n') == source + '#print axioms Outside.fact\n'
    assert p.compact_names(source, names_v3=False, names_v4=True) == encoded


@pytest.mark.parametrize('where', ['single', 'final_only', 'chunk', 'final', 'both', 'neither', 'mixed'])
def test_pack_support_exact_and_on_demand(where):
    from pathlib import Path
    body = sample().split(p._HEADER, 1)[1].split(p._FOOTER)[0]
    legacy = body.replace(SIMPROC, 'ordinarySimproc')
    if where in ('single', 'final_only'):
        groups = [p.ProofGroup(body, 1, (), final=where == 'final_only')]
    else:
        groups = [p.ProofGroup(body if where in ('chunk', 'both', 'mixed') else legacy, 50, ()),
                  p.ProofGroup(legacy, 50, ()),
                  p.ProofGroup(body if where in ('final', 'both') else legacy, 1, (), final=True)]
    entry, supporting = p.pack_proofs([groups], names_v3=where == 'mixed', names_v4=True)
    assert (MODULE + '.lean' in supporting) == (where != 'neither')
    assert (p.NAMES_V3_FILE in supporting) == (where == 'mixed')
    assert supporting[p.SUPPORT_FILE] == p.support_source()
    if where != 'neither':
        assert p.NAMES_V4_MODULE == MODULE
        assert p.NAMES_V4_FILE == MODULE + '.lean'
        assert supporting[p.NAMES_V4_FILE] == p.names_v4_source()
        assert p.names_v4_source() == Path(p.__file__).with_name('runtime_prefix_names_v4.lean').read_text()
    assert (IMPORT in entry) == (where in ('single', 'final_only', 'final', 'both'))
    default_entry, default_support = p.pack_proofs([groups])
    assert MODULE + '.lean' not in default_support
    assert p.NAMES_V3_FILE not in default_support
    assert p.expand_names(entry) == p.expand_names(default_entry)
    support_files = {p.SUPPORT_FILE, p.NAMES_V3_FILE, MODULE + '.lean'}
    sources = {n: s for n, s in supporting.items() if n not in support_files}
    assert list(sources) == [n for n in default_support if n not in support_files]
    for name, source in sources.items():
        assert p.expand_names(source) == p.expand_names(default_support[name])
        assert (IMPORT in source) == (SIMPROC in p.expand_names(source))


@pytest.mark.parametrize('extra', [
    'def pE := 1\n', '#check pE\n', 'example (pE : Nat) := pE\n', 'def pL := 1\n',
    'def pR := 1\n', 'def pS := 1\n', 'def pF := 1\n', 'def z := 1\n', 'def z_ := 1\n',
    'def literal := "Nat.reduceEqDiff"\n', '#check «Nat.reduceEqDiff»\n',
    '#check `Nat.reduceEqDiff\n', '/- Nat.reduceEqDiff -/\n',
    IMPORT, 'import TrainVerifyRuntimePrefixNamesV4 Other\n',
    '#print  axioms tinyPrefixRead_0\n',
])
def test_collision_or_unsupported_returns_original(extra):
    source = sample() + extra
    assert p.compact_names(source, names_v4=True) == source


@pytest.mark.parametrize('token', [
    'Other.Nat.reduceEqDiff', SIMPROC + '.more', SIMPROC + "'", SIMPROC + '?',
    SIMPROC + '!', SIMPROC + '_more', 'α' + SIMPROC,
    'Other.pE', 'pE.more', "pE'", 'pE?', 'pE!', 'pE_more',
])
def test_only_exact_tokens_change(token):
    extra = f'#check {token}\n-- {SIMPROC} pE tinyPrefixRead_99\n'
    source = sample() + extra
    encoded = p.compact_names(source, names_v4=True)
    assert 'prefix_names_v4 ' in encoded
    assert all(line in encoded for line in extra.splitlines())
    assert p.expand_names(encoded) == source


@pytest.mark.parametrize('names_v3', [False, True])
def test_no_target_or_unprofitable_keeps_existing_codec(names_v3):
    for source in (sample('ordinarySimproc'),
                   sample('ordinarySimproc') + f'-- {SIMPROC}\n',
                   'import Nat.reduceEqDiff\n' + sample('ordinarySimproc'),
                   'def tinyPrefixRead_0 : Nat := 0\n',
                   '#check Nat.reduceEqDiff\n',
                   ''.join(f'def tinyPrefixRead_{i} := 0\n' for i in range(12))
                   + 'example : (1 : Nat) ≠ 2 := by simp only [Nat.reduceEqDiff]\n'):
        assert p.compact_names(source, names_v3=names_v3, names_v4=True) == p.compact_names(source, names_v3=names_v3)


@pytest.mark.parametrize('stem', ['ordinary', 'pL', 'pE'])
@pytest.mark.parametrize('plus', ['', ' +', ' + +'])
@pytest.mark.parametrize('query', ['', ' !'])
@pytest.mark.parametrize('indent', [' ', '  '])
def test_old_domains_flags_metadata_and_mixed_suffix(stem, plus, query, indent):
    body = 'def r_0 (pE pL pR pS pF : Nat) := pE\n'
    query_body = ('#a' if query else '#print axioms') + ' r_0\n'
    block = ''.join(indent + line for line in (body + query_body).splitlines(keepends=True))
    expected = body.replace('r_0', stem + 'Read_0') + '#print axioms ' + stem + 'Read_0\n'
    if plus:
        expected = expected.replace('pR', 'prefixRead')
    if plus == ' + +':
        expected = expected.replace('pS', 'storeSet_eq_of_not_mem_fst').replace('pF', 'prefixFrame_trans')
    old = f'prefix_names {stem}{plus}{query} where\n' + block
    v3 = p._NAMES_V3_IMPORT + old.replace('prefix_names ', 'prefix_names_v3 ', 1)
    v4 = IMPORT + old.replace('prefix_names ', 'prefix_names_v4 ', 1)
    # Replace body identifiers only; a stem matching an alias remains metadata.
    expected3 = expected.replace('(pE pL ', '(pE ' + HELPER + ' ')
    expected4 = expected3.replace('(pE ', '(' + SIMPROC + ' ').replace(':= pE', ':= ' + SIMPROC)
    assert p.expand_names(old) == expected
    assert p.expand_names(v3) == expected3
    assert p.expand_names(v4) == expected4
    assert p.expand_names(v4 + v3 + old) == expected4 + expected3 + expected


@pytest.mark.parametrize('preamble', ['', IMPORT + IMPORT, IMPORT + '\n',
                                      p._NAMES_V3_IMPORT, 'import Other\n',
                                      'import TrainVerifyRuntimePrefixNamesV4 Other\n'])
def test_import_ownership_rejects_missing_duplicate_or_nonowned(preamble):
    with pytest.raises(ValueError, match='import'):
        p.expand_names(preamble + 'prefix_names_v4 ordinary where\n def r_0 := pE\n')


@pytest.mark.parametrize('header', ['prefix_names_v5 ordinary where',
                                   'prefix_names_v4 ordinary + + + where',
                                   'prefix_names_v4 ordinary ! + where',
                                   'prefix_names_v4 ordinary !! where'])
def test_invalid_header_even_before_valid_suffix(header):
    source = IMPORT + header + '\n def r_0 := 0\n'
    with pytest.raises(ValueError, match='header'):
        p.expand_names(source + 'prefix_names ordinary where\n def r_1 := 1\n')


def test_new_support_name_does_not_change_legacy_opt_out():
    source = sample() + f'def {MODULE} := 0\n'
    legacy = p.compact_names(sample()) + f' def {MODULE} := 0\n'
    assert p.compact_names(source) == legacy
    assert p.compact_names(source, names_v4=True) == source


def test_real_lean_identity_and_bad_expander_controls(tmp_path):
    """Opt-in isolated kernel probe: set TRAINVERIFY_NAMES_LEAN and LEAN_PATH.

    LEAN_PATH must contain built denote.Denote / AllToAllSourceFaithful and their
    dependencies. No lake build, capture, installation or shared object writes.
    Source copies use their actual module names, never runtime_prefix_names_v4.
    """
    import os
    import subprocess
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
        assert (result.returncode == 0) == ok, result.stdout[:5000]
        if ok:
            assert 'sorry' not in result.stdout
        return result.stdout

    for module, source in ((p.SUPPORT_MODULE, p.support_source()),
                           (p.NAMES_V3_MODULE, p.names_v3_source()),
                           (MODULE, p.names_v4_source())):
        compile_source(root, module, source)

    imports = ('import TrainVerifyRuntimePrefixNamesV3\n' + IMPORT
               + 'import denote.AllToAllSourceFaithful\n'
               + 'open Lean Elab Command TrainVerify.Denote\n')
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
    configurations = list(product(['ordinary', 'pL', 'pE'], ['', ' +', ' + +'], ['', ' !'], [' ', '  ']))
    for i, (stem, plus, query, indent) in enumerate(configurations):
        prefix = f'namespace Case{i}\nnoncomputable section\n'
        # Aliases occur only in Syntax.ident; strings and comments must survive.
        body = (f'def {stem}State_0 : Nat := 7\n'
                f'attribute [local irreducible] {stem}State_0\n'
                f'record_prefix_opacity {stem}State_0\n'
                f'def {stem}Step_0 := @{HELPER}\n'
                f'theorem {stem}Read_0 : ((1 : Nat) = 2) = False := by\n'
                f'  simp only [{SIMPROC}]\n'
                f'#print axioms {stem}Read_0\n'
                'def literal : String := "pE pL"\n-- pE pL stay comments\n')
        compressed = (body.replace(stem + 'State_0', 's_0')
                      .replace(stem + 'Step_0', 't_0').replace(stem + 'Read_0', 'r_0')
                      .replace(HELPER, 'pL').replace(SIMPROC, 'pE'))
        if query:
            compressed = compressed.replace('#print axioms ', '#a ')
        checks = (f'audit_decl {stem}State_0\naudit_decl {stem}Step_0\n'
                  f'audit_decl {stem}Read_0\naudit_decl literal\nend\nend Case{i}\n')
        canonical += prefix + body + checks
        encoded += prefix + f'prefix_names_v4 {stem}{plus}{query} where\n' + ''.join(
            indent + line for line in compressed.splitlines(keepends=True)) + checks
    # Old wrappers retain literal pE, including when pE is the stem metadata.
    for i, wrapper in enumerate(['prefix_names', 'prefix_names_v3']):
        body = 'def pERead_0 (pE : Nat) := pE\n'
        prefix = f'namespace Legacy{i}\n'
        checks = 'audit_decl pERead_0\nend Legacy' + str(i) + '\n'
        canonical += prefix + body + checks
        encoded += prefix + wrapper + ' pE where\n def r_0 (pE : Nat) := pE\n' + checks
    canonical += 'restore_prefix_opacity\naudit_opacity\n'
    encoded += 'restore_prefix_opacity\naudit_opacity\n'
    plain_log = compile_source(root / 'canonical', 'Probe', canonical)
    compact_log = compile_source(root / 'encoded', 'Probe', encoded)
    assert compact_log == plain_log  # exact declaration names/types/proofs/status/inventory
    assert 'does not depend on any axioms' in compact_log or 'depends on axioms:' in compact_log
    assert 'sorryAx' not in compact_log and 'Lean.trustCompiler' not in compact_log

    # Kill two plausible unsound implementations with the same real probe.
    bad_name = p.names_v4_source().replace('`Nat.reduceEqDiff', 'Name.mkSimple "Nat.reduceEqDiff"')
    bad_stem = p.names_v4_source().replace('(args.set! 6 (expand (args[6]!)))', '(args.map expand)')
    for label, broken in [('dotted-simple', bad_name), ('metadata-rewrite', bad_stem)]:
        compile_source(root / label, MODULE, broken)
        compile_source(root / label, 'Probe', encoded, ok=False)
    compile_source(root, MODULE, p.names_v4_source())
    for i, header in enumerate(['prefix_names_v5 ordinary where',
                                'prefix_names_v4 ordinary + + + where',
                                'prefix_names_v4 ordinary ! + where']):
        compile_source(root / 'negative', f'Bad{i}', imports + header + '\n def r_0 := 0\n', ok=False)
