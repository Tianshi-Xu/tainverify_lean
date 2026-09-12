import hashlib, json, os, re, subprocess, sys, time
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
A = ROOT / '.hermes/backward-kernel'
OLD = Path('/home/v-zhouziyu/trainverify-audits/general-parallel-internal1/dp-prefix-cost-closure')
PIN = json.loads((OLD/'initial-relations/SourceValueRead-kernel.json').read_text())
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
for name, h in PIN['sources'].items():
    relative = name.split('/trainverify/', 1)[1]
    assert sha(ROOT/'trainverify'/relative) == h, name
for name, h in PIN['dependencies'].items():
    assert sha(name) == h, name
assert sha(ROOT/'trainverify/denote/SourceValueRead.lean') == PIN['source_sha256']
assert sha(OLD/'initial-relations/objects/denote/SourceValueRead.olean') == PIN['object_sha256']
# Lean resolves a namespace from its first root, not per-file fallback. Populate
# the isolated overlay with only the receipt-verified read-only dependencies.
for name in [*PIN['dependencies'], str(OLD/'initial-relations/objects/denote/SourceValueRead.olean')]:
    source = Path(name)
    target = A/'objects'/source.relative_to(OLD/'initial-relations/objects')
    target.parent.mkdir(parents=True, exist_ok=True)
    if not target.exists():
        target.symlink_to(source)
lean = '/home/v-zhouziyu/.elan/toolchains/leanprover--lean4---v4.32.2/bin/lean'
assert (ROOT/'trainverify/lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.32.2'
assert '4.32.2' in subprocess.check_output([lean, '--version'], text=True)
paths = [str(A/'objects'), str(OLD/'initial-relations/objects')]
paths += [p for p in json.loads((OLD/'dependency-pins.json').read_text())['LEAN_PATH'].split(':') if '/.lake/packages/' in p or p.endswith('/lib/lean')]
# Independent modules may compile concurrently; callers order dependencies and
# give each source a distinct output. Resource availability, not other jobs'
# process names, determines admission.
available_kib = int(next(line.split()[1] for line in Path('/proc/meminfo').read_text().splitlines()
                         if line.startswith('MemAvailable:')))
assert available_kib >= 32 * 1024 * 1024, 'kernel admission: less than 32 GiB memory available'
src = Path(sys.argv[1]); name = src.stem
if 'import TrainVerifyRuntimeWorldData' in src.read_text():
    root=OLD/'output-projection'
    entry=json.loads((root/'actual-output-projection1-entry-kernel.json').read_text())
    assert entry['inner_exit']==0
    data=root/'actual-output-projection1/TrainVerifyRuntimeWorldData.lean'
    data_object=root/'final-objects/TrainVerifyRuntimeWorldData.olean'
    assert sha(data)==json.loads((OLD/'dependency-pins.json').read_text())['source_sha256']
    assert sha(data_object)==entry['dependencies'][str(data_object)]
    target=A/'objects/TrainVerifyRuntimeWorldData.olean'
    if not target.exists(): target.symlink_to(data_object)
    assert sha(target)==sha(data_object)
    prefix_imports=re.findall(r'^import TrainVerifyRuntimePrefix(\d+)\s*$',src.read_text(),re.M)
    if prefix_imports:
        maximum=max(map(int,prefix_imports))
        modules=json.loads((root/'actual-output-projection1/world-receipt.json').read_text())['proof_bundle']['modules']
        for module in ['TrainVerifyRuntimePrefixSupport',*(f'TrainVerifyRuntimePrefix{i:04d}' for i in range(maximum+1))]:
            info=next(m for m in modules if m['module']==module)
            assert sha(root/'actual-output-projection1'/info['file'])==info['source_sha256']
            obj=root/'final-objects'/(module+'.olean')
            check=next(r for r in json.loads((OLD/'post-transpose/actual-post-transpose1-kernel.json').read_text()) if r['key']==module)
            assert check['inner_exit']==0 and check['source_sha256']==info['source_sha256']
            assert sha(obj)==check['object_sha256']
            for path,h in check['dependency_objects'].items(): assert sha(path)==h,path
            dst=A/'objects'/(module+'.olean')
            if not dst.exists(): dst.symlink_to(obj)
            assert sha(dst)==sha(obj)
for module in ('SourceParameterFrame','SourcePrimitiveRead'):
    if ('import denote.'+module) not in src.read_text(): continue
    frame=json.loads((OLD/('initial-relations/'+module+'-kernel.json')).read_text())
    assert frame['inner_exit']==0
    for path,h in frame['sources'].items():
        assert sha(ROOT/'trainverify'/path.split('/trainverify/',1)[1])==h,path
    assert sha(ROOT/('trainverify/denote/'+module+'.lean'))==frame['source_sha256']
    for path,h in {**frame['dependencies'],str(OLD/('initial-relations/objects/denote/'+module+'.olean')):frame['object_sha256']}.items():
        assert sha(path)==h,path
        source=Path(path);target=A/'objects'/source.relative_to(OLD/'initial-relations/objects')
        target.parent.mkdir(parents=True,exist_ok=True)
        if not target.exists(): target.symlink_to(source)
        assert sha(target)==h
for module in ('ActualBWLinearRead','ActualBWSeedRead'):
    if ('import '+module) not in src.read_text(): continue
    receipt=json.loads((A/(module+'-kernel.json')).read_text())
    assert receipt['inner_exit']==0
    assert sha(receipt['source'])==receipt['source_sha256']
    assert sha(receipt['object'])==receipt['object_sha256']
out = A/'objects'/('denote' if src.parent.name == 'denote' else '')/(name+'.olean')
out.parent.mkdir(parents=True, exist_ok=True)
start=time.time()
cmd=[lean,'-j1','--tstack=65536','-DmaxHeartbeats=500000','-DmaxRecDepth=4096','-o',str(out),str(src)]
with (A/(name+'.log')).open('w') as f:
    p=subprocess.run(cmd,cwd=ROOT,env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1'),stdout=f,stderr=subprocess.STDOUT,timeout=600)
text=(A/(name+'.log')).read_text()
ax={n:[x.strip() for x in v.split(',') if x.strip()] for n,v in re.findall(r"'([^']+)' depends on axioms: \[([\s\S]*?)\]",text)}
ax.update({n:[] for n in re.findall(r"'([^']+)' does not depend on any axioms",text)})
if p.returncode==0:
    namespace=re.search(r'^namespace (\S+)',src.read_text(),re.M)
    expected={n if '.' in n else namespace[1]+'.'+n
              for n in re.findall(r'^#print axioms (\S+)',src.read_text(),re.M)}
    assert set(ax)==expected,(set(ax),expected)
    assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in ax.values()),ax
record=dict(source=str(src), source_sha256=sha(src), inner_exit=p.returncode, seconds=time.time()-start, command=cmd, object=str(out), object_sha256=sha(out) if p.returncode==0 else None, axioms=ax, dependency_receipt=str(OLD/'initial-relations/SourceValueRead-kernel.json'))
(A/(name+'-kernel.json')).write_text(json.dumps(record,indent=2))
print(json.dumps(record,indent=2)); print(text)
sys.exit(p.returncode)
