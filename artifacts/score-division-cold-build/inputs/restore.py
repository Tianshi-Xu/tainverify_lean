#!/usr/bin/env python3
"""Portable source-first restore: public Git pins + minimal source bundle only."""
import pathlib,json,subprocess,hashlib,tarfile,argparse,os
B=pathlib.Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--source-output',default='sources');p.add_argument('--skip-provision',action='store_true');p.add_argument('--build',action='store_true');a=p.parse_args()
M=json.loads((B/'source-manifest.json').read_text());P=B/'public';T=B/'lean-4.32.2-linux';out=(B/a.source_output).resolve();assert out.is_relative_to(B)
def run(cmd,**kwargs):subprocess.run(list(map(str,cmd)),check=True,**kwargs)
def sha(data):return hashlib.sha256(data).hexdigest()
if not P.exists():
 run(['git','init',P]);run(['git','-C',P,'remote','add','origin',M['remote']]);run(['git','-C',P,'fetch','--depth=1','origin',M['commit']]);run(['git','-C',P,'checkout','--detach',M['commit']])
assert subprocess.check_output(['git','-C',P,'rev-parse','HEAD'],text=True).strip()==M['commit']
for c in sorted({r['git_commit'] for r in M['modules'] if 'git_commit' in r}):
 if subprocess.run(['git','-C',P,'cat-file','-e',c],stderr=subprocess.DEVNULL).returncode:run(['git','-C',P,'fetch','--depth=1','origin',c])
archive=B/'minimal-missing-sources.tar.gz'
with tarfile.open(archive,'r:gz') as tar:
 allowed={r['relative_path'] for r in M['modules'] if r['remote_kind']=='missing_from_reachable_git'}
 assert set(tar.getnames())==allowed
 for r in M['modules']:
  rel=r['relative_path'];target=out/rel;assert target.resolve().is_relative_to(out)
  if r['remote_kind']=='missing_from_reachable_git':
   mem=tar.getmember(rel);assert mem.isfile();data=tar.extractfile(mem).read()
  else:data=subprocess.check_output(['git','-C',P,'show',r['git_commit']+':'+r['git_path']])
  assert sha(data)==r['sha256'],r['module']
  target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
(B/'source-restoration.json').write_text(json.dumps({'status':'verified','module_count':len(M['modules']),'source_output':str(out),'public_remote':M['remote'],'pinned_commit':M['commit'],'manifest_sha256':sha((B/'source-manifest.json').read_bytes()),'missing_bundle_sha256':sha(archive.read_bytes()),'historical_local_source_paths_opened':False,'objects_restored':False},indent=2)+'\n')
print('Restored',len(M['modules']),'verified sources into',out,flush=True)
if not a.skip_provision:
 provenance=json.loads((B/'official-provenance.json').read_text());pin=provenance['toolchain'];archive=B/'downloads/lean-4.32.2-linux.tar.zst';archive.parent.mkdir(exist_ok=True)
 if not archive.exists():run(['curl','-fL','--retry','3','-o',archive,pin['url']])
 with archive.open('rb') as f:assert hashlib.file_digest(f,'sha256').hexdigest()==pin['archive_sha256']
 if not T.exists():run(['tar','--zstd','-xf',archive,'-C',B])
 env={'PATH':str(T/'bin')+':/usr/bin:/bin','HOME':str(B/'home'),'LEAN_NUM_THREADS':'4'}
 (B/'home').mkdir(exist_ok=True)
 with (B/'packages-setup.log').open('w') as log:run([T/'bin/lake','exe','cache','get'],cwd=P/'trainverify',env=env,stdout=log,stderr=subprocess.STDOUT)
 print('Official dependencies provisioned',flush=True)
if a.build:
 assert out==B/'sources','build.py consumes sources/'
 run(['python3',B/'build.py','--jobs','4','--module-timeout','1800'])
 run(['python3',B/'verify_contracts.py'])
 run(['python3',B/'audit_axiom_logs.py'])
