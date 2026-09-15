#!/usr/bin/env python3
"""Direct-Lean sealed import-DAG build; no Lake project targets or old objects."""
import pathlib,json,os,subprocess,time,hashlib,concurrent.futures,argparse,resource
B=pathlib.Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--jobs',type=int,default=4);p.add_argument('--module-timeout',type=int,default=1800);args=p.parse_args();assert 1<=args.jobs<=4
D=json.loads((B/'source-manifest.json').read_text()) if (B/'source-manifest.json').exists() else {'modules':list(json.loads((B/'discovery.json').read_text())['modules'].values())}
rows={r['module']:r for r in D['modules']}; src=B/'sources'; obj=B/'objects'; logs=B/'logs';obj.mkdir(exist_ok=True);logs.mkdir(exist_ok=True)
lean=B/'lean-4.32.2-linux/bin/lean'; pkgs=B/'public/trainverify/.lake/packages'; paths=[obj]+[p/'.lake/build/lib/lean' for p in sorted(pkgs.iterdir()) if p.is_dir()]+[B/'lean-4.32.2-linux/lib/lean']
env={'HOME':str(B/'home'),'PATH':str(lean.parent)+':/usr/bin:/bin','LEAN_PATH':':'.join(map(str,paths)),'LEAN_NUM_THREADS':'1'}
assert all(str(p.resolve()).startswith(str(B)+'/') for p in paths)
def sha(p):return hashlib.file_digest(open(p,'rb'),'sha256').hexdigest()
for r in rows.values():assert sha(src/r['relative_path'])==r['sha256']
receipt=B/'build-receipts.jsonl'; done={}; failures=[]; running={};started=time.time()
if receipt.exists():
 for line in receipt.read_text().splitlines():
  r=json.loads(line)
  if r['exit_code']==0 and sha(obj/(r['module'].replace('.','/')+'.olean'))==r['object_sha256'] and r['source_sha256']==rows[r['module']]['sha256']:done[r['module']]=r
# Resumption is private-run-only and revalidates all recorded dependencies.
for m,r in done.items():
 for f,h in r['dependencies'].items():assert sha(pathlib.Path(f))==h

def build(m):
 row=rows[m]; rel=row['relative_path']; out=obj/rel.replace('.lean','.olean');out.parent.mkdir(parents=True,exist_ok=True)
 dep={}
 for name in row['imports']:
  f=next((base/(name.replace('.','/')+'.olean') for base in paths if (base/(name.replace('.','/')+'.olean')).is_file()),None)
  if f is None:raise RuntimeError('missing import '+name)
  dep[str(f)]=sha(f)
 cmd=[str(lean),'-j1','--tstack=65536','-DmaxHeartbeats=500000','-DmaxRecDepth=4096','-o',str(out),rel]
 log=logs/(m+'.log'); timing=logs/(m+'.time');t=time.time()
 with log.open('w') as stream:
  proc=subprocess.Popen(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=src,env=env,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
  try:code=proc.wait(timeout=args.module_timeout)
  except subprocess.TimeoutExpired:
   import signal
   os.killpg(proc.pid,signal.SIGKILL);proc.wait();code=124
 result={'module':m,'source_sha256':row['sha256'],'dependencies':dep,'command':cmd,'lean_path':list(map(str,paths)),'exit_code':code,'seconds':time.time()-t,'log':str(log),'timing':str(timing),'object_sha256':sha(out) if code==0 and out.exists() else None,'newly_compiled':True}
 return result
with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
 while len(done)<len(rows):
  ready=[m for m,r in rows.items() if m not in done and m not in running and all(x in done for x in r['imports'] if x in rows)]
  if not failures:
   for m in ready[:args.jobs-len(running)]:running[m]=ex.submit(build,m);print('START',m,flush=True)
  if not running:break
  finished,_=concurrent.futures.wait(list(running.values()),timeout=20,return_when=concurrent.futures.FIRST_COMPLETED)
  for m,f in list(running.items()):
   if f not in finished:continue
   r=f.result();del running[m]
   with receipt.open('a') as stream:stream.write(json.dumps(r)+'\n');stream.flush();os.fsync(stream.fileno())
   print('DONE' if r['exit_code']==0 else 'FAIL',m,r['exit_code'],round(r['seconds'],2),flush=True)
   if r['exit_code']==0:done[m]=r
   else:failures.append(r)
  (B/'build-progress.json').write_text(json.dumps({'completed':sorted(done),'running':list(running),'failed':failures,'elapsed_seconds':time.time()-started,'total':len(rows)},indent=2)+'\n')
result={'status':'compiled' if len(done)==len(rows) and not failures else 'blocked','complete_joint_compiled':'ScoreDivFrontierJoint' in done,'completed_modules':sorted(done),'failed_modules':failures,'expected_modules':len(rows),'elapsed_seconds':time.time()-started,'old_task_objects_used':False,'old_shared_package_cache_used':False}
(B/'build-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result));raise SystemExit(0 if result['status']=='compiled' else 1)
