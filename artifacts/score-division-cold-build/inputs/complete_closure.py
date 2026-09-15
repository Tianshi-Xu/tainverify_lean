#!/usr/bin/env python3
"""Ask pinned Lean's actual header parser for the complete transitive closure."""
import pathlib,subprocess,json,hashlib,concurrent.futures
B=pathlib.Path(__file__).resolve().parent;T=B/'lean-4.32.2-linux';P=B/'public/trainverify/.lake/packages';lean=T/'bin/lean'
M=json.loads((B/'source-manifest.json').read_text());pkgs=json.loads((B/'public/trainverify/lake-manifest.json').read_text())['packages']
roots=[(B/'sources',B/'objects','task')]+[(P/p['name'],P/p['name']/'.lake/build/lib/lean',p['name']) for p in pkgs]+[(T/'src/lean',T/'lib/lean','lean4')]
env={'PATH':str(T/'bin')+':/usr/bin:/bin','HOME':str(B/'home'),'LEAN_SRC_PATH':':'.join(str(r[0]) for r in roots[:-1]),'LEAN_NUM_THREADS':'1'}
known={};pending=['ScoreDivFrontierJoint'];refs=[]
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def resolve(m):
 rel=m.replace('.','/')+'.lean'
 for root,obj,pkg in roots:
  if (root/rel).is_file():return root/rel,obj/rel.replace('.lean','.olean'),pkg
 raise RuntimeError('No source '+m)
def read(m):
 src,obj,pkg=resolve(m);p=subprocess.run([str(lean),'--src-deps',str(src)],env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,timeout=30)
 assert p.returncode==0,(m,p.stdout,p.stderr)
 deps=[]
 for line in p.stdout.splitlines():
  f=pathlib.Path(line).resolve();name=None
  for root,ob,pk in roots:
   for base in [root,ob]:
    if f.is_relative_to(base.resolve()):name='.'.join(f.relative_to(base.resolve()).with_suffix('').parts);break
   if name:break
  assert name,(m,line)
  if name not in deps:deps.append(name)
 return {'module':m,'source':str(src.relative_to(B)),'source_sha256':sha(src),'package':pkg,'imports':deps,'object':str(obj.relative_to(B)),'object_sha256':sha(obj) if obj.is_file() else None}
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:
 while pending:
  batch=list(dict.fromkeys(x for x in pending if x not in known));pending=[]
  for r in ex.map(read,batch):known[r['module']]=r;pending.extend(x for x in r['imports'] if x not in known)
  print('discovered',len(known),'pending',len(pending),flush=True)
  (B/'complete-import-closure.json').write_text(json.dumps({'root':'ScoreDivFrontierJoint','modules':list(known.values()),'count':len(known),'complete':not pending},indent=2)+'\n')
local={m for m,r in known.items() if r['package']=='task'};expected={r['module'] for r in M['modules']};assert local==expected,(local-expected,expected-local)
for r in M['modules']:
 assert set(r['imports']) - {'Init'} == set(known[r['module']]['imports']) - {'Init'},r['module']
print('complete',len(known),'task',len(local))
