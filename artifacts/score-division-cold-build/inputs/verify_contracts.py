#!/usr/bin/env python3
"""Verify saved full Expr contracts and kernel3 using only newly built objects."""
import pathlib,json,hashlib,subprocess,sys
B=pathlib.Path(__file__).resolve().parent;sys.path.insert(0,str(B/'public'))
from trainverify.artifact_contracts import dump_contracts,parse_contracts,preserve_old
M=json.loads((B/'contract-manifest.json').read_text());E=json.loads((B/'expected-contracts.json').read_text());S=json.loads((B/'source-manifest.json').read_text())
R=json.loads((B/'build-result.json').read_text());assert R['status']=='compiled' and R['complete_joint_compiled']
T=B/'lean-4.32.2-linux';P=B/'public/trainverify/.lake/packages';paths=[B/'objects']+[p/'.lake/build/lib/lean' for p in sorted(P.iterdir()) if p.is_dir()]+[T/'lib/lean']
source=B/'sources/ColdContracts.lean';source.write_text(dump_contracts(['ScoreDivFrontierJoint'],M))
env={'PATH':str(T/'bin')+':/usr/bin:/bin','HOME':str(B/'home'),'LEAN_PATH':':'.join(map(str,paths)),'LEAN_NUM_THREADS':'1'}
cmd=[str(T/'bin/lean'),'-j1','--tstack=65536','-DmaxHeartbeats=500000','-DmaxRecDepth=4096','-o',str(B/'objects/ColdContracts.olean'),'ColdContracts.lean']
proc=subprocess.run(cmd,cwd=B/'sources',env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,timeout=600)
(B/'contracts.log').write_text(proc.stdout);assert proc.returncode==0,proc.stdout[-5000:]
actual=parse_contracts(proc.stdout,M);assert preserve_old(E['contracts'],actual['contracts'])==154
for name,axs in {**E['axioms'],**E['extra_axioms']}.items():assert set(actual['axioms'][name])==set(axs),(name,actual['axioms'][name],axs)
for r in S['modules']:
 assert hashlib.sha256((B/'sources'/r['relative_path']).read_bytes()).hexdigest()==r['sha256']
(B/'contracts.json').write_text(json.dumps(actual,indent=2)+'\n')
result={'status':'verified','exact_saved_full_Expr_contracts_equal':154,'kernel3_queries':len(actual['axioms']),'division_and_joint_sources':'Byte-identical accepted sources; complete original explicit statements re-elaborated, no old objects loaded','all_candidate_source_hashes_preserved':True,'command':cmd,'exit_code':proc.returncode,'object_sha256':hashlib.sha256((B/'objects/ColdContracts.olean').read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest()}
(B/'contract-verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
