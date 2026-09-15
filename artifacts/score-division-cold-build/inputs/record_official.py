#!/usr/bin/env python3
import pathlib,json,subprocess,hashlib,re,os
B=pathlib.Path(__file__).resolve().parent; T=B/'lean-4.32.2-linux'; P=B/'public/trainverify/.lake/packages'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
lock=json.loads((B/'public/trainverify/lake-manifest.json').read_text());packages=[]
for p in lock['packages']:
 root=P/p['name'];rev=subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD'],text=True).strip();assert rev==p['rev']
 packages.append(dict(name=p['name'],url=p['url'],rev=rev,build_root=str(root/'.lake/build'),provision='Fresh public Git clone via pinned Lake manifest; official mathlib cache download, isolated HOME'))
records=[]
for root in [T]+[P/p['name']/'.lake/build' for p in lock['packages']]:
 for f in sorted(root.rglob('*')):
  if not f.is_file():continue
  # Include the complete build tree, including cache executable and .o.export.
  records.append({'path':str(f.relative_to(B)),'sha256':sha(f),'bytes':f.stat().st_size,'symlink':f.is_symlink(),'symlink_target':os.readlink(f) if f.is_symlink() else None})
(B/'official-files.json').write_text(json.dumps(records,indent=2)+'\n')
r={'toolchain':{'url':'https://github.com/leanprover/lean4/releases/download/v4.32.2/lean-4.32.2-linux.tar.zst','archive_sha256':sha(B/'downloads/lean-4.32.2-linux.tar.zst'),'version':subprocess.check_output([str(T/'bin/lean'),'--version'],text=True).strip(),'provision':'Fresh official release archive; no installed elan tree used'},'packages':packages,'lock_sha256':sha(B/'public/trainverify/lake-manifest.json'),'cache_log_sha256':sha(B/'packages-setup.log'),'official_file_manifest_sha256':sha(B/'official-files.json'),'official_file_count':len(records),'native_linkage':subprocess.check_output(['ldd',str(T/'bin/lean')],text=True)}
(B/'official-provenance.json').write_text(json.dumps(r,indent=2)+'\n');print('official files',len(records))
