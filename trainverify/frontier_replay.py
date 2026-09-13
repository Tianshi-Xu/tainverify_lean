"""Replay a configured frontier from trusted saved captures, never recapture.

Uses the original common-context attachment boundary, records selected genuine
predecessors once with the identical six objects, and stops before canonical
world/publication writes. Recipe paths and source commits are explicit inputs.
"""
import argparse
from contextlib import ExitStack
import importlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time
from unittest.mock import patch

from trainverify.artifact_tools import Configuration,absolute,digest_value,emit,keys,lean_name,require,sha256

_FLAGS=('proof_admissible','kernel_value_proved','public_complete','torch_refinement')


def _spec(row,ancestor=False):
    keys(row,('module','name','imports','detail') if ancestor else ('module','name','imports'),'frontier recipe record')
    require(type(row['module']) is str and re.fullmatch(r'Verdict\.runtime_[A-Za-z0-9_]+',row['module']) is not None,'invalid renderer module')
    lean_name(row['name']); require('.' not in row['name'],'flat fragment module name required')
    require(type(row['imports']) is list and bool(row['imports']),'fragment imports required')
    for name in row['imports']: lean_name(name)
    require(len(set(row['imports']))==len(row['imports']),'duplicate fragment import')
    if ancestor:
        require(type(row['detail']) is str and re.fullmatch('[A-Za-z0-9_-]+',row['detail']) is not None,'invalid detail filename')


def render_context(module,records,final,out,sm,pm,lineages,validation,bound,order):
    require(type(records) is list,'predecessor records required')
    for row in records: _spec(row,True)
    _spec(final)
    require(module.__name__==final['module'],'target renderer identity mismatch')
    names=[r['name'] for r in records]+[final['name']]
    require(len(names)==len(set(names)),'duplicate fragment module')
    require(len({r['detail'] for r in records})==len(records),'duplicate detail filename')
    chain=[]; subject=module; seen={id(module)}
    for row in reversed(records):
        subject=subject.predecessor
        require(id(subject) not in seen and subject.__name__==row['module'],'predecessor module order/identity mismatch')
        chain.append((subject,row)); seen.add(id(subject))
    for previous,row in zip(records,records[1:]+[final]):
        require(row['imports'][0]==previous['name'],'predecessor fragment import mismatch')
    six=(sm,pm,lineages,validation,bound,order); counts={}; saved={}
    def recorder(subject,row):
        original=subject.render
        def call(*args,**kwargs):
            require(len(args)==6 and not kwargs and all(x is y for x,y in zip(args,six,strict=True)),
                'predecessor did not receive the identical six original objects')
            name=row['name']; counts[name]=counts.get(name,0)+1
            require(counts[name]==1,'duplicate public predecessor call')
            text,detail=original(*args)
            saved[name]=(text,detail)
            return text,detail
        return call
    with ExitStack() as stack:
        for subject,row in chain:
            stack.enter_context(patch.object(subject,'render',recorder(subject,row)))
        text,detail=module.render(*six)
    require(counts=={r['name']:1 for r in records},'predecessor public call cover mismatch')
    require(all(detail.get(flag) is False for flag in _FLAGS),'renderer status must remain false/uncompiled')
    saved[final['name']]=(text,detail)
    # Validate and serialize all outputs before any emission; never overwrite.
    pending={}
    for row in records+[final]:
        body,info=saved[row['name']]
        require(type(body) is str,'renderer source must be text')
        pending[row['name']+'.lean']=''.join('import '+i+'\n' for i in row['imports'])+body
        label=row['detail']+'-detail.json' if row is not final else 'detail.json'
        pending[label]=json.dumps(info,indent=2,allow_nan=False)
    out=Path(out)
    require(out.is_dir() and not any((out/name).exists() or (out/name).is_symlink() for name in pending),'output collision')
    for name,body in pending.items():
        with (out/name).open('x') as stream: stream.write(body)
    return dict(detail=detail,predecessor_public_calls=counts)


def _git(root,*args):
    run=subprocess.run(['git','-C',str(root),*args],capture_output=True,text=True)
    require(run.returncode==0,'Git source check failed: '+run.stderr)
    return run.stdout.strip()


def replay(config,recipe,root,out,commit):
    keys(recipe,('version','target','ancestors','pins','seed_bundle','batch_authority','rank_code_directory'),'replay recipe')
    require(type(recipe['version']) is int and recipe['version']==1,'unsupported replay recipe')
    require(type(commit) is str and re.fullmatch(r'(?:[0-9a-f]{40}|[0-9a-f]{64})',commit) is not None,'invalid source commit')
    require(_git(root,'rev-parse','HEAD')==commit and not _git(root,'status','--porcelain'),'replay requires the specified clean Git source')
    config.verify(); _spec(recipe['target'])
    pins=recipe['pins']; require(type(pins) is dict and bool(pins),'saved-source pins required')
    for path,digest in pins.items():
        digest_value(digest); require(sha256(config.resolve(path))==digest,'saved-source hash mismatch: '+path)
    seed_path=recipe['seed_bundle']; require(seed_path in pins,'seed bundle is not pinned')
    seed=config.read_json(seed_path,pins[seed_path])
    for field in ('sm_capture','pm_capture'):
        for name in ('capture.pkl','capture.json'):
            require(str(absolute(seed[field])/name) in pins,'unbound capture input')
    require(recipe['batch_authority'] in pins,'batch authority is not pinned')
    rankcode=config.resolve(recipe['rank_code_directory'])
    rankpins={config.resolve(path):digest for path,digest in pins.items() if config.resolve(path).parent==rankcode and path.endswith('.py')}
    require(bool(rankpins) and set(rankcode.glob('*.py'))==set(rankpins),'generated rank-code inventory mismatch')
    runtime_pins={str(p):sha256(p) for p in (root/'Verdict').glob('runtime_*.py')}
    runtime_pins.update({str(p):sha256(p) for p in (Path(__file__),root/'trainverify/artifact_tools.py',root/'Verdict/graph_to_lean.py')})
    sys.dont_write_bytecode=True
    sys.path.insert(0,str(root))
    sys.path.insert(0,str(root/'Verdict'))
    from Verdict import graph_to_lean as compiler
    from Verdict import runtime_initial_relations as initial
    from Verdict.runtime_schedule import build
    module=importlib.import_module(recipe['target']['module'])
    for loaded in (compiler,initial,module):
        require(Path(loaded.__file__).resolve()==root/'Verdict'/(loaded.__name__.split('.')[-1]+'.py'),'compiler/renderer imported from the wrong source root')
    out=absolute(str(out)); out.parent.mkdir(parents=True,exist_ok=True); out.mkdir(exist_ok=False)
    report=dict(passed=False,head=commit,actual_saved_source=True,new_capture=False,published=False,
        public_complete=False,torch_refinement=False,config_sha256=config.config_sha256)
    class LocalComplete(Exception): pass
    calls=0
    def observe(world,sm,pm,parameter_inputs,lineages,validation):
        nonlocal calls
        calls+=1; require(calls==1,'duplicate common-context attachment')
        bound=initial.bind(sm,pm,parameter_inputs,lineages,validation)
        order=dict(sm=build(sm),pm=build(pm))
        require(order==world.receipt['execution_order'],'original execution order mismatch')
        result=render_context(module,recipe['ancestors'],recipe['target'],out,sm,pm,lineages,validation,bound,order)
        emit(dict(execution_order=order,bound=bound,world_fullrefs=world.receipt.get('fullrefs'),
            source_hashes={**pins,**runtime_pins},head=commit,predecessor_public_calls=result['predecessor_public_calls'],
            local_only=True,published=False,kernel_checked=False),out/'world-binding.json',print_report=False)
        report['counts']={key:len(result['detail'][key]) for key in ('reads','units','frontier_units','retained_units','deferred_units')}
        raise LocalComplete()
    argv=['graph_to_lean','--sm-pkl',str(config.resolve(seed['sm_capture'])/'capture.pkl'),
        '--pm-pkl',str(config.resolve(seed['pm_capture'])/'capture.pkl'),'--verifier-cache-dir',str(out/'capture-cache'),
        '--runtime-rank-code-directory',str(rankcode),'--runtime-batch-authority',str(config.resolve(recipe['batch_authority'])),
        '--out',str(out/'NEVER/GeneratedData.lean'),'--module','Never.GeneratedData',
        '--runtime-input-handoff',str(config.resolve(seed['pm_run'])),'--runtime-world-definitions-out',str(out/'NEVER-WORLD/RuntimeWorld.lean'),
        '--runtime-seed-bundle',str(config.resolve(seed_path))]
    emit(dict(argv=argv,root=str(root),head=commit,source_hashes={**pins,**runtime_pins}),out/'command.json',print_report=False)
    started=time.monotonic()
    try:
        with patch.object(initial,'attach',observe),patch.object(sys,'argv',argv):
            try: compiler.main()
            except LocalComplete: pass
            else: raise ValueError('original common-context authority hook not reached')
        require(calls==1 and not (out/'NEVER').exists() and not (out/'NEVER-WORLD').exists(),'canonical output escaped the local hook')
        for path,digest in {**pins,**runtime_pins}.items():
            require(sha256(config.resolve(path))==digest,'replay input/source changed: '+path)
        config.verify()
        require(_git(root,'rev-parse','HEAD')==commit and not _git(root,'status','--porcelain'),'replay source drift')
        report['passed']=True
        return report
    finally:
        report['seconds']=time.monotonic()-started
        emit(report,out/'render-result.json')


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config',required=True); parser.add_argument('--recipe',required=True)
    parser.add_argument('--recipe-sha256',required=True); parser.add_argument('--expected-commit',required=True)
    parser.add_argument('--out',required=True)
    args=parser.parse_args(argv)
    try:
        config=Configuration.load(args.config)
        recipe=config.read_json(args.recipe,args.recipe_sha256)
        replay(config,recipe,Path(__file__).resolve().parents[1],args.out,args.expected_commit)
        return 0
    except (ValueError,OSError,KeyError,TypeError,AttributeError) as exc:
        print(json.dumps(dict(status='error',error=str(exc))))
        return 2


if __name__=='__main__':
    raise SystemExit(main())
