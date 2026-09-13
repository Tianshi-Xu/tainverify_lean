"""Versioned local artifact verification with explicit legacy-path relocation.

Configuration is operator-owned input, not proof authority. Immutable receipt
hashes authenticate historical bytes; verification never rewrites those bytes.
No pickle loading, capture, theorem weakening or implicit filesystem fallback.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import sys
from typing import Any


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha256(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as stream:
        for chunk in iter(lambda:stream.read(4*1024*1024),b''):
            h.update(chunk)
    return h.hexdigest()


def strict_json(data):
    def pairs(items):
        out={}
        for key,value in items:
            require(key not in out, 'duplicate JSON key: '+key)
            out[key]=value
        return out
    def constant(value):
        raise ValueError('non-finite JSON constant: '+value)
    return json.loads(data,object_pairs_hook=pairs,parse_constant=constant)


def keys(value, expected, label):
    require(type(value) is dict and set(value)==set(expected),label+' fields mismatch')


def digest_value(value):
    require(type(value) is str and re.fullmatch('[0-9a-f]{64}',value) is not None,'invalid SHA256')
    return value


def absolute(value):
    require(type(value) is str and '\x00' not in value,'invalid path type')
    p=PurePosixPath(value)
    require(p.is_absolute() and '..' not in p.parts and str(p)==value,'noncanonical absolute path: '+value)
    return Path(value)


class Configuration:
    def __init__(self,data:dict[str,Any],config_sha256=None):
        keys(data,('version','relocations','binding_sets','lean'),'configuration')
        require(type(data['version']) is int and data['version']==1,'unsupported configuration version')
        require(type(data['relocations']) is list,'relocations must be a list')
        self.relocations=[]
        for row in data['relocations']:
            keys(row,('kind','source','target'),'relocation')
            require(row['kind'] in ('directory','file'),'unknown relocation kind')
            source,target=absolute(row['source']),absolute(row['target'])
            require(source!=target,'self relocation')
            self.relocations.append((row['kind'],source,target))
        for i,(_,source,target) in enumerate(self.relocations):
            for j,(_,other,_) in enumerate(self.relocations):
                if i!=j:
                    require(not source.is_relative_to(other),'overlapping relocation sources')
                require(not target.is_relative_to(other),'relocation target depends on a retired path')
        self.binding_sets:list[dict[str,Any]]=data['binding_sets']
        require(type(self.binding_sets) is list and bool(self.binding_sets),'nonempty binding sets required')
        for row in self.binding_sets:
            keys(row,('path','sha256','field','base'),'binding set')
            absolute(row['path']); digest_value(row['sha256'])
            require(type(row['field']) is list and all(type(k) is str for k in row['field']),'invalid field selector')
            if row['base'] is not None:
                absolute(row['base'])
        self.lean=data['lean']
        if self.lean is not None:
            keys(self.lean,('executable','sha256','paths'),'Lean configuration')
            absolute(self.lean['executable']); digest_value(self.lean['sha256'])
            require(type(self.lean['paths']) is list and bool(self.lean['paths']),'Lean search paths required')
            for path in self.lean['paths']: absolute(path)
        self.config_sha256=config_sha256

    @classmethod
    def load(cls,path):
        data=Path(path).read_bytes()
        return cls(strict_json(data),hashlib.sha256(data).hexdigest())

    def resolve(self,value):
        path=absolute(str(value) if isinstance(value,Path) else value)
        for kind,source,target in self.relocations:
            if path==source or (kind=='directory' and path.is_relative_to(source)):
                return target/path.relative_to(source)
        return path

    def read_json(self,path,expected)->Any:
        digest_value(expected)
        data=self.resolve(path).read_bytes()
        require(hashlib.sha256(data).hexdigest()==expected,'JSON artifact hash mismatch: '+str(path))
        return strict_json(data)

    def bindings(self):
        result={}
        for row in self.binding_sets:
            value=self.read_json(row['path'],row['sha256'])
            for field in row['field']:
                require(type(value) is dict and field in value,'missing binding field: '+field)
                value=value[field]
            require(type(value) is dict and bool(value),'empty or malformed binding map')
            for path,digest in value.items():
                digest_value(digest)
                if row['base'] is not None:
                    require(type(path) is str,'invalid relative binding path')
                    rel=PurePosixPath(path)
                    require(not rel.is_absolute() and '..' not in rel.parts and str(rel)==path,'noncanonical relative binding path')
                    path=str(absolute(row['base'])/rel)
                absolute(path)
                require(path not in result or result[path]==digest,'conflicting artifact binding: '+path)
                result[path]=digest
        return result

    def verify(self):
        bindings=self.bindings()
        for path,expected in bindings.items():
            require(sha256(self.resolve(path))==expected,'artifact hash mismatch: '+path)
        return dict(status='verified',files_verified=len(bindings),binding_sets=len(self.binding_sets),
            config_sha256=self.config_sha256,relocations=len(self.relocations),proof_admissible=False,
            scope='Historical artifact integrity only; not a new mathematical proof or capture witness.')


_AXIOMS={'propext','Classical.choice','Quot.sound'}


def lean_name(value):
    require(type(value) is str and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*",value) is not None,
        'invalid Lean identifier')
    return value


def natural(value,positive=False):
    require(type(value) is int and value >= (1 if positive else 0),'invalid natural dimension/index')
    return value


def render_joint(rows:list[dict[str,Any]],module):
    """The original global-shape / every-local-shape / mixed-value contract."""
    lean_name(module)
    require(type(rows) is list and bool(rows),'frontier rows required')
    clauses=[]; calls=[]
    for row in rows:
        D=natural(row['dimensions']['D'],True); T=natural(row['dimensions']['T'],True)
        unit=natural(row['unit']); require(unit<D,'DP unit out of range')
        tid=natural(row['sm_output_tid']); outputs=row['pm_output_tids']
        require(type(outputs) is list and len(outputs)==T and len(set(outputs))==T,'ordered local output cover mismatch')
        for x in outputs: natural(x)
        for key in ('global_shape','local_shape'):
            require(type(row[key]) is list and bool(row[key]),'nonempty shape required')
            for x in row[key]: natural(x,True)
        ys='['+', '.join('q '+str(i) for i in outputs)+']'
        chunk=f'chunkPrimDimN 0 {D} {unit} (t {tid})'; axis=row['gather_axis']
        if row['layout']=='sharded':
            natural(axis); require(axis<len(row['local_shape']),'gather axis out of range')
            relation=f'{chunk} = allGatherPrimDimN {axis} {T} 0 {ys}'
        else:
            require(row['layout']=='replicated_within_dp' and axis is None,'unsupported mixed frontier layout')
            relation=f'(∀ y ∈ {ys}, y = {chunk})'
        clauses.append(f'((t {tid}).shape = {row["global_shape"]} ∧ (∀ y ∈ {ys}, y.shape = {row["local_shape"]}) ∧ {relation})')
        calls.append(lean_name(row['facts_theorem'])+' s p t q hs hp hvalues')
    return ('import '+module+'\nnamespace TrainVerify.Denote.RuntimeWorld\nnoncomputable section\n'
        'theorem projectionFrontierJoint (s p t q : Store)\n'
        '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)\n'
        '    (hvalues : InitialParameterValues s p) :\n    '+' ∧\n    '.join(clauses)+
        ' := by\n  exact ⟨'+', '.join(calls)+'⟩\n#print axioms projectionFrontierJoint\n'
        'end\nend TrainVerify.Denote.RuntimeWorld\n')


def verify_kernel(config,path,expected):
    """Recheck a hash-pinned historical frontier kernel receipt, not rerun it."""
    row=config.read_json(path,expected)
    required={'source','source_sha256','object','object_sha256','inner_exit','axioms','dependency_objects'}
    optional={'module','seconds','command','log','local_only','public_complete','reused','reused_from'}
    require(type(row) is dict and required<=set(row)<=required|optional,'kernel receipt fields mismatch')
    require(type(row['inner_exit']) is int and row['inner_exit']==0,'kernel receipt was not successful')
    for key in ('source','object'):
        digest_value(row[key+'_sha256'])
        require(sha256(config.resolve(row[key]))==row[key+'_sha256'],'kernel '+key+' hash mismatch')
    require(type(row['dependency_objects']) is dict and bool(row['dependency_objects']),'kernel dependencies required')
    for p,h in row['dependency_objects'].items():
        digest_value(h); require(sha256(config.resolve(p))==h,'kernel dependency hash mismatch: '+p)
    require(type(row['axioms']) is dict and bool(row['axioms']),'kernel axiom inventory required')
    for name,axioms in row['axioms'].items():
        lean_name(name)
        require(type(axioms) is list and all(type(x) is str for x in axioms),'invalid axiom list')
        require(len(set(axioms))==len(axioms) and set(axioms)<=_AXIOMS,'unsupported kernel axioms')
    return dict(status='verified',checked_declarations=len(row['axioms']),receipt_sha256=expected,
        source_sha256=row['source_sha256'],object_sha256=row['object_sha256'],proof_admissible=False,
        scope='Integrity of an existing successful conditional kernel receipt; no new kernel invocation.')


def emit(report,output=None,print_report=True):
    text=json.dumps(report,indent=2,allow_nan=False)+'\n'
    if output:
        path=Path(output); path.parent.mkdir(parents=True,exist_ok=True)
        with path.open('x') as stream:
            stream.write(text); stream.flush(); os.fsync(stream.fileno())
    if print_report: print(text,end='')


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    sub=parser.add_subparsers(dest='command',required=True)
    commands={}
    for name in ('verify','resolve','verify-kernel','render-joint','check-lean','plan-links','apply-links','remove-aliases','check-score-exchange'):
        p=sub.add_parser(name); p.add_argument('--config',required=True); p.add_argument('--output')
        commands[name]=p
    commands['resolve'].add_argument('--path',required=True)
    p=commands['verify-kernel']; p.add_argument('--receipt',required=True); p.add_argument('--sha256',required=True)
    p=commands['render-joint']
    for flag in ('detail','sha256','module','source-output'): p.add_argument('--'+flag,required=True)
    p=commands['check-lean']
    for flag in ('source','sha256','out-dir'): p.add_argument('--'+flag,required=True)
    p.add_argument('--query',action='append',required=True); p.add_argument('--module')
    p.add_argument('--timeout',type=int,default=120)
    for name in ('plan-links','remove-aliases'):
        commands[name].add_argument('--scan-root',action='append',required=True)
    p=commands['apply-links']; p.add_argument('--plan',required=True); p.add_argument('--sha256',required=True)
    p=commands['check-score-exchange']
    for flag in ('old-detail','old-sha256','detail','sha256','world','world-sha256','sm-capture','pm-capture'):
        p.add_argument('--'+flag,required=True)
    args=parser.parse_args(argv)
    try:
        config=Configuration.load(args.config)
        if args.command=='verify': report=config.verify()
        elif args.command=='resolve':
            report=dict(original=args.path,resolved=str(config.resolve(args.path)),proof_admissible=False)
        elif args.command=='verify-kernel':
            config.verify(); report=verify_kernel(config,args.receipt,args.sha256)
        elif args.command=='render-joint':
            config.verify(); detail=config.read_json(args.detail,args.sha256)
            require(all(detail.get(f) is False for f in ('proof_admissible','kernel_value_proved','public_complete','torch_refinement')),'renderer flags must remain false')
            source=render_joint(detail['frontier_units'],args.module)
            target=absolute(args.source_output); target.parent.mkdir(parents=True,exist_ok=True)
            with target.open('x') as stream: stream.write(source)
            report=dict(status='rendered',source=str(target),source_sha256=sha256(target),full_contracts=len(detail['frontier_units']),kernel_checked=False,proof_admissible=False)
        elif args.command=='check-lean':
            from trainverify.artifact_lean import run_lean
            report=run_lean(config,args.source,args.sha256,args.out_dir,args.query,args.timeout,args.module)
        elif args.command in ('plan-links','apply-links','remove-aliases'):
            from trainverify.artifact_links import plan_links,apply_links,remove_aliases
            if args.command=='plan-links':
                require(bool(args.output),'persist a link plan with --output')
                config.verify(); plan=plan_links(config,args.scan_root)
                emit(plan,args.output,print_report=False)
                emit(dict(status='planned',links=len(plan['links']),plan=args.output,plan_sha256=sha256(args.output)))
                return 0
            if args.command=='apply-links': report=apply_links(config,config.read_json(args.plan,args.sha256))
            else: report=remove_aliases(config,args.scan_root)
        else:
            from trainverify.score_exchange_audit import check_raw,load_worlds
            config.verify()
            old=config.read_json(args.old_detail,args.old_sha256); detail=config.read_json(args.detail,args.sha256)
            world=config.read_json(args.world,args.world_sha256)
            sm,pm=load_worlds(config,world['source_hashes'],args.sm_capture,args.pm_capture)
            report=check_raw(sm,pm,old,detail,world)
        emit(report,args.output)
        return 0
    except (ValueError,OSError,KeyError,TypeError,AttributeError) as exc:
        print(json.dumps(dict(status='error',error=str(exc))))
        return 2


if __name__=='__main__':
    raise SystemExit(main())
