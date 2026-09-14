"""Direct, bounded Lean checks over explicit immutable artifact inputs.

No Lake build, cache population or accepted-object overwrite. The executable,
search roots and expected hashes are trusted operator configuration, not a
sandbox or a replacement for semantic/source review.
"""
import hashlib
import os
from pathlib import Path
import re
import signal
import subprocess
import time

from trainverify.artifact_tools import _AXIOMS,absolute,emit,lean_name,require,sha256


def resolve_import(module,paths):
    lean_name(module)
    for root in map(Path,paths):
        anchor=root/module.split('.')[0]
        if anchor.is_dir() or anchor.with_suffix('.olean').is_file():
            path=root/('/'.join(module.split('.'))+'.olean')
            require(path.is_file(),'first Lean namespace lacks imported module: '+str(path))
            return path
    raise ValueError('Lean import namespace unavailable: '+module)


def _stdout_lines(text):
    require(type(text) is str,'Lean stdout must be text')
    # Remove only the final LF terminator, never blank lines or other whitespace.
    return iter(text.removesuffix('\n').split('\n'))


def _parse_axiom_record(line,lines):
    """Consume one standard #print axioms record, not arbitrary multiline output.

    Lean may break a comma-separated list onto space-indented lines. Each
    fragment must end in a comma (continue) or the closing bracket (stop).
    Name domains and axiom allowlists remain the caller's responsibility.
    """
    match=re.fullmatch(r"'(.+)' does not depend on any axioms",line)
    if match:
        return match.group(1),[]
    match=re.fullmatch(r"'(.+)' depends on axioms: \[(.*)",line)
    require(match is not None,'unexpected Lean output: '+line)
    name,fragment=match.groups()
    if fragment==']':
        return name,[]
    values=[]
    token=r"[A-Za-z_][A-Za-z0-9_.']*"
    while True:
        match=re.fullmatch('('+token+'(?:, *'+token+')*)(,|\\])',fragment)
        require(match is not None,'unexpected Lean output: '+fragment)
        items,ending=match.groups()
        values.extend(v.strip(' ') for v in items.split(','))
        if ending==']':
            return name,values
        continuation=next(lines,None)
        require(continuation is not None,'unclosed Lean axiom list')
        require(continuation.startswith(' '),'unexpected Lean output: '+continuation)
        fragment=continuation.lstrip(' ')


def parse_axioms(text,expected):
    require(type(expected) is list and bool(expected),'explicit axiom query inventory required')
    for name in expected: lean_name(name)
    require(len(expected)==len(set(expected)),'duplicate expected axiom query')
    result={}
    lines=_stdout_lines(text)
    for line in lines:
        name,axioms=_parse_axiom_record(line,lines)
        lean_name(name)
        require(name not in result,'duplicate printed axiom query')
        require(len(set(axioms))==len(axioms) and set(axioms)<=_AXIOMS,'unsupported or duplicate Lean axioms')
        result[name]=axioms
    require(set(result)==set(expected),'Lean axiom query inventory mismatch')
    return result


def run_lean(config,source,expected,outdir,queries,timeout=120,module=None):
    # The existing entry point remains axiom-only and fail-closed.
    return _run_lean(config,source,expected,outdir,queries,timeout,module,
        lambda text: {'axioms': parse_axioms(text,queries)},lean_name,{})


def _run_lean(config,source,expected,outdir,queries,timeout,module,parse_output,query_name,metadata):
    # Check supplied source bytes before creating any output or launching Lean.
    data=config.resolve(source).read_bytes()
    require(hashlib.sha256(data).hexdigest()==expected,'Lean source hash mismatch')
    require(type(timeout) is int and 0<timeout<=1800,'invalid Lean timeout')
    for name in queries: query_name(name)
    require(bool(queries) and len(set(queries))==len(queries),'explicit distinct queries required')
    module=lean_name(module or Path(source).stem)
    config.verify()
    require(config.lean is not None,'Lean configuration missing')
    executable=config.resolve(config.lean['executable'])
    require(sha256(executable)==config.lean['sha256'],'Lean executable hash mismatch')
    roots=[config.resolve(p) for p in config.lean['paths']]
    require(all(p.is_dir() for p in roots),'Lean search root missing')
    pinned={}
    bindings=config.bindings()
    for path,digest in bindings.items():
        physical=config.resolve(path).resolve()
        require(physical not in pinned or pinned[physical]==digest,'conflicting physical artifact binding')
        pinned[physical]=digest
    imports={}
    for line in data.decode().splitlines():
        line=line.split('--',1)[0].strip()
        if line.startswith(('import ','public import ','private import ')):
            for name in line.split('import ',1)[1].split():
                obj=resolve_import(name,roots); physical=obj.resolve()
                require(physical in pinned,'direct Lean import is not pinned: '+str(obj))
                require(sha256(obj)==pinned[physical],'direct Lean import hash mismatch')
                imports[str(obj)]=pinned[physical]
    require(bool(imports),'explicit pinned imports required')
    env={k:v for k,v in os.environ.items() if k not in ('LEAN_PATH','LEAN_SYSROOT','LEAN_SRC_PATH')}
    env.update(LEAN_PATH=':'.join(map(str,roots)),LEAN_NUM_THREADS='1')
    version=subprocess.run([str(executable),'--version'],env=env,capture_output=True,text=True,timeout=15)
    require(version.returncode==0 and version.stdout.startswith('Lean (version '),'configured executable is not Lean')
    out=absolute(str(outdir))
    require(out.parent.resolve()==out.parent and out.parent.is_dir(),'physical existing output parent required')
    out.mkdir(exist_ok=False)
    relative=Path(*module.split('.'))
    staged=out/relative.with_suffix('.lean'); staged.parent.mkdir(parents=True,exist_ok=True)
    staged.write_bytes(data)
    obj=out/'objects'/relative.with_suffix('.olean'); obj.parent.mkdir(parents=True,exist_ok=True)
    command=[str(executable),'-j1','--tstack=65536','-DmaxHeartbeats=500000','-DmaxRecDepth=4096','-o',str(obj),str(staged)]
    report=dict(status='failed',module=module,original_source=source,source=str(staged),source_sha256=expected,
        command=command,dependency_objects=imports,config_sha256=config.config_sha256,
        proof_admissible=False,whole_capture_witness=False,recompiled_accepted_modules=False,
        executable_sha256=config.lean['sha256'],lean_version=version.stdout.strip(),
        lean_path=list(map(str,roots)),artifact_bindings=bindings,timeout=timeout,
        cwd=str(out),lean_num_threads=1,**metadata)
    def save_logs(stdout,stderr):
        for name,text in (('stdout',stdout),('stderr',stderr),('log',stdout+stderr)):
            path=out/('lean.log' if name=='log' else name+'.log')
            path.write_text(text)
            report[name]=str(path); report[name+'_sha256']=sha256(path)
    started=time.monotonic()
    try:
        proc=subprocess.Popen(command,cwd=out,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,start_new_session=True)
        try:
            stdout,stderr=proc.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid,signal.SIGKILL); stdout,stderr=proc.communicate()
            save_logs(stdout,stderr)
            raise ValueError('Lean check timed out')
        save_logs(stdout,stderr)
        report['inner_exit']=proc.returncode
        require(proc.returncode==0 and not stderr,'Lean check failed; see '+str(out/'lean.log'))
        report.update(parse_output(stdout))
        require(sha256(staged)==expected,'staged Lean source changed')
        require(obj.is_file() and obj.stat().st_size>0,'Lean produced no object')
        config.verify()
        require(sha256(executable)==config.lean['sha256'],'Lean executable changed during check')
        report.update(status='checked',kernel_checked=True,object=str(obj),object_sha256=sha256(obj),
            checked_queries=len(queries),log=str(out/'lean.log'))
        return report
    finally:
        report['seconds']=time.monotonic()-started
        emit(report,out/'result.json',print_report=False)
