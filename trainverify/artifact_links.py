"""Checked link relocation for operator-owned, quiescent artifact directories.

Cooperating invocations lock the same scan-root directory inodes. This is not a
sandbox against hostile same-UID writers. Partial failures keep legacy aliases;
reapplying the original plan resumes without rolling back unrelated entries.
"""
from contextlib import contextmanager
import fcntl
import os
from pathlib import Path
import stat
import uuid
from typing import Any

from trainverify.artifact_tools import absolute,digest_value,keys,natural,require


def _roots(config,roots):
    require(type(roots) in (list,tuple) and bool(roots),'scan roots required')
    paths=sorted({config.resolve(str(p)).resolve() for p in roots})
    require(all(p.is_dir() for p in paths),'scan root missing')
    return [p for p in paths if not any(p!=q and p.is_relative_to(q) for q in paths)]


@contextmanager
def _locked(roots):
    fds=[]
    try:
        for root in roots:
            fd=os.open(root,os.O_RDONLY|os.O_DIRECTORY); fds.append(fd)
            fcntl.flock(fd,fcntl.LOCK_EX|fcntl.LOCK_NB)
        yield
    finally:
        for fd in reversed(fds): os.close(fd)


def _identity(path,follow=True):
    s=path.stat() if follow else path.lstat()
    return [s.st_dev,s.st_ino,stat.S_IFMT(s.st_mode)]


def _new_target(config,path,old_target):
    # POSIX link payloads are not canonical manifest identifiers. Normalize a
    # lookup key, preserve the original payload, and verify the real referent
    # separately: lexical '..' must not silently cross a symlink directory.
    old=Path(os.path.abspath(path.parent/old_target))
    new=config.resolve(old)
    return str(new) if new!=old else None


def plan_links(config,roots)->dict[str,Any]:
    roots=_roots(config,roots); entries=[]
    def inaccessible(error): raise error
    for root in roots:
        for directory,dirs,files in os.walk(root,followlinks=False,onerror=inaccessible):
            for name in dirs+files:
                p=Path(directory)/name
                if not p.is_symlink(): continue
                old=os.readlink(p); new=_new_target(config,p,old)
                if new is None: continue
                require(p.parent.resolve()==p.parent,'symlink parent is not a physical directory')
                target=Path(new)
                require(p.resolve()==target.resolve(),'link normalization changes the real referent: '+str(p))
                require(_identity(p)==_identity(target),'relocation changes the target identity: '+str(p))
                entries.append(dict(path=str(p),old_target=old,new_target=new,
                    link_identity=_identity(p,False),target_identity=_identity(target)))
    return dict(version=1,config_sha256=config.config_sha256,roots=[str(p) for p in roots],
        links=sorted(entries,key=lambda row:row['path']))


def _validate_entry(config,row,roots):
    keys(row,('path','old_target','new_target','link_identity','target_identity'),'link plan entry')
    p=absolute(row['path'])
    require(any(p.is_relative_to(root) and p!=root for root in roots),'link outside declared scan roots')
    require(p.parent.resolve()==p.parent,'link parent escaped scan roots')
    require(type(row['old_target']) is str and '\x00' not in row['old_target'],'invalid original link target')
    new=_new_target(config,p,row['old_target'])
    require(new is not None and new==row['new_target'],'forged or nonlegacy relocated link target')
    absolute(row['new_target'])
    for key in ('link_identity','target_identity'):
        require(type(row[key]) is list and len(row[key])==3,'invalid inode identity')
        for value in row[key]: natural(value)
    require(p.is_symlink(),'planned path is no longer a symlink: '+str(p))
    current=os.readlink(p)
    require(current in (row['old_target'],row['new_target']),'planned link target changed')
    require(p.resolve()==Path(row['new_target']).resolve(),'planned real referent changed')
    require(_identity(p)==row['target_identity'],'planned payload identity changed')
    if current==row['old_target']:
        require(_identity(p,False)==row['link_identity'],'planned symlink inode changed')
    return current==row['old_target']


def _replace(row):
    p=Path(row['path']); fd=os.open(p.parent,os.O_RDONLY|os.O_DIRECTORY)
    temporary='.artifact-link-'+uuid.uuid4().hex; owned=None
    try:
        current=os.stat(p.name,dir_fd=fd,follow_symlinks=False)
        require([current.st_dev,current.st_ino,stat.S_IFMT(current.st_mode)]==row['link_identity'],'link changed before replacement')
        os.symlink(row['new_target'],temporary,dir_fd=fd)
        s=os.stat(temporary,dir_fd=fd,follow_symlinks=False); owned=(s.st_dev,s.st_ino)
        os.replace(temporary,p.name,src_dir_fd=fd,dst_dir_fd=fd)
        s=os.stat(p.name,dir_fd=fd,follow_symlinks=False)
        require((s.st_dev,s.st_ino)==owned,'replacement ownership mismatch')
    finally:
        if owned is not None:
            try:
                s=os.stat(temporary,dir_fd=fd,follow_symlinks=False)
                if (s.st_dev,s.st_ino)==owned: os.unlink(temporary,dir_fd=fd)
            except FileNotFoundError: pass
        os.close(fd)


def apply_links(config,plan):
    keys(plan,('version','config_sha256','roots','links'),'link plan')
    require(type(plan['version']) is int and plan['version']==1,'invalid link plan version')
    digest_value(plan['config_sha256'])
    require(plan['config_sha256']==config.config_sha256,'link plan configuration changed')
    roots=_roots(config,plan['roots'])
    require([str(p) for p in roots]==plan['roots'],'noncanonical plan roots')
    require(type(plan['links']) is list,'invalid link plan rows')
    with _locked(roots):
        config.verify()
        paths=[row['path'] for row in plan['links']]
        require(len(paths)==len(set(paths)),'duplicate planned link')
        for row in plan['links']: _validate_entry(config,row,roots)
        current=plan_links(config,roots)
        require({r['path'] for r in current['links']}<=set(paths),'plan omits current legacy references')
        changed=0; touched=set()
        for row in plan['links']:
            if _validate_entry(config,row,roots):
                _replace(row); changed+=1; touched.add(Path(row['path']).parent)
        for parent in touched:
            fd=os.open(parent,os.O_RDONLY|os.O_DIRECTORY)
            try: os.fsync(fd)
            finally: os.close(fd)
        require(not plan_links(config,roots)['links'],'legacy references appeared during relocation')
        config.verify()
        return dict(status='relocated',rewritten_links=changed,plan_links=len(paths),legacy_aliases_removed=False)


def remove_aliases(config,roots):
    roots=_roots(config,roots)
    with _locked(roots):
        config.verify()
        require(not plan_links(config,roots)['links'],'remaining legacy link references block alias removal')
        selected=[]
        for kind,old,new in config.relocations:
            if kind!='directory' or not os.path.lexists(old): continue
            require(old.is_symlink() and os.readlink(old)==str(new),'legacy alias does not match the configured directory')
            require(_identity(old)==_identity(new),'legacy alias target mismatch')
            selected.append((old,_identity(old,False)))
        for old,identity in selected:
            require(_identity(old,False)==identity,'legacy alias changed before removal')
            old.unlink()
            fd=os.open(old.parent,os.O_RDONLY|os.O_DIRECTORY)
            try: os.fsync(fd)
            finally: os.close(fd)
        config.verify()
        return dict(status='retired',removed_aliases=len(selected),preserved_targets=True)
