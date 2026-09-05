#!/usr/bin/env python3
"""Lower legacy YOCO-3B authority heartbeat budget to the compiler policy."""
from __future__ import annotations
import argparse, hashlib, os, tempfile
from pathlib import Path
INPUT_SHA256="145300e8f502bb9a12a99fa5fba2fa9850b1f3d766fe9be434c35c898a9f3198"
OUTPUT_SHA256="b5396db5b636a8fa100eaec805ef33c73b3bc57fce9ddce7b9bc6795552b4999"
OLD="set_option maxHeartbeats 4000000"
NEW="set_option maxHeartbeats 500000"
def sha256(data):return hashlib.sha256(data).hexdigest()
def transform(source):
    if source.count(OLD)==1 and NEW not in source:return source.replace(OLD,NEW,1),1
    if OLD not in source and source.count(NEW)==1:return source,0
    raise RuntimeError("mixed or malformed heartbeat policy state")
def write_atomic(path,data):
    path.parent.mkdir(parents=True,exist_ok=True);fd,tmp=tempfile.mkstemp(prefix=f".{path.name}.",dir=path.parent)
    try:
        with os.fdopen(fd,"wb") as f:f.write(data);f.flush();os.fsync(f.fileno())
        os.replace(tmp,path)
    except BaseException:
        try:os.unlink(tmp)
        except FileNotFoundError:pass
        raise
def main():
    p=argparse.ArgumentParser();p.add_argument("input",type=Path);p.add_argument("output",type=Path);a=p.parse_args();data=a.input.read_bytes();d=sha256(data)
    if d not in {INPUT_SHA256,OUTPUT_SHA256}:raise RuntimeError(f"unexpected input SHA-256: {d}")
    out,n=transform(data.decode());result=out.encode()
    if sha256(result)!=OUTPUT_SHA256:raise RuntimeError(f"unexpected output SHA-256: {sha256(result)}")
    write_atomic(a.output,result);print(f"heartbeat_budget input={d} output={sha256(result)} changed={n}")
if __name__=="__main__":main()
