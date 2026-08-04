#!/usr/bin/env python3
"""Bridge emitter — regression harness (backup-safe).

For each written GoalNBridge.lean:
  1. back up original to BACKUP_DIR
  2. regenerate via emit2 (--no-compile)
  3. compile with lake env lean
  4. check exit0 + 0 sorry
  5. ALWAYS restore original from backup
Records PASS / FAIL / SKIP and reasons. Never leaves a tracked file modified.

    python3 regress.py [N ...]        # specific goals, or all if none given
    python3 regress.py --report       # just print last report
"""
import os, sys, re, subprocess, shutil, glob, json, time

HERE = os.path.dirname(os.path.abspath(__file__))
TV   = os.path.dirname(HERE)
DEN  = "denote/gpt_ly4_regen"
DEND = os.path.join(TV, DEN)
BACKUP = os.path.join(TV, ".lake", "bridge_backup")
RESULTS_JSON = os.path.join(HERE, "regress_results.json")


def written_goals():
    # only git-tracked GoalNBridge.lean (avoid stray untracked artifacts)
    r = subprocess.run(["git", "ls-files", DEN], cwd=TV, capture_output=True, text=True)
    ns = []
    for f in r.stdout.splitlines():
        m = re.search(r'Goal(\d+)Bridge\.lean$', f)
        if m:
            ns.append(int(m.group(1)))
    return sorted(ns)


def compile_bridge(n, timeout=900):
    r = subprocess.run(["lake", "env", "lean", f"{DEN}/Goal{n}Bridge.lean"],
                       cwd=TV, capture_output=True, text=True, timeout=timeout)
    out = r.stdout + "\n" + r.stderr
    return r.returncode, out


def run_one(n):
    src = os.path.join(DEND, f"Goal{n}Bridge.lean")
    bak = os.path.join(BACKUP, f"Goal{n}Bridge.lean")
    os.makedirs(BACKUP, exist_ok=True)
    shutil.copy2(src, bak)
    rec = {"n": n, "status": "?", "reason": ""}
    try:
        gen = subprocess.run([sys.executable, os.path.join(HERE, "emit2.py"), str(n),
                              "--no-compile", "--quiet"],
                             cwd=HERE, capture_output=True, text=True, timeout=900)
        if gen.returncode != 0:
            tail = (gen.stdout + gen.stderr).strip().splitlines()
            rec["status"] = "SKIP"
            rec["reason"] = "emit: " + (tail[-1] if tail else "gen failed")
            # detect unsupported topology
            blob = gen.stdout + gen.stderr
            m = re.search(r'UnsupportedTopology: (.*)', blob)
            if m:
                rec["reason"] = "unsupported: " + m.group(1).strip()
            return rec
        t0 = time.time()
        try:
            rc, out = compile_bridge(n)
        except subprocess.TimeoutExpired:
            rec["secs"] = round(time.time() - t0, 1)
            rec["status"] = "FAIL"
            rec["reason"] = "compile timeout >900s"
            return rec
        rec["secs"] = round(time.time() - t0, 1)
        nsorry = len(re.findall(r'\bsorry\b', out))
        if rc == 0 and nsorry == 0:
            rec["status"] = "PASS"
        else:
            rec["status"] = "FAIL"
            errs = [l for l in out.splitlines() if "error" in l.lower()][:4]
            rec["reason"] = f"rc={rc} sorry={nsorry}: " + " | ".join(errs)[:400]
    finally:
        shutil.copy2(bak, src)   # ALWAYS restore
    return rec


def main():
    args = sys.argv[1:]
    if "--report" in args:
        print(open(RESULTS_JSON).read()); return
    ns = [int(a) for a in args if a.isdigit()] or written_goals()
    results = {}
    if os.path.exists(RESULTS_JSON):
        try: results = {int(k): v for k, v in json.load(open(RESULTS_JSON)).items()}
        except Exception: results = {}
    for n in ns:
        rec = run_one(n)
        results[n] = rec
        print(f"g{n}: {rec['status']:5s} {rec.get('reason','')[:160]}")
        json.dump({str(k): v for k, v in sorted(results.items())},
                  open(RESULTS_JSON, "w"), indent=1)
    # verify nothing tracked modified
    st = subprocess.run(["git", "status", "--short", "--", DEN],
                        cwd=TV, capture_output=True, text=True)
    dirty = [l for l in st.stdout.splitlines() if l and not l.strip().endswith("ProbeAuto.lean")]
    if dirty:
        print("!!! WARNING tracked files modified:\n" + "\n".join(dirty))
    p = sum(1 for r in results.values() if r["status"] == "PASS")
    f = sum(1 for r in results.values() if r["status"] == "FAIL")
    s = sum(1 for r in results.values() if r["status"] == "SKIP")
    print(f"\n=== {p} PASS / {f} FAIL / {s} SKIP  (of {len(results)}) ===")


if __name__ == "__main__":
    main()
