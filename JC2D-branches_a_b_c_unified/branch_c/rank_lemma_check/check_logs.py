"""check_logs.py -- read the Lean logs written by run.sh and decide PASS or FAIL.

  checks    every RCCheck module: exit 0, no error, both `#print axioms` lines read exactly `[propext]`;
            the generated check modules hold 2 n theorems (n = the number of columns);
  controls  RCControls: an error on exactly the lines listed under "fail" in RCControls.expect.json, none on the
            "pass" line, and ctrl_pass depends on `[propext]` only.
usage: python3 check_logs.py LEANDIR LOGDIR K
"""
import sys, os, re, json

LEANDIR, LOGDIR, K = sys.argv[1], sys.argv[2], int(sys.argv[3])
ok = True
for mod in ["RCCommon"] + [f"RCData{k:02d}" for k in range(K)]:
    log = open(os.path.join(LOGDIR, mod + ".log")).read()
    good = re.search(rf"{mod}: exit 0,", log) is not None and not re.search(r":\d+:\d+: error", log)
    print(f"{mod}: {'built' if good else 'FAILED'}")
    ok &= good
nthm, axioms = 0, []
for k in range(K):
    mod = f"RCCheck{k:02d}"
    log = open(os.path.join(LOGDIR, mod + ".log")).read()
    src = open(os.path.join(LEANDIR, mod + ".lean")).read()
    nthm += len(re.findall(r"^theorem ", src, re.M))
    errs = [l for l in log.splitlines() if re.search(r":\d+:\d+: error", l)]
    ax = re.findall(r"'([\w.]+)' depends on axioms: (\[.*?\])", log)
    exit0 = re.search(rf"{mod}: exit 0,", log) is not None
    good = exit0 and not errs and len(ax) == 2 and all(a == "[propext]" for _, a in ax)
    axioms += ax
    print(f"{mod}: exit 0 {exit0}; errors {len(errs)}; axioms {[a for _, a in ax]}: {'ok' if good else 'FAIL'}")
    ok &= good
ncols = sum(len(re.findall(r"^noncomputable def Cpk_", open(os.path.join(LEANDIR, f"RCData{k:02d}.lean")).read(), re.M))
            for k in range(K))
print(f"theorems in the check modules: {nthm} (2 x {ncols} packed columns: {nthm == 2 * ncols})")
ok &= nthm == 2 * ncols
exp = json.load(open(os.path.join(LEANDIR, "RCControls.expect.json")))
log = open(os.path.join(LOGDIR, "RCControls.log")).read()
err_lines = {int(m) for m in re.findall(r"RCControls\.lean:(\d+):\d+: error", log)}
want_fail = {int(x) for x in exp["fail"]}
want_pass = {int(x) for x in exp["pass"]}
ax = re.findall(r"'[\w.]+ctrl_pass' depends on axioms: (\[.*?\])", log)
good = err_lines == want_fail and not (err_lines & want_pass) and ax == ["[propext]"]
for line, name in sorted(((int(a), b) for a, b in exp["fail"].items())):
    print(f"control {name} (line {line}): {'rejected' if line in err_lines else 'NOT REJECTED'}")
for line, name in exp["pass"].items():
    print(f"control {name} (line {line}): {'FAILED' if int(line) in err_lines else 'passes'}; axioms {ax}")
print(f"controls on column {exp['column']}: {'ALL AS REQUIRED' if good else 'NOT AS REQUIRED'}")
ok &= good
print("RESULT: PASS" if ok else "RESULT: FAIL")
sys.exit(0 if ok else 1)
