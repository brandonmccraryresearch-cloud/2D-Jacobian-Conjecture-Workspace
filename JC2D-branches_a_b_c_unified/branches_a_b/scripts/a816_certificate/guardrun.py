#!/usr/bin/env python3
"""guardrun.py [--max-anon MB] -- cmd ... : run cmd; kill it if the bash memory cgroup's anonymous + mapped memory
exceeds the threshold (the cgroup limit, ~5.8 GiB, covers every process started from the shell, including the
concurrent chain build; the OOM killer would otherwise pick the largest process).  Reports wall time, peak RSS of the
largest process in the command's process group, and the cgroup peak."""
import os, sys, time, subprocess, signal, threading
args = sys.argv[1:]
max_anon = 5000
verbose = False
if args and args[0] == "--verbose": verbose = True; args = args[1:]
if args and args[0] == "--max-anon": max_anon = int(args[1]); args = args[2:]
if args and args[0] == "--verbose": verbose = True; args = args[1:]
if args and args[0] == "--min-avail": args = args[2:]          # backwards compatibility (ignored)
if args and args[0] == "--": args = args[1:]
def _detect_cg():
    """the memory cgroup (v1) of this process; PROCMON_CGROUP overrides"""
    if os.environ.get("PROCMON_CGROUP"): return os.environ["PROCMON_CGROUP"]
    try:
        for line in open("/proc/self/cgroup"):
            hid, ctrl, path = line.strip().split(":", 2)
            if "memory" in ctrl.split(","): return "/sys/fs/cgroup/memory" + path
    except OSError: pass
    return "/sys/fs/cgroup/memory"
CG = _detect_cg()
def cg_mb():
    try:
        d = {}
        for line in open(os.path.join(CG, "memory.stat")):
            k, v = line.split(); d[k] = int(v)
        return d.get("total_rss", 0) // (1 << 20)          # anonymous memory: what the OOM killer counts
    except Exception:
        return 0
t0 = time.time()
p = subprocess.Popen(args, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True)
out = []
def reader():
    for line in p.stdout:
        t = line.decode(errors="replace")
        if verbose:                       # stream everything, unfiltered and untruncated
            sys.stdout.write(t); sys.stdout.flush()
        else:
            out.append(t)
th = threading.Thread(target=reader); th.start()
peak, cgpeak, killed = 0, 0, False
while p.poll() is None:
    for pid in os.listdir("/proc"):
        if not pid.isdigit(): continue
        try:
            if os.getpgid(int(pid)) != p.pid: continue
            for line in open(f"/proc/{pid}/status"):
                if line.startswith("VmHWM:"): peak = max(peak, int(line.split()[1]) // 1024)
        except Exception: pass
    c = cg_mb(); cgpeak = max(cgpeak, c)
    if c > max_anon and not killed:
        os.killpg(p.pid, signal.SIGKILL); killed = True
    if verbose and time.time() - globals().get('_last', 0) >= 10:
        globals()['_last'] = time.time()
        sys.stderr.write(f"[guardrun {time.strftime('%H:%M:%S')}] elapsed {time.time() - t0:.0f}s  peak RSS {peak} MB  cgroup anon {c} MB\n"); sys.stderr.flush()
    time.sleep(0.3)
th.join()
sys.stdout.write("".join(out[-60:]))          # non-verbose: the last 60 lines only
print(f"[guardrun] exit {p.returncode}  {time.time() - t0:.1f}s  peak RSS {peak} MB  cgroup anon peak {cgpeak} MB"
      + ("  KILLED (memory guard)" if killed else ""))
sys.exit(0 if p.returncode == 0 else 1)
