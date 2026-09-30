#!/usr/bin/env python3
"""procmon.py (v2) -- developer-level, cgroup-aware process diagnostics for this session.

Why: every shell-launched process shares ONE memory cgroup (limit ~5.98 GB).  The OOM killer enforces that limit, and
/proc/meminfo (MemAvailable) does not show it.  What the OOM killer counts is anonymous memory (heap); memory-mapped
.olean files are shared and reclaimable, but evicting them makes Lean thrash (major faults, working-set refaults).

LOGS (in --dir, default this directory)
  procmon.debug.log   DEBUG and up: every sample in logfmt (key=value), one line for the cgroup, one for the system,
                      one per process (state, cpu%, rss/anon/file, PSS split from smaps_rollup, private dirty, minor/
                      major faults per second, I/O rates, context switches, threads, fds, the .lean file compiled),
                      followed build-log lines, kernel lines, and the monitor's own overhead.  Rotates at 20 MB (x5).
  procmon.log         INFO and up: process start/exit with lifetime peaks, build-log milestones (built/FAILED),
                      WARNING (low anon headroom, fault storms / thrashing, memory-pressure bursts, D-state or zombie
                      processes, a module running unusually long), ERROR (OOM kills with the kernel's lines, build
                      failures, Lean `error:` lines), CRITICAL (the monitor itself failing).
  procmon.jsonl       one structured record per sample (everything above, machine-readable).
Format: `YYYY-mm-dd HH:MM:SS.mmm LEVEL   logger          message key=value ...`

COMMANDS
  run     [--interval S] [--follow FILE ...]   the daemon (default interval 2 s; follows the build logs)
  now     [--verbose]                          snapshot (cgroup, system, every process; --verbose adds smaps split)
  tree                                         process tree of the cgroup (pid, state, rss, anon, cmd)
  report  [--since MIN]                        headroom minimum, OOM/WARN/ERROR events, largest Lean processes
  modules [--since MIN]                        per Lean module: wall time seen, peak RSS/anon/PSS, CPU, major faults
  tail    [N] [--level L] [--grep RE] [--debug] last N lines of the event log (or the debug log), filtered
  smaps   PID [--top N]                        largest mappings of a process by RSS (from /proc/PID/smaps)
  trace   PID [--seconds S]                    strace -c -f summary of a process's system calls for S seconds
Overhead: ~30 MB RSS, well under 1% of one core at 2 s.
"""
import os, sys, time, json, argparse, subprocess, re, logging, logging.handlers, traceback
import psutil

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
HERE = os.path.dirname(os.path.abspath(__file__))
SCRATCH = os.environ.get("PROCMON_LOGDIR", os.path.dirname(HERE))
MB = 1 << 20
DEFAULT_FOLLOW = [os.path.join(SCRATCH, f) for f in ("build_refl.log", "build_t1z.log", "build_t1z_main.log",
                                                      "build_final.log")]

# ----------------------------------------------------------------------------------------------------- logging setup
def setup_logging(d, console=False):
    fmt = logging.Formatter("%(asctime)s.%(msecs)03d %(levelname)-7s %(name)-15s %(message)s", "%Y-%m-%d %H:%M:%S")
    root = logging.getLogger("procmon"); root.setLevel(logging.DEBUG); root.handlers.clear()
    h1 = logging.handlers.RotatingFileHandler(os.path.join(d, "procmon.debug.log"), maxBytes=20 * MB, backupCount=5)
    h1.setLevel(logging.DEBUG); h1.setFormatter(fmt); root.addHandler(h1)
    h2 = logging.FileHandler(os.path.join(d, "procmon.log")); h2.setLevel(logging.INFO); h2.setFormatter(fmt)
    root.addHandler(h2)
    if console:
        h3 = logging.StreamHandler(sys.stderr); h3.setLevel(logging.INFO); h3.setFormatter(fmt); root.addHandler(h3)
    return root

def kv(**kw):
    out = []
    for k, v in kw.items():
        if v is None: continue
        if isinstance(v, float): v = f"{v:.1f}"
        v = str(v)
        if " " in v or "=" in v or '"' in v: v = '"' + v.replace('"', "'") + '"'
        out.append(f"{k}={v}")
    return " ".join(out)

# ----------------------------------------------------------------------------------------------------- readers
def read_kv(path):
    d = {}
    try:
        for line in open(path):
            p = line.split()
            if len(p) >= 2:
                try: d[p[0].rstrip(":")] = int(p[1])
                except ValueError: pass
    except OSError: pass
    return d

def cg_stats():
    st = read_kv(os.path.join(CG, "memory.stat"))
    def one(f):
        try: return int(open(os.path.join(CG, f)).read())
        except (OSError, ValueError): return 0
    oom = read_kv(os.path.join(CG, "memory.oom_control"))
    try: pids = [int(x) for x in open(os.path.join(CG, "cgroup.procs")).read().split()]
    except OSError: pids = []
    return {"limit": one("memory.limit_in_bytes") // MB, "usage": one("memory.usage_in_bytes") // MB,
            "max_usage": one("memory.max_usage_in_bytes") // MB, "failcnt": one("memory.failcnt"),
            "anon": st.get("total_rss", 0) // MB, "mapped": st.get("total_mapped_file", 0) // MB,
            "cache": st.get("total_cache", 0) // MB, "active_anon": st.get("total_active_anon", 0) // MB,
            "inactive_anon": st.get("total_inactive_anon", 0) // MB,
            "active_file": st.get("total_active_file", 0) // MB,
            "inactive_file": st.get("total_inactive_file", 0) // MB,
            "pgfault": st.get("total_pgfault", 0), "pgmajfault": st.get("total_pgmajfault", 0),
            "oom_kill": oom.get("oom_kill", 0), "under_oom": oom.get("under_oom", 0), "pids": pids}

def psi(name):
    try:
        line = open(f"/proc/pressure/{name}").readline().split()
        return float(line[1].split("=")[1])           # some avg10
    except (OSError, IndexError, ValueError):
        return None

def vmstat():
    v = read_kv("/proc/vmstat")
    return {k: v.get(k, 0) for k in ("pgmajfault", "pgscan_kswapd", "pgscan_direct", "pgsteal_kswapd",
                                     "pgsteal_direct", "workingset_refault_file", "workingset_refault",
                                     "oom_kill")}

def smaps_rollup(pid):
    d = read_kv(f"/proc/{pid}/smaps_rollup")
    return {k: d.get(k, 0) // 1024 for k in ("Rss", "Pss", "Pss_Anon", "Pss_File", "Shared_Clean", "Private_Clean",
                                              "Private_Dirty", "Anonymous", "Swap")}

def stat_faults(pid):
    try:
        f = open(f"/proc/{pid}/stat").read()
        rest = f[f.rindex(")") + 2:].split()
        return int(rest[7]), int(rest[9])              # minflt, majflt
    except (OSError, ValueError, IndexError):
        return 0, 0

def lean_target(cmd):
    if not cmd or not os.path.basename(cmd[0]).startswith("lean"): return None
    for a in cmd:
        if a.endswith(".lean"): return a.split("jacobian_lean/")[-1]
    return None

def proc_info(p, detail):
    try:
        with p.oneshot():
            cmd = p.cmdline(); mi = p.memory_info(); ct = p.cpu_times()
            r = {"pid": p.pid, "ppid": p.ppid(), "name": p.name(), "state": p.status(),
                 "create": p.create_time(), "cmd": " ".join(cmd), "lean": lean_target(cmd),
                 "rss": mi.rss // MB, "vms": mi.vms // MB, "shared": mi.shared // MB,
                 "anon": (mi.rss - mi.shared) // MB, "cpu": ct.user + ct.system, "thr": p.num_threads()}
            try: r["fds"] = p.num_fds()
            except psutil.Error: pass
            try:
                cs = p.num_ctx_switches(); r["vcsw"], r["ivcsw"] = cs.voluntary, cs.involuntary
            except psutil.Error: pass
            try:
                io = p.io_counters(); r["rd"], r["wr"] = io.read_bytes, io.write_bytes
            except psutil.Error: pass
        r["minflt"], r["majflt"] = stat_faults(p.pid)
        if detail and r["rss"] >= 100:
            r["smaps"] = smaps_rollup(p.pid)
        return r
    except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
        return None

def dmesg_lines():
    try:
        return subprocess.run(["dmesg"], capture_output=True, text=True, timeout=10).stdout.splitlines()
    except Exception as e:
        return [f"(dmesg unavailable: {e})"]

# ----------------------------------------------------------------------------------------------------- daemon
class Follower:
    def __init__(self, path):
        self.path, self.pos = path, None
    def poll(self):
        try:
            size = os.path.getsize(self.path)
        except OSError:
            return []
        if self.pos is None or size < self.pos: self.pos = size if self.pos is None else 0
        if size == self.pos: return []
        with open(self.path, errors="replace") as f:
            f.seek(self.pos); data = f.read(); self.pos = f.tell()
        return [l for l in data.splitlines() if l.strip()]

def run(args):
    log = setup_logging(args.dir)
    L = {k: logging.getLogger("procmon." + k) for k in ("sample", "proc", "cgroup", "system", "build", "kernel",
                                                          "self", "event")}
    jl = open(os.path.join(args.dir, "procmon.jsonl"), "a", buffering=1)
    follow = [Follower(f) for f in (args.follow or DEFAULT_FOLLOW)]
    L["event"].info(kv(msg="procmon v2 start", pid=os.getpid(), interval=args.interval, verbose=args.verbose,
                       follow=",".join(os.path.basename(f.path) for f in follow), cgroup=CG.split("/")[-1]))
    prev_p, peaks, prev_cg, prev_vm, prev_t = {}, {}, None, vmstat(), time.time()
    dmesg_n = len(dmesg_lines()); lowwarn = False; n = 0; dstate = {}
    psutil.cpu_percent(percpu=True)
    while True:
        t_start = time.time()
        try:
            dt = max(1e-3, t_start - prev_t); prev_t = t_start
            cg = cg_stats(); vm = vmstat()
            sysd = {"load1": os.getloadavg()[0], "cpu": psutil.cpu_percent(percpu=True),
                    "memavail": psutil.virtual_memory().available // MB,
                    "psi_mem": psi("memory"), "psi_cpu": psi("cpu"), "psi_io": psi("io")}
            rates = {k: (vm[k] - prev_vm[k]) / dt for k in vm}; prev_vm = vm
            procs = []
            for pid in cg["pids"]:
                try: r = proc_info(psutil.Process(pid), detail=True)
                except psutil.NoSuchProcess: r = None
                if r: procs.append(r)
            # ------------------------------------------------ cgroup + system lines
            fail_rate = (cg["failcnt"] - prev_cg["failcnt"]) / dt if prev_cg else 0
            majf_rate = (cg["pgmajfault"] - prev_cg["pgmajfault"]) / dt if prev_cg else 0
            head = cg["limit"] - cg["anon"]
            L["cgroup"].debug(kv(anon=cg["anon"], mapped=cg["mapped"], cache=cg["cache"], usage=cg["usage"],
                                 limit=cg["limit"], headroom_anon=head, active_anon=cg["active_anon"],
                                 inactive_anon=cg["inactive_anon"], active_file=cg["active_file"],
                                 inactive_file=cg["inactive_file"], failcnt_per_s=round(fail_rate),
                                 majflt_per_s=round(majf_rate), oom_kill=cg["oom_kill"], under_oom=cg["under_oom"],
                                 nproc=len(cg["pids"])))
            L["system"].debug(kv(load1=round(sysd["load1"], 2), cpu="/".join(f"{c:.0f}" for c in sysd["cpu"]),
                                 memavail=sysd["memavail"], psi_mem=sysd["psi_mem"], psi_cpu=sysd["psi_cpu"],
                                 psi_io=sysd["psi_io"], pgmajfault_s=round(rates["pgmajfault"]),
                                 refault_file_s=round(rates.get("workingset_refault_file", 0)),
                                 pgscan_s=round(rates["pgscan_kswapd"] + rates["pgscan_direct"]),
                                 pgsteal_s=round(rates["pgsteal_kswapd"] + rates["pgsteal_direct"])))
            # ------------------------------------------------ per-process lines, deltas, peaks
            now = {}
            for r in procs:
                pv = prev_p.get(r["pid"])
                r["cpu_pct"] = 100 * (r["cpu"] - pv["cpu"]) / dt if pv else None
                r["majflt_s"] = (r["majflt"] - pv["majflt"]) / dt if pv else None
                r["minflt_s"] = (r["minflt"] - pv["minflt"]) / dt if pv else None
                r["rd_s"] = (r.get("rd", 0) - pv.get("rd", 0)) / dt / MB if pv else None
                r["wr_s"] = (r.get("wr", 0) - pv.get("wr", 0)) / dt / MB if pv else None
                r["csw_s"] = ((r.get("vcsw", 0) + r.get("ivcsw", 0)) - (pv.get("vcsw", 0) + pv.get("ivcsw", 0))) / dt \
                    if pv else None
                sm = r.get("smaps", {})
                if args.verbose or r["rss"] >= 20 or r["lean"]:
                    L["proc"].debug(kv(pid=r["pid"], ppid=r["ppid"], name=r["name"], state=r["state"],
                                       cpu_pct=r["cpu_pct"], rss=r["rss"], anon=r["anon"], file=r["shared"],
                                       pss=sm.get("Pss"), pss_anon=sm.get("Pss_Anon"), pss_file=sm.get("Pss_File"),
                                       priv_dirty=sm.get("Private_Dirty"), vms=r["vms"], thr=r["thr"],
                                       fds=r.get("fds"), minflt_s=r["minflt_s"], majflt_s=r["majflt_s"],
                                       rd_mb_s=r["rd_s"], wr_mb_s=r["wr_s"], csw_s=r["csw_s"],
                                       lean=r["lean"], cmd=(r["cmd"] if args.verbose else (None if r["lean"] else r["cmd"][:140]))))
                pk = peaks.get(r["pid"])
                if pk is None:
                    pk = peaks[r["pid"]] = {"rss": 0, "anon": 0, "pss": 0, "cpu": 0, "lean": r["lean"],
                                            "name": r["name"], "t0": r["create"], "majflt0": r["majflt"],
                                            "cmd": r["cmd"]}
                    if r["rss"] >= 50 or r["lean"]:
                        L["event"].info(kv(msg="start", pid=r["pid"], ppid=r["ppid"], name=r["name"],
                                           lean=r["lean"], cmd=(None if r["lean"] else r["cmd"][:160])))
                pk["rss"] = max(pk["rss"], r["rss"]); pk["anon"] = max(pk["anon"], r["anon"])
                pk["pss"] = max(pk["pss"], sm.get("Pss", 0)); pk["cpu"] = r["cpu"]; pk["majflt"] = r["majflt"]
                # D state (uninterruptible, usually I/O on evicted pages) and zombies
                if r["state"] in ("disk-sleep", "zombie"):
                    dstate[r["pid"]] = dstate.get(r["pid"], 0) + 1
                    if dstate[r["pid"]] == 5:
                        L["event"].warning(kv(msg=f"process in state {r['state']} for 5 samples", pid=r["pid"],
                                              name=r["name"], lean=r["lean"]))
                else:
                    dstate.pop(r["pid"], None)
                if r["majflt_s"] and r["majflt_s"] > 500:
                    pk["storm"] = pk.get("storm", 0) + 1
                    age = time.time() - r["create"]
                    if age < 30:              # a new process mapping .olean files that the page cache had dropped
                        if pk["storm"] == 1:
                            L["event"].info(kv(msg="startup refault burst (olean pages re-read from disk)",
                                               pid=r["pid"], lean=r["lean"] or r["name"],
                                               majflt_s=round(r["majflt_s"]), cg_mapped=cg["mapped"]))
                    elif pk["storm"] == 3:
                        pressured = (cg["limit"] - cg["anon"] < 1500) or fail_rate > 1000
                        if pressured:          # the working set does not fit next to the anonymous memory: thrashing
                            L["event"].warning(kv(msg="sustained major faults under memory pressure (thrashing)",
                                                  pid=r["pid"], lean=r["lean"] or r["name"],
                                                  majflt_s=round(r["majflt_s"]), age_s=round(age), cg_anon=cg["anon"],
                                                  cg_mapped=cg["mapped"], failcnt_per_s=round(fail_rate)))
                        else:                  # plenty of headroom: cold page cache (first read of .olean files)
                            L["event"].info(kv(msg="sustained major faults without memory pressure (cold cache, I/O bound)",
                                               pid=r["pid"], lean=r["lean"] or r["name"],
                                               majflt_s=round(r["majflt_s"]), age_s=round(age), cg_anon=cg["anon"]))
                else:
                    pk["storm"] = 0
                if r["lean"] and time.time() - r["create"] > args.long and not pk.get("longwarn"):
                    pk["longwarn"] = True
                    L["event"].warning(kv(msg=f"lean module running > {args.long}s", pid=r["pid"], lean=r["lean"],
                                          rss=r["rss"], anon=r["anon"], cpu_s=round(r["cpu"])))
                now[r["pid"]] = r
            for pid in list(prev_p):
                if pid not in now:
                    pk = peaks.pop(pid, None)
                    if pk and (pk["rss"] >= 50 or pk["lean"]):
                        L["event"].info(kv(msg="exit", pid=pid, name=pk["name"], lean=pk["lean"],
                                           secs=round(time.time() - pk["t0"]), peak_rss=pk["rss"],
                                           peak_anon=pk["anon"], peak_pss=pk["pss"], cpu_s=round(pk["cpu"]),
                                           majflt=pk.get("majflt", 0) - pk["majflt0"],
                                           cmd=(None if pk["lean"] else pk["cmd"][:120])))
            prev_p = now
            # ------------------------------------------------ cgroup-level warnings and OOM
            if head < args.warn and not lowwarn:
                top = sorted(procs, key=lambda p: -p["anon"])[:3]
                L["event"].warning(kv(msg="low anon headroom", headroom=head, anon=cg["anon"], limit=cg["limit"],
                                      top=";".join(f"{p['pid']}:{p['lean'] or p['name']}:{p['anon']}MB" for p in top)))
                lowwarn = True
            elif head >= args.warn + 300:
                lowwarn = False
            if prev_cg and fail_rate > 50000:
                L["event"].warning(kv(msg="memory-pressure burst (limit hits; page cache being reclaimed)",
                                      failcnt_per_s=round(fail_rate), usage=cg["usage"], anon=cg["anon"],
                                      mapped=cg["mapped"], majflt_per_s=round(majf_rate)))
            if prev_cg and cg["oom_kill"] > prev_cg["oom_kill"]:
                lines = dmesg_lines(); new = lines[dmesg_n:]; dmesg_n = len(lines)
                L["event"].error(kv(msg="OOM kill in the cgroup", oom_kill_before=prev_cg["oom_kill"],
                                    oom_kill_after=cg["oom_kill"], anon=cg["anon"]))
                for l in [x for x in new if "oom" in x.lower() or "Killed process" in x][-6:]:
                    L["kernel"].error(l.strip())
            prev_cg = cg
            # ------------------------------------------------ followed build logs
            for f in follow:
                for line in f.poll():
                    tag = os.path.basename(f.path)
                    if "FAILED" in line or re.search(r"\berror\b", line, re.I):
                        L["build"].error(kv(file=tag, line=line[:300]))
                    elif re.search(r"\bbuilt\b|ALL .* OK|exit 0", line):
                        L["build"].info(kv(file=tag, line=line[:300]))
                    else:
                        L["build"].debug(kv(file=tag, line=line[:300]))
            # ------------------------------------------------ kernel lines (every 15 samples)
            if n % 15 == 0:
                lines = dmesg_lines()
                for l in lines[dmesg_n:]:
                    (L["kernel"].error if re.search(r"oom|killed process|segfault", l, re.I) else L["kernel"].debug)(l.strip())
                dmesg_n = len(lines)
            # ------------------------------------------------ structured record
            jl.write(json.dumps({"t": round(t_start, 2), "cg": {k: v for k, v in cg.items() if k != "pids"},
                                 "sys": sysd, "rates": {k: round(v, 1) for k, v in rates.items()},
                                 "procs": [{k: (round(v, 2) if isinstance(v, float) else v) for k, v in r.items()
                                            if k not in ("cmd",)} | {"cmd": r["cmd"][:200]}
                                           for r in procs if r["rss"] >= 20 or r["lean"]]}) + "\n")
            n += 1
            if n % 30 == 0:
                me = psutil.Process()
                L["self"].debug(kv(rss=me.memory_info().rss // MB, cpu_s=round(sum(me.cpu_times()[:2]), 1),
                                   sample_ms=round(1000 * (time.time() - t_start), 1), samples=n))
        except Exception:
            logging.getLogger("procmon.self").critical("sample failed: " + traceback.format_exc().replace("\n", " | "))
        time.sleep(max(0.2, args.interval - (time.time() - t_start)))

# ----------------------------------------------------------------------------------------------------- queries
def load(args):
    path = os.path.join(args.dir, "procmon.jsonl")
    if not os.path.exists(path): sys.exit("no samples yet: start `procmon.py run`")
    t_min = time.time() - args.since * 60 if args.since else 0
    out = []
    for line in open(path):
        try: s = json.loads(line)
        except Exception: continue
        if s["t"] >= t_min and "cg" in s: out.append(s)
    return out

def fmt_now(args):
    cg = cg_stats(); vm = vmstat()
    procs = [r for r in (proc_info(psutil.Process(p), True) for p in cg["pids"] if psutil.pid_exists(p)) if r]
    print(f"cgroup: anon {cg['anon']} MB + mapped {cg['mapped']} MB (cache {cg['cache']}) / limit {cg['limit']} MB;"
          f" anon headroom {cg['limit'] - cg['anon']} MB; max_usage {cg['max_usage']} MB; oom_kill {cg['oom_kill']};"
          f" failcnt {cg['failcnt']}; pgmajfault {cg['pgmajfault']}")
    print(f"system: load {os.getloadavg()[0]:.2f}; MemAvailable {psutil.virtual_memory().available // MB} MB;"
          f" PSI mem {psi('memory')} cpu {psi('cpu')} io {psi('io')}")
    print(f"{'pid':>7} {'st':>4} {'rss':>6} {'anon':>6} {'file':>6} {'pss':>6} {'pdirty':>6} {'majflt':>7} "
          f"{'cpu_s':>7} {'age':>6} {'thr':>4}  what")
    for p in sorted(procs, key=lambda p: -p["rss"]):
        if p["rss"] < 20 and not args.verbose: continue
        sm = p.get("smaps", {})
        print(f"{p['pid']:>7} {p['state'][:4]:>4} {p['rss']:>6} {p['anon']:>6} {p['shared']:>6} {sm.get('Pss', ''):>6} "
              f"{sm.get('Private_Dirty', ''):>6} {p['majflt']:>7} {p['cpu']:>7.0f} {time.time() - p['create']:>6.0f} "
              f"{p['thr']:>4}  {p['lean'] or p['cmd'][:80]}")
        if args.verbose and sm:
            print("        smaps_rollup MB: " + " ".join(f"{k}={v}" for k, v in sm.items()))

def tree(args):
    cg = cg_stats(); ps = {}
    for pid in cg["pids"]:
        try: ps[pid] = psutil.Process(pid)
        except psutil.NoSuchProcess: pass
    kids = {}
    for pid, p in ps.items():
        try: kids.setdefault(p.ppid() if p.ppid() in ps else None, []).append(pid)
        except psutil.NoSuchProcess: pass
    def show(pid, depth):
        p = ps[pid]
        try:
            mi = p.memory_info()
            print(f"{'  ' * depth}{pid} [{p.status()[:4]}] rss {mi.rss // MB} anon {(mi.rss - mi.shared) // MB}  "
                  f"{(lean_target(p.cmdline()) or ' '.join(p.cmdline()))[:110]}")
        except psutil.NoSuchProcess: return
        for c in sorted(kids.get(pid, [])): show(c, depth + 1)
    for r in sorted(kids.get(None, [])): show(r, 0)

def modules_table(S):
    mods = {}
    for s in S:
        for p in s["procs"]:
            if not p.get("lean"): continue
            m = mods.setdefault((p["lean"], p["pid"]), {"t0": s["t"], "t1": s["t"], "rss": 0, "anon": 0, "pss": 0,
                                                         "cpu": 0, "maj0": p.get("majflt", 0), "maj": 0})
            m["t1"] = s["t"]; m["rss"] = max(m["rss"], p["rss"]); m["anon"] = max(m["anon"], p["anon"])
            m["pss"] = max(m["pss"], p.get("smaps", {}).get("Pss", 0)); m["cpu"] = max(m["cpu"], p["cpu"])
            m["maj"] = p.get("majflt", 0) - m["maj0"]
    return mods

def report(args):
    S = load(args)
    if not S: print("no samples in range"); return
    cgs = [s["cg"] for s in S]
    lo = min(cgs, key=lambda c: c["limit"] - c["anon"])
    print(f"{len(S)} samples over {(S[-1]['t'] - S[0]['t']) / 60:.1f} min; min anon headroom {lo['limit'] - lo['anon']} MB"
          f" (anon {lo['anon']} MB); peak anon {max(c['anon'] for c in cgs)} MB; peak anon+mapped "
          f"{max(c['anon'] + c['mapped'] for c in cgs)} MB; oom_kill {cgs[0]['oom_kill']} -> {cgs[-1]['oom_kill']}; "
          f"failcnt +{cgs[-1]['failcnt'] - cgs[0]['failcnt']}; pgmajfault +{cgs[-1].get('pgmajfault', 0) - cgs[0].get('pgmajfault', 0)}")
    mods = modules_table(S)
    print(f"largest Lean processes by anon peak ({len(mods)} seen):")
    for (f, pid), m in sorted(mods.items(), key=lambda kv_: -kv_[1]["anon"])[:args.top]:
        print(f"  anon {m['anon']:>5}  rss {m['rss']:>5}  pss {m['pss']:>5}  {m['t1'] - m['t0']:>5.0f}s  majflt {m['maj']:>6}  {f}")
    evp = os.path.join(args.dir, "procmon.log")
    if os.path.exists(evp):
        bad = [l.rstrip() for l in open(evp) if re.search(r" (WARNING|ERROR|CRITICAL) ", l)]
        print(f"WARNING/ERROR/CRITICAL events (all time): {len(bad)}")
        for l in bad[-args.top:]: print("  " + l[:240])

def tail(args):
    p = os.path.join(args.dir, "procmon.debug.log" if args.debug else "procmon.log")
    if not os.path.exists(p): print("no log yet"); return
    order = {"DEBUG": 10, "INFO": 20, "WARNING": 30, "ERROR": 40, "CRITICAL": 50}
    lvl = order.get(args.level.upper(), 0) if args.level else 0
    out = []
    for l in open(p, errors="replace"):
        m = re.match(r"\S+ \S+ (\w+)", l)
        if m and order.get(m.group(1), 0) < lvl: continue
        if args.grep and not re.search(args.grep, l): continue
        out.append(l.rstrip())
    print("\n".join(x[:300] for x in out[-args.n:]))

def smaps(args):
    cur, rows = None, []
    for line in open(f"/proc/{args.pid}/smaps"):
        if re.match(r"^[0-9a-f]+-[0-9a-f]+ ", line):
            parts = line.split(); cur = {"name": parts[5] if len(parts) > 5 else "[anon]", "rss": 0, "anon": 0}
            rows.append(cur)
        elif line.startswith("Rss:"): cur["rss"] = int(line.split()[1]) // 1024
        elif line.startswith("Anonymous:"): cur["anon"] = int(line.split()[1]) // 1024
    agg = {}
    for r in rows:
        a = agg.setdefault(r["name"], [0, 0, 0]); a[0] += r["rss"]; a[1] += r["anon"]; a[2] += 1
    print(f"{'rss':>7} {'anon':>7} {'maps':>5}  mapping")
    for name, (rss, anon, k) in sorted(agg.items(), key=lambda kv_: -kv_[1][0])[:args.top]:
        print(f"{rss:>7} {anon:>7} {k:>5}  {name.split('jacobian_lean/')[-1][-100:]}")

def trace(args):
    print(f"strace -c -f -p {args.pid} for {args.seconds}s ...", flush=True)
    r = subprocess.run(["timeout", "-s", "INT", str(args.seconds), "strace", "-c", "-f", "-p", str(args.pid)],
                       capture_output=True, text=True)
    print(r.stderr[-4000:])
    logging.getLogger("procmon.trace").debug(kv(pid=args.pid, seconds=args.seconds, summary=r.stderr[-800:]))

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("cmd", choices=["run", "now", "tree", "report", "modules", "tail", "smaps", "trace"])
    ap.add_argument("n", nargs="?", type=int, default=30, help="tail: lines; smaps/trace: pid")
    ap.add_argument("--interval", type=float, default=2.0)
    ap.add_argument("--dir", default=HERE)
    ap.add_argument("--follow", nargs="*")
    ap.add_argument("--since", type=float, default=0)
    ap.add_argument("--warn", type=int, default=800, help="anon headroom warning threshold, MB")
    ap.add_argument("--long", type=int, default=900, help="warn when a lean module runs longer than this, s")
    ap.add_argument("--top", type=int, default=12)
    ap.add_argument("--level"); ap.add_argument("--grep"); ap.add_argument("--debug", action="store_true")
    ap.add_argument("--verbose", action="store_true", help="run: log every process each sample, with full command lines; now: smaps split")
    ap.add_argument("--seconds", type=int, default=10)
    a = ap.parse_args()
    if a.cmd in ("smaps", "trace"): a.pid = a.n
    if a.cmd != "run": setup_logging(a.dir)
    {"run": run, "now": fmt_now, "tree": tree, "report": report, "tail": tail, "smaps": smaps, "trace": trace,
     "modules": lambda a_: [print(f"{time.strftime('%H:%M:%S', time.localtime(m['t0']))} {m['t1'] - m['t0']:>5.0f}s "
                                  f"rss {m['rss']:>5} anon {m['anon']:>5} pss {m['pss']:>5} cpu {m['cpu']:>6.0f}s "
                                  f"majflt {m['maj']:>6}  {f}")
                            for (f, pid), m in sorted(modules_table(load(a_)).items(), key=lambda kv_: kv_[1]["t0"])]
     }[a.cmd](a)

if __name__ == "__main__":
    try:
        main()
    except BrokenPipeError:
        pass
