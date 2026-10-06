"""timed.py -- run a command with its output sent to a log file; print one summary line: exit status, wall time,
CPU time (user + system) and the peak resident memory of the largest child process.
usage: python3 timed.py LABEL LOGFILE cmd ...        (Linux: ru_maxrss is in KB)"""
import sys, time, subprocess, resource

label, logfile, cmd = sys.argv[1], sys.argv[2], sys.argv[3:]
t0 = time.time()
with open(logfile, "w") as fh:
    rc = subprocess.call(cmd, stdout=fh, stderr=subprocess.STDOUT)
wall = time.time() - t0
ru = resource.getrusage(resource.RUSAGE_CHILDREN)
line = (f"{label}: exit {rc}, wall {wall:.1f} s, cpu {ru.ru_utime + ru.ru_stime:.1f} s, "
        f"max RSS {ru.ru_maxrss // 1024} MB")
with open(logfile, "a") as fh:
    fh.write(line + "\n")
print(line, flush=True)
sys.exit(rc)
