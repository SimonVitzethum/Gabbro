#!/usr/bin/env python3
"""A `lean` front that keeps a build inside the owner's RAM rules (AGENTS.md, "RAM discipline").

`instrumente/pruefe-lean.py` hands this file to Lake as its `lean` (fake sysroot, `LAKE_OVERRIDE_LEAN=1`) and to
`lake env` for the direct checks. Lake has no job limit (Lake 5.0.0 has no `-j`, no jobs option, no environment
variable for it), so the limit is set where Lake runs the compiler: before a `lean` that compiles a file starts,
it takes a private lock (concurrency), then one of the shared slot locks (global concurrency with the other
workers), waits until enough memory is available, and runs `lean` inside a no-swap `systemd-run` scope.
Calls that only query (`--githash`, `--version`, `--print-prefix`, ...) go straight to the real `lean`.

Environment (set by the guardian):
  GABBRO_LEAN_ECHT     the real `lean` binary (required)
  GABBRO_LEAN_PRIVAT   `:`-separated private lock files; the call takes any free one (their count is the
                       number of `lean` processes that may run at once in this guardian run)
  GABBRO_LEAN_SLOTS    `:`-separated shared slot lock files; the call takes any free one while it runs
                       (empty when the guardian holds the slots itself)
  GABBRO_LEAN_ARGS     `streng`: drop `-j*`, `-M*`, `-DElab.async=*` and run `-j4 -DElab.async=true -M4608`
                       (the Stage-0 rule); `lake`: keep the arguments as Lake passes them
  GABBRO_LEAN_MAX      MemoryMax of the scope in GiB (default 5), GABBRO_LEAN_HOCH its MemoryHigh (default 4)
  GABBRO_LEAN_MIN      GiB of MemAvailable required before a start (default 8)
  GABBRO_LEAN_FRIST    seconds to wait for lock and memory before giving up with exit 75 (default 14400)
"""
import fcntl, os, signal, subprocess, sys, time

ABFRAGEN = ("--githash", "--version", "-v", "--print-prefix", "--print-libdir", "--help", "-h", "--stdin",
            "--deps", "--deps-json", "--short-version", "--features")


def verfuegbar_gib():
    for z in open("/proc/meminfo"):
        if z.startswith("MemAvailable:"):
            return int(z.split()[1]) / 1024 / 1024
    return 0.0


class _Alarm(Exception):
    pass


def _bei_alarm(signum, frame):
    raise _Alarm()


def nimm(dateien, ende):
    """Take any free lock of `dateien`; the open file keeps it until exit. A free lock is taken at once; otherwise
    the call queues with a BLOCKING `flock` (the other workers queue that way, polling would starve against them),
    on another file each round, and looks at all of them again every 30 s."""
    signal.signal(signal.SIGALRM, _bei_alarm)
    runde = 0
    while True:
        for d in dateien:
            fd = os.open(d, os.O_RDWR | os.O_CREAT, 0o666)
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                return fd
            except OSError:
                os.close(fd)
        if time.time() > ende:
            return None
        fd = os.open(dateien[(os.getpid() + runde) % len(dateien)], os.O_RDWR | os.O_CREAT, 0o666)
        signal.alarm(30)
        try:
            fcntl.flock(fd, fcntl.LOCK_EX)
            signal.alarm(0)
            return fd
        except _Alarm:
            os.close(fd)
        runde += 1


def main():
    echt = os.environ["GABBRO_LEAN_ECHT"]
    args = sys.argv[1:]
    if not any(a.endswith(".lean") for a in args) or any(a in ABFRAGEN for a in args):
        os.execv(echt, [echt, *args])
    frist = float(os.environ.get("GABBRO_LEAN_FRIST", "14400"))
    ende = time.time() + frist
    privat = [p for p in os.environ.get("GABBRO_LEAN_PRIVAT", "").split(":") if p]
    slots = [p for p in os.environ.get("GABBRO_LEAN_SLOTS", "").split(":") if p]
    halte = []
    for satz in (privat, slots):
        if satz:
            fd = nimm(satz, ende)
            if fd is None:
                print("lean-seriell: no lock free in time -- NOT MEASURED", file=sys.stderr)
                return 75
            halte.append(fd)
    mind = float(os.environ.get("GABBRO_LEAN_MIN", "8"))
    while verfuegbar_gib() < mind:
        if time.time() > ende:
            print(f"lean-seriell: under {mind} GiB available memory for too long -- NOT MEASURED", file=sys.stderr)
            return 75
        time.sleep(10)
    if os.environ.get("GABBRO_LEAN_ARGS", "streng") == "streng":
        args = [a for a in args if not (a.startswith("-j") or a.startswith("-M") or a.startswith("-DElab.async="))]
        args = ["-j4", "-DElab.async=true", "-M4608", *args]
    mx = os.environ.get("GABBRO_LEAN_MAX", "5")
    hoch = os.environ.get("GABBRO_LEAN_HOCH", "4")
    cmd = ["systemd-run", "--user", "--scope", "-q", "-p", f"MemoryHigh={hoch}G", "-p", f"MemoryMax={mx}G",
           "-p", "MemorySwapMax=0", echt, *args]
    return subprocess.run(cmd).returncode


if __name__ == "__main__":
    sys.exit(main())
