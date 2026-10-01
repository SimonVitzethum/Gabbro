#!/usr/bin/env python3
"""Automatic OpenCode coordinator failover supervisor (lane 620).

Portable standard-library supervisor. The foreground coordinator owns the
role and renews its heartbeat lease; this background supervisor never renews
it. After the lease expires it starts exactly one identified managed Muse
fallback coordinator in a shared model slot. See dokumente/x86/COORDINATOR-FAILOVER.md.
"""
import argparse
import datetime
import fcntl
import json
import os
import sys
import time
import uuid
from pathlib import Path

SLOT_COUNT = 15
AUTHORISATION = (
    "Simon: automatic OpenCode takeover if the foreground coordinator "
    "no longer responds (coordinator role only, guarded publication)"
)


def parse_args(argv=None):
    p = argparse.ArgumentParser(description="Coordinator failover supervisor.")
    p.add_argument("action", choices=["supervise", "heartbeat"])
    p.add_argument("--project-root", required=True)
    p.add_argument("--control-dir", required=True)
    p.add_argument("--pool-dir", required=True)
    p.add_argument("--coordinator", required=True)
    p.add_argument("--opencode", required=True)
    p.add_argument("--model", required=True)
    p.add_argument("--budget", type=float, default=43200.0)
    p.add_argument("--timeout-seconds", type=float, default=300.0)
    p.add_argument("--turn-seconds", type=float, default=7200.0)
    p.add_argument("--proc-root", default="/proc")
    p.add_argument("--prompt-file", default=None)
    p.add_argument("--poll-seconds", type=float, default=5.0)
    return p.parse_args(argv)


def now_iso():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def atomic_write_json(path, data):
    p = Path(path)
    if str(p.parent) not in ("", "."):
        p.parent.mkdir(parents=True, exist_ok=True)
    tmp = p.with_suffix(f".{os.getpid()}.tmp")
    tmp.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    tmp.replace(p)


def read_lease(control_dir):
    path = Path(control_dir) / "orchestrator-lease.json"
    try:
        return json.loads(path.read_text())
    except (FileNotFoundError, ValueError, OSError):
        return {}


def heartbeat_age_secs(lease):
    try:
        hb = datetime.datetime.fromisoformat(str(lease.get("heartbeat")))
    except (ValueError, TypeError):
        return float("inf")
    if hb.tzinfo is None:
        hb = hb.replace(tzinfo=datetime.timezone.utc)
    now = datetime.datetime.now(datetime.timezone.utc)
    return (now - hb).total_seconds()


def read_proc_parts(proc_root, pid):
    """Return (cmdline_parts, state, starttime) or None if the pid is gone."""
    try:
        raw = Path(proc_root, str(pid), "cmdline").read_bytes()
    except (FileNotFoundError, NotADirectoryError):
        return None
    except (PermissionError, ProcessLookupError, OSError):
        return ([], "unknown", None)
    try:
        stat = Path(proc_root, str(pid), "stat").read_text()
    except (FileNotFoundError, NotADirectoryError):
        return None
    except (PermissionError, ProcessLookupError, OSError):
        stat = ""
    state, starttime = None, None
    if stat:
        try:
            after = stat.rsplit(")", 1)[1].split()
            state = after[0]
            starttime = after[19]
        except (IndexError, ValueError):
            pass
    parts = [x.decode(errors="replace") for x in raw.split(b"\x00") if x]
    return (parts, state, starttime)


def identify_model(pid, proc_root, opencode_marker, model_marker, expected_start=None):
    """Identify a live managed fallback model pid, else None.

    Checks the process start time against the lease so a reused pid is never
    mistaken for the fallback. Zombie/dead states (Z/X) never count. Never
    returns or logs the cmdline itself.
    """
    if pid is None:
        return None
    try:
        pid_int = int(pid)
    except (ValueError, TypeError):
        return None
    info = read_proc_parts(proc_root, pid_int)
    if info is None:
        return None
    parts, state, starttime = info
    if state in ("Z", "X"):
        return None
    if state == "unknown":
        return None
    blob = "\x00".join(parts)
    if opencode_marker not in blob or model_marker not in blob:
        return None
    if expected_start is not None and starttime is not None:
        if str(expected_start) != str(starttime):
            return None
    return {"pid": pid_int, "starttime": starttime}


def get_start_time(pid, proc_root):
    info = read_proc_parts(proc_root, pid)
    if info is None:
        return None
    return info[2]


def is_paused(control_dir):
    for name in ("pool-paused.json", "coordinator-pause.json"):
        try:
            if (Path(control_dir) / name).is_file():
                return True, name
        except OSError:
            continue
    return False, None


def return_requested(control_dir):
    try:
        return (Path(control_dir) / "return-to-codex.json").is_file()
    except OSError:
        return False


def git_clean(project_root):
    """True only if git reports a clean tree and no merge is in progress."""
    import subprocess
    try:
        out = subprocess.run(
            ["git", "-C", str(project_root), "status", "--porcelain"],
            text=True, capture_output=True, timeout=60)
    except (OSError, ValueError):
        return False
    if out.returncode != 0:
        return False
    if out.stdout.strip():
        return False
    try:
        if (Path(project_root) / ".git" / "MERGE_HEAD").exists():
            return False
    except OSError:
        return False
    return True


def lock_free(path):
    """Nonblocking probe: True if nobody holds an exclusive flock on path."""
    try:
        fh = open(path, "a")
    except OSError:
        return False
    try:
        fcntl.flock(fh, fcntl.LOCK_EX | fcntl.LOCK_NB)
        fcntl.flock(fh, fcntl.LOCK_UN)
        return True
    except (BlockingIOError, OSError):
        return False
    finally:
        fh.close()


def safe_boundary(control_dir, project_root):
    """Cooperative stop boundary: clean tree AND no active watcher/action.

    A clean git tree alone is NOT enough: an integration or publication step
    may hold the watch lock or the foreground action lock while the tree
    still looks clean. Both locks are probed nonblocking and released
    immediately; a held lock means 'not safe, keep the role running'.
    """
    if not git_clean(project_root):
        return False, "dirty_root"
    if not lock_free(Path(control_dir) / "watch.lock"):
        return False, "watch_busy"
    if not lock_free(Path(control_dir) / "foreground-action.lock"):
        return False, "action_busy"
    return True, "safe"


def run_heartbeat(args):
    """Foreground only: renew the codex lease, or request a safe handback."""
    if args.turn_seconds > 7200.0:
        print("error: --turn-seconds must be <= 7200", file=sys.stderr)
        return 3
    control = Path(args.control_dir)
    control.mkdir(parents=True, exist_ok=True)
    lock_path = control / "orchestrator-lease.lock"
    lease_path = control / "orchestrator-lease.json"
    with open(lock_path, "a") as guard:
        fcntl.flock(guard, fcntl.LOCK_EX)
        lease = read_lease(args.control_dir)
        if lease.get("owner") == "muse" and lease.get("model_pid"):
            found = identify_model(
                lease.get("model_pid"), args.proc_root,
                args.opencode, args.model,
                lease.get("model_start_time"))
            if found is not None:
                atomic_write_json(control / "return-to-codex.json", {
                    "requested": now_iso(),
                    "reason": "foreground coordinator returned; "
                              "finish current safe action and release role",
                })
                print("Fallback coordinator owns the role; "
                      "safe return requested. Do not mutate until released.")
                return 2
        lease = {
            "owner": "codex",
            "heartbeat": now_iso(),
            "timeout_seconds": float(args.timeout_seconds),
            "authorisation": AUTHORISATION,
        }
        atomic_write_json(lease_path, lease)
    print("Foreground coordinator heartbeat recorded.")
    return 0


def slot_path(pool_dir, slot):
    return Path(pool_dir) / "locks" / f"go-contributor-{slot:02d}"


def reserve_slot(pool_dir):
    """Reserve one shared model slot (1..15); return (slot, file_handle)."""
    lock_dir = Path(pool_dir) / "locks"
    lock_dir.mkdir(parents=True, exist_ok=True)
    for slot in range(1, SLOT_COUNT + 1):
        fh = open(slot_path(pool_dir, slot), "a")
        try:
            fcntl.flock(fh, fcntl.LOCK_EX | fcntl.LOCK_NB)
            return slot, fh
        except (BlockingIOError, OSError):
            fh.close()
    return None, None


def lock_slot(pool_dir, slot):
    """Re-acquire one specific slot after a supervisor restart."""
    fh = open(slot_path(pool_dir, slot), "a")
    try:
        fcntl.flock(fh, fcntl.LOCK_EX | fcntl.LOCK_NB)
        return fh
    except (BlockingIOError, OSError):
        fh.close()
        return None


GUARDIAN_MARKER = "gabbro-failover-slot-guardian"


def proc_pgrp(proc_root, pid):
    """Return the process-group id of pid, or None if gone/unreadable."""
    try:
        stat = Path(proc_root, str(int(pid)), "stat").read_text()
    except (FileNotFoundError, NotADirectoryError, ValueError, OSError):
        return None
    try:
        after = stat.rsplit(")", 1)[1].split()
        return int(after[2])
    except (IndexError, ValueError):
        return None


def group_members(pgid, proc_root, exclude=()):
    """List live pids whose process group is pgid (kernel /proc scan).

    Zombies and dead states never count as live members. Unreadable or
    gone pids are skipped. Excluded pids (supervisor, guardian) are not
    reported.
    """
    try:
        want = int(pgid)
    except (ValueError, TypeError):
        return []
    excluded = set()
    for pid in exclude:
        try:
            excluded.add(int(pid))
        except (ValueError, TypeError):
            continue
    members = []
    try:
        names = os.listdir(str(proc_root))
    except OSError:
        return []
    for name in names:
        if not name.isdigit():
            continue
        pid = int(name)
        if pid in excluded:
            continue
        try:
            stat = Path(proc_root, name, "stat").read_text()
        except (FileNotFoundError, NotADirectoryError, OSError):
            continue
        try:
            after = stat.rsplit(")", 1)[1].split()
            state = after[0]
            pgrp = int(after[2])
        except (IndexError, ValueError):
            continue
        if state in ("Z", "X"):
            continue
        if pgrp == want:
            members.append(pid)
    return sorted(members)


def wait_group_gone(pgid, proc_root, exclude=(), timeout=30.0,
                    poll=0.2):
    """True once no live member of pgid remains (excluding given pids)."""
    deadline = time.monotonic() + max(float(timeout), 0.0)
    while time.monotonic() < deadline:
        if not group_members(pgid, proc_root, exclude=exclude):
            return True
        time.sleep(poll)
    return not group_members(pgid, proc_root, exclude=exclude)


def guardian_code():
    """Python source for the slot-guardian child.

    The guardian inherits the SAME locked slot/role file descriptions
    via pass_fds, runs in its own session (never in the fallback group,
    so killpg on the fallback never signals it) and exits only after the
    fallback process group has no live member left. Any survivor holding
    the inherited description keeps the kernel slot/role lock until then,
    so a supervisor crash or budget exit cannot free the 15-slot
    accounting while fallback tools still run.
    """
    return (
        "import os,sys,time\n"
        "from pathlib import Path\n"
        "pgid=int(sys.argv[2]); root=sys.argv[3]\n"
        "guard=int(sys.argv[4]) if len(sys.argv)>4 else 0\n"
        "sup=int(sys.argv[5]) if len(sys.argv)>5 else 0\n"
        "while True:\n"
        " members=[]\n"
        " try:\n"
        "  names=os.listdir(root)\n"
        " except OSError:\n"
        "  break\n"
        " for n in names:\n"
        "  if not n.isdigit(): continue\n"
        "  p=int(n)\n"
        "  if p in (guard,sup,os.getpid()): continue\n"
        "  try:\n"
        "   s=Path(root,n,'stat').read_text()\n"
        "  except OSError:\n"
        "   continue\n"
        "  try:\n"
        "   a=s.rsplit(')',1)[1].split()\n"
        "   st=a[0]; g=int(a[2])\n"
        "  except (IndexError,ValueError):\n"
        "   continue\n"
        "  if st in ('Z','X'): continue\n"
        "  if g==pgid: members.append(p)\n"
        " if not members: break\n"
        " time.sleep(1.0)\n"
    )


def spawn_guardian(pgid, proc_root, slot_fh, role_fh=None):
    """Spawn the slot-guardian sharing the locked slot/role descriptions."""
    import subprocess
    marker = GUARDIAN_MARKER
    fds = []
    if slot_fh is not None:
        fds.append(slot_fh.fileno())
    if role_fh is not None and role_fh.fileno() not in fds:
        fds.append(role_fh.fileno())
    if not fds:
        return None
    try:
        proc = subprocess.Popen(
            [sys.executable, "-c", guardian_code(), marker,
             str(int(pgid)), str(proc_root),
             str(os.getpid()), str(os.getpid())],
            stdin=subprocess.DEVNULL,
            stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            start_new_session=True, close_fds=False,
            pass_fds=tuple(fds))
    except Exception:
        return None
    return proc


def guardian_alive(pid, proc_root, pgid=None):
    """True while the guardian process itself is live (marker cmdline)."""
    if pid is None:
        return False
    try:
        pid_int = int(pid)
    except (ValueError, TypeError):
        return False
    info = read_proc_parts(proc_root, pid_int)
    if info is None:
        return False
    parts, state, _ = info
    if state in ("Z", "X", "unknown"):
        return False
    blob = "\x00".join(parts)
    if GUARDIAN_MARKER not in blob:
        return False
    if pgid is not None and str(int(pgid)) not in blob:
        return False
    return True


def acquire_boundary(control_dir, timeout=60.0, poll=0.1):
    """Hold safe-boundary locks across termination (never probe-release).

    Acquires foreground-action.lock EX and then watch.lock EX, blocking
    (with timeout) while an integration, tool run or watcher step holds
    them. Both locks are HELD on success and must stay held through the
    fallback signal/wait/group-drain; the caller releases them only after
    the lease has been updated. Returns (action_fh, watch_fh) or
    (None, None) on timeout. The lease lock must NOT be held while
    calling this (foreground mutations take action EX then lease SH, so
    holding lease EX here would deadlock); acquire boundary first, then
    re-check the lease while holding all three.
    """
    deadline = time.monotonic() + max(float(timeout), 0.0)
    action_path = Path(control_dir) / "foreground-action.lock"
    watch_path = Path(control_dir) / "watch.lock"
    try:
        action_fh = open(action_path, "a")
    except OSError:
        return None, None
    while True:
        try:
            fcntl.flock(action_fh, fcntl.LOCK_EX | fcntl.LOCK_NB)
            break
        except (BlockingIOError, OSError):
            if time.monotonic() >= deadline:
                try:
                    action_fh.close()
                except OSError:
                    pass
                return None, None
            time.sleep(poll)
    try:
        watch_fh = open(watch_path, "a")
    except OSError:
        try:
            action_fh.close()
        except OSError:
            pass
        return None, None
    while True:
        try:
            fcntl.flock(watch_fh, fcntl.LOCK_EX | fcntl.LOCK_NB)
            return action_fh, watch_fh
        except (BlockingIOError, OSError):
            if time.monotonic() >= deadline:
                for fh in (watch_fh, action_fh):
                    try:
                        fh.close()
                    except OSError:
                        pass
                return None, None
            time.sleep(poll)


def close_fhs(*fhs):
    for fh in fhs:
        if fh is None:
            continue
        try:
            fh.close()
        except OSError:
            pass


def own_pause_path(control_dir):
    return Path(control_dir) / "coordinator-pause.json"


def ensure_own_pause(control_dir):
    """Request a watcher safe boundary via a supervisor-owned pause file."""
    path = own_pause_path(control_dir)
    try:
        if path.is_file():
            try:
                doc = json.loads(path.read_text())
            except (ValueError, OSError):
                doc = {}
            if str(doc.get("owner", "")) == f"failover-{os.getpid()}":
                return True
            return False
    except OSError:
        return False
    try:
        atomic_write_json(path, {"owner": f"failover-{os.getpid()}",
                                 "requested": now_iso(),
                                 "reason": "failover requests watcher safe "
                                           "boundary before role close"})
    except OSError:
        return False
    return True


def remove_own_pause(control_dir):
    """Remove only the supervisor's own pause request, never another's."""
    path = own_pause_path(control_dir)
    try:
        if not path.is_file():
            return True
        try:
            doc = json.loads(path.read_text())
        except (ValueError, OSError):
            return False
        if str(doc.get("owner", "")) != f"failover-{os.getpid()}":
            return False
        path.unlink()
    except OSError:
        return False
    return True


def coordinator_cmd(coordinator):
    if str(coordinator).endswith(".py"):
        return [sys.executable, str(coordinator)]
    return [str(coordinator)]


def coordinator_action(coordinator, action, timeout=120):
    """Dispatch one coordinator action via subprocess argv, never a shell."""
    import subprocess
    try:
        out = subprocess.run(
            coordinator_cmd(coordinator) + [action],
            text=True, capture_output=True, timeout=timeout)
    except Exception:
        return False, "spawn_failed"
    return (out.returncode == 0), f"exit_{out.returncode}"


def model_env(args, epoch):
    env = os.environ.copy()
    env["GABBRO_COORDINATOR_ROLE"] = "muse"
    env["GABBRO_COORDINATOR_EPOCH"] = epoch
    env["OPENCODE_DISABLE_AUTOUPDATE"] = "1"
    env["OPENCODE_DB"] = str(
        Path(args.control_dir) / "sessions" / "fallback-coordinator.db")
    scratch = Path(args.pool_dir) / "fallback-scratch"
    try:
        scratch.mkdir(parents=True, exist_ok=True)
    except OSError:
        pass
    env["TMPDIR"] = str(scratch)
    return env


def model_argv(args):
    argv = [str(args.opencode), "run", "--model", str(args.model),
            "--title", "gabbro-fallback-coordinator"]
    if args.prompt_file:
        argv += ["--file", str(args.prompt_file)]
    return argv


def write_status(control_dir, **fields):
    doc = {"time": now_iso()}
    doc.update(fields)
    atomic_write_json(Path(control_dir) / "failover-status.json", doc)
    return doc


MAX_BACKOFF_SECS = 300.0


def should_takeover(lease, paused, model_alive, age, timeout):
    return (not paused and not model_alive
            and lease.get("owner") == "codex" and age >= timeout)


def live_fallback(args, lease):
    if lease.get("owner") != "muse" or not lease.get("model_pid"):
        return None
    return identify_model(
        lease.get("model_pid"), args.proc_root,
        args.opencode, args.model, lease.get("model_start_time"))


def leader_alive(pid, proc, proc_root, opencode, model, start):
    """True while OUR direct fallback child still exists.

    For an adopted pid the start time is rechecked so a reused pid is never
    mistaken for the fallback. A zombie direct child counts as gone once it
    can be reaped (Popen) or once its state is Z/X (adopted).
    """
    if proc is not None:
        if proc.poll() is not None:
            return False
        return True
    info = read_proc_parts(proc_root, int(pid))
    if info is None:
        return False
    parts, state, starttime = info
    if state in ("Z", "X"):
        return False
    if state == "unknown":
        return True
    blob = "\x00".join(parts)
    if opencode not in blob or model not in blob:
        return False
    if start is not None and starttime is not None:
        if str(start) != str(starttime):
            return False
    return True


def stop_own_child(pid, proc=None, proc_root="/proc", opencode="",
                   model="", start=None, timeout=30):
    """Stop only the supervisor's own fallback process tree.

    Every signal is scoped to the fallback's own process group (it is
    started as a group leader). Group *existence* is never used as the stop
    criterion: an orphaned grandchild keeps the group id alive after the
    leader dies, so the loop waits for the direct child and then SIGKILLs
    strays of the same group instead of blocking.
    """
    import signal
    pid = int(pid)
    try:
        os.killpg(pid, signal.SIGTERM)
    except (ProcessLookupError, PermissionError, ValueError, OSError):
        pass
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        if not leader_alive(pid, proc, proc_root, opencode, model, start):
            break
        time.sleep(0.2)
    if proc is not None:
        try:
            proc.wait(timeout=5)
        except Exception:
            pass
    # Strays of our own tree may outlive the leader (reparented, same group).
    try:
        os.killpg(pid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError, ValueError, OSError):
        pass
    if proc is not None:
        try:
            return str(proc.wait(timeout=5))
        except Exception:
            return "killed"
    return "stopped"


def update_lease_locked(control_dir, **values):
    """Read-modify-write the lease, preserving unknown keys (e.g. session)."""
    path = Path(control_dir) / "orchestrator-lease.json"
    try:
        lease = json.loads(path.read_text())
    except (FileNotFoundError, ValueError, OSError):
        lease = {}
    lease.update(values)
    atomic_write_json(path, lease)
    return lease


def run_supervise(args):
    import subprocess
    if args.turn_seconds > 7200.0:
        print("error: --turn-seconds must be <= 7200", file=sys.stderr)
        return 3
    control = Path(args.control_dir)
    control.mkdir(parents=True, exist_ok=True)
    (control / "sessions").mkdir(parents=True, exist_ok=True)
    sup_lock = open(control / "failover-supervisor.lock", "a")
    try:
        fcntl.flock(sup_lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except (BlockingIOError, OSError):
        write_status(args.control_dir, status="duplicate_supervisor",
                     detail="another failover supervisor holds the lock; "
                            "no second supervisor started")
        print("Another failover supervisor is already running; exiting.")
        return 4
    budget = float(args.budget)
    timeout = float(args.timeout_seconds)
    turn_secs = float(args.turn_seconds)
    poll = max(float(args.poll_seconds), 0.05)
    start = time.monotonic()
    child = None  # dict(proc|None, pid, turn_start, slot, slot_fh, role_fh,
    #                guardian_proc|None, guardian_pid|None, epoch)
    started = 0
    failures = 0
    backoff = 5.0
    retry_at = 0.0
    last_exit = None
    note = "watching_foreground_heartbeat"
    dispatcher_held = False

    def dispatcher_stop_once():
        nonlocal dispatcher_held
        if dispatcher_held:
            return
        try:
            coordinator_action(args.coordinator, "dispatch_stop")
        except Exception:
            pass
        dispatcher_held = True

    def dispatcher_restore():
        nonlocal dispatcher_held
        if not dispatcher_held:
            return
        try:
            coordinator_action(args.coordinator, "dispatch_start")
        except Exception:
            pass
        dispatcher_held = False

    def release_child_locks():
        if child is not None:
            for fh in (child.get("slot_fh"), child.get("role_fh")):
                try:
                    if fh is not None:
                        fh.close()
                except OSError:
                    pass
            child["slot_fh"] = None
            child["role_fh"] = None

    def reap_guardian():
        if child is not None:
            gproc = child.get("guardian_proc")
            child["guardian_proc"] = None
            child["guardian_pid"] = None
            if gproc is not None:
                try:
                    gproc.wait(timeout=0)
                except Exception:
                    pass

    # Crash/restart recovery: adopt an already-identified live fallback
    # instead of starting a duplicate, and NEVER take a different slot
    # while its group still lives. A slot that is still flock-held is
    # recognised as held (lock_slot fails) and adopted as externally
    # held; only a free recorded slot is re-held (pre-inheritance
    # leases) to restore the cap, with a fresh guardian.
    with open(control / "orchestrator-lease.lock", "a") as guard:
        fcntl.flock(guard, fcntl.LOCK_EX)
        lease = read_lease(args.control_dir)
        found = live_fallback(args, lease)
        if found is not None:
            slot = lease.get("slot")
            slot_fh = lock_slot(args.pool_dir, slot) if slot else None
            slot_held_externally = False
            if slot is not None and slot_fh is None:
                # Still held by the fallback/guardian that inherited the
                # same description via pass_fds: recognised, not best-effort
                # released, and no different slot is taken.
                slot_held_externally = True
            role_fh = open(control / "fallback-owner.lock", "a")
            try:
                fcntl.flock(role_fh, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except (BlockingIOError, OSError):
                # Role still held by the inherited fallback/guardian copy.
                try:
                    role_fh.close()
                except OSError:
                    pass
                role_fh = None
            gpid = lease.get("guardian_pid")
            g_alive = guardian_alive(gpid, args.proc_root,
                                     lease.get("model_pid"))
            child = {"proc": None, "pid": found["pid"],
                     "turn_start": time.monotonic(),
                     "slot": slot, "slot_fh": slot_fh, "role_fh": role_fh,
                     "guardian_proc": None,
                     "guardian_pid": gpid if g_alive else None,
                     "epoch": str(lease.get("epoch", ""))}
            if slot_held_externally:
                note = "adopted_live_fallback_slot_held"
            else:
                note = "adopted_live_fallback"
            if not g_alive and slot_fh is not None:
                # Pre-inheritance lease re-held: attach a fresh guardian
                # sharing the same description so the cap outlives us.
                try:
                    gproc = spawn_guardian(found["pid"], args.proc_root,
                                           slot_fh, role_fh)
                except Exception:
                    gproc = None
                if gproc is not None:
                    child["guardian_proc"] = gproc
                    child["guardian_pid"] = gproc.pid
                    try:
                        update_lease_locked(
                            args.control_dir,
                            guardian_pid=gproc.pid)
                    except OSError:
                        pass

    while budget <= 0 or time.monotonic() - start < budget:
        with open(control / "orchestrator-lease.lock", "a") as guard:
            fcntl.flock(guard, fcntl.LOCK_EX)
            lease = read_lease(args.control_dir)
            age = heartbeat_age_secs(lease)
            paused, pause_name = is_paused(args.control_dir)
            want_return = return_requested(args.control_dir)
            alive = live_fallback(args, lease)

            if child is not None and alive is None:
                # Direct fallback gone (or pid reused by an unrelated
                # process, which never counts). The role/slot stay held
                # until EVERY live group member is gone: orphaned
                # grandchildren keep the pgid alive and the inherited
                # guardian copy keeps the kernel lock.
                if child.get("proc") is not None:
                    try:
                        last_exit = child["proc"].wait(timeout=0)
                    except Exception:
                        last_exit = "gone"
                pgid = child["pid"]
                strays = group_members(
                    pgid, args.proc_root,
                    exclude=(os.getpid(), child.get("guardian_pid") or -1))
                if strays:
                    # Keep slot/role: release nothing, hand back nothing.
                    # If our copies were the only holders and are somehow
                    # free, re-hold the recorded slot to cover the strays.
                    if (child.get("slot_fh") is None and child.get("slot")
                            is not None):
                        cover = lock_slot(args.pool_dir, child.get("slot"))
                        if cover is not None:
                            child["slot_fh"] = cover
                    note = (f"descendants_remain_{len(strays)}_"
                            f"slot_held")
                    failures = 0
                    alive = None
                    lease = read_lease(args.control_dir)
                    age = heartbeat_age_secs(lease)
                else:
                    quick = (time.monotonic() - child["turn_start"]) < 60.0
                    # Group fully drained: guardian exits on its own once
                    # it observes the empty group; reap it, then release
                    # our copies so the kernel lock frees only now.
                    reap_guardian()
                    release_child_locks()
                    if want_return:
                        update_lease_locked(
                            args.control_dir, owner="codex",
                            heartbeat=now_iso(), timeout_seconds=timeout,
                            model_pid=None, guardian_pid=None,
                            returned_from_muse=True)
                        try:
                            (control / "return-to-codex.json").unlink()
                        except OSError:
                            pass
                        note = "handed_back"
                    else:
                        stale = (datetime.datetime.now(datetime.timezone.utc)
                                 - datetime.timedelta(seconds=timeout + 1))
                        update_lease_locked(
                            args.control_dir, owner="codex",
                            heartbeat=stale.isoformat(),
                            timeout_seconds=timeout, model_pid=None,
                            guardian_pid=None)
                        note = "turn_ended"
                    child = None
                    if want_return or paused:
                        failures = 0
                        backoff = 5.0
                        retry_at = 0.0
                    elif quick:
                        failures += 1
                        backoff = min(backoff * 2, MAX_BACKOFF_SECS)
                        retry_at = (time.monotonic() + backoff)
                        note = f"quick_exit_backing_off_{backoff:.0f}s"
                    else:
                        failures = 0
                        backoff = 5.0
                        retry_at = 0.0
                alive = None
                lease = read_lease(args.control_dir)
                age = heartbeat_age_secs(lease)

            if child is not None:
                turn_age = time.monotonic() - child["turn_start"]
                stop_reason = None
                if paused:
                    stop_reason = f"paused_by_{pause_name}"
                elif want_return:
                    stop_reason = "return_requested"
                elif turn_age > turn_secs:
                    stop_reason = "turn_expired"
                if stop_reason is not None:
                    # Safe boundary with locks HELD across termination,
                    # never probe-and-release. Nonblocking acquire while
                    # holding the lease lock (no deadlock: a holder keeps
                    # making progress and we retry next poll after
                    # releasing the lease). On success both locks stay
                    # held through signal, group drain and lease update,
                    # so no new action/integration can start mid-kill.
                    if not git_clean(args.project_root):
                        note = "waiting_for_safe_boundary_dirty_root"
                        failures = 0
                    else:
                        act_fh, wat_fh = acquire_boundary(
                            args.control_dir, timeout=0.0)
                        if act_fh is None:
                            _safe, why = safe_boundary(
                                args.control_dir, args.project_root)
                            note = f"waiting_for_safe_boundary_{why}"
                            failures = 0
                            if why == "watch_busy":
                                ensure_own_pause(args.control_dir)
                        else:
                            try:
                                pid = child["pid"]
                                if (child.get("proc") is None
                                        and live_fallback(
                                            args, read_lease(
                                                args.control_dir)) is None
                                        and not group_members(
                                            pid, args.proc_root,
                                            exclude=(os.getpid(),
                                                     child.get(
                                                         "guardian_pid")
                                                     or -1))):
                                    release_child_locks()
                                    reap_guardian()
                                    child = None
                                    remove_own_pause(args.control_dir)
                                    note = f"adopted_gone_{stop_reason}"
                                else:
                                    lease_now = read_lease(args.control_dir)
                                    outcome = stop_own_child(
                                        pid, proc=child.get("proc"),
                                        proc_root=args.proc_root,
                                        opencode=args.opencode,
                                        model=args.model,
                                        start=lease_now.get(
                                            "model_start_time"))
                                    last_exit = outcome
                                    # Drain the whole group while still
                                    # holding boundary + lease + slot/role:
                                    # release role/slot only after every
                                    # live descendant is gone.
                                    drained = wait_group_gone(
                                        pid, args.proc_root,
                                        exclude=(os.getpid(),
                                                 child.get("guardian_pid")
                                                 or -1),
                                        timeout=30.0)
                                    if not drained:
                                        note = ("descendants_remain_"
                                                "fail_closed")
                                        last_exit = (
                                            f"{outcome};"
                                            "group_not_drained")
                                    else:
                                        reap_guardian()
                                        release_child_locks()
                                        remove_own_pause(args.control_dir)
                                        if want_return or paused:
                                            update_lease_locked(
                                                args.control_dir,
                                                owner="codex",
                                                heartbeat=now_iso(),
                                                timeout_seconds=timeout,
                                                model_pid=None,
                                                guardian_pid=None,
                                                returned_from_muse=bool(
                                                    want_return))
                                            if want_return:
                                                try:
                                                    (control /
                                                     "return-to-codex.json"
                                                     ).unlink()
                                                except OSError:
                                                    pass
                                            note = (f"stopped_at_boundary_"
                                                    f"{stop_reason}")
                                        else:
                                            stale = (datetime.datetime.now(
                                                datetime.timezone.utc)
                                                - datetime.timedelta(
                                                    seconds=timeout + 1))
                                            update_lease_locked(
                                                args.control_dir,
                                                owner="codex",
                                                heartbeat=stale.isoformat(),
                                                timeout_seconds=timeout,
                                                model_pid=None,
                                                guardian_pid=None,
                                                last_exit=last_exit)
                                            note = (f"stopped_at_boundary_"
                                                    f"{stop_reason}")
                                        child = None
                                        failures = 0
                                        backoff = 5.0
                                        retry_at = 0.0
                            finally:
                                close_fhs(act_fh, wat_fh)
                    lease = read_lease(args.control_dir)
                    age = heartbeat_age_secs(lease)
                    paused, pause_name = is_paused(args.control_dir)
            if child is None and paused:
                dispatcher_restore()
                write_status(args.control_dir, pid=os.getpid(),
                             status="paused_no_takeover", owner="codex",
                             foreground_heartbeat_age_seconds=round(age, 1),
                             timeout_seconds=timeout, model_pid=None,
                             bounded_turns_started=started,
                             last_exit=last_exit, note=note)
                return 0

            if child is None and should_takeover(
                    lease, paused, alive is not None, age, timeout):
                if failures > 0 and time.monotonic() < retry_at:
                    note = f"backing_off_{max(retry_at - time.monotonic(), 0):.0f}s"
                else:
                    # Free one dispatcher slot for the role; contributors,
                    # watchers and the user's own processes are never
                    # touched. Stopped once, kept stopped while awaiting a
                    # slot: no stop/start churn.
                    if not dispatcher_held:
                        dispatcher_stop_once()
                    role_fh = open(control / "fallback-owner.lock", "a")
                    try:
                        fcntl.flock(role_fh, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    except (BlockingIOError, OSError):
                        role_fh.close()
                        role_fh = None
                        note = "role_held_by_other"
                        failures += 1
                        backoff = min(max(backoff, 5.0) * 2,
                                      MAX_BACKOFF_SECS)
                        retry_at = time.monotonic() + backoff
                        dispatcher_restore()
                    else:
                        slot, slot_fh = reserve_slot(args.pool_dir)
                        if slot is None:
                            role_fh.close()
                            role_fh = None
                            # All 15 slots occupied: KEEP the owned
                            # dispatcher stopped (reserved next
                            # completion), back off without churn, and
                            # restore only on fresh foreground, explicit
                            # pause, failed launch or successful handoff.
                            note = "slot_exhausted_dispatcher_held"
                            failures = 0
                            backoff = 5.0
                            retry_at = time.monotonic() + 30.0
                        else:
                            fresh = read_lease(args.control_dir)
                            fresh_age = heartbeat_age_secs(fresh)
                            fresh_paused, _ = is_paused(args.control_dir)
                            if not should_takeover(
                                    fresh, fresh_paused,
                                    live_fallback(args, fresh) is not None,
                                    fresh_age, timeout):
                                slot_fh.close()
                                role_fh.close()
                                note = "fresh_heartbeat_before_launch"
                                dispatcher_restore()
                            else:
                                epoch = (datetime.datetime.now(
                                    datetime.timezone.utc).strftime(
                                        "%Y%m%dT%H%M%S")
                                    + "-" + uuid.uuid4().hex[:8])
                                log = open(control / "fallback-model.log", "a",
                                           buffering=1)
                                try:
                                    # Inherit the SAME locked slot/role
                                    # descriptions into the model: the
                                    # kernel lock then outlives a
                                    # supervisor crash/budget exit while
                                    # the fallback or its group remains.
                                    proc = subprocess.Popen(
                                        model_argv(args), cwd=str(
                                            args.project_root),
                                        env=model_env(args, epoch),
                                        stdin=subprocess.DEVNULL,
                                        stdout=log, stderr=subprocess.STDOUT,
                                        start_new_session=True,
                                        close_fds=False,
                                        pass_fds=(slot_fh.fileno(),
                                                  role_fh.fileno()))
                                except Exception:
                                    proc = None
                                finally:
                                    try:
                                        log.close()
                                    except OSError:
                                        pass
                                if proc is None:
                                    slot_fh.close()
                                    role_fh.close()
                                    failures += 1
                                    backoff = min(backoff * 2,
                                                  MAX_BACKOFF_SECS)
                                    retry_at = (time.monotonic() + backoff)
                                    note = "launch_failed"
                                    dispatcher_restore()
                                else:
                                    # Guardian shares the same
                                    # descriptions in its own session so
                                    # the slot/role stay held until ALL
                                    # live group members are gone,
                                    # including orphaned grandchildren
                                    # the model runtime never inherits
                                    # the fd to.
                                    try:
                                        gproc = spawn_guardian(
                                            proc.pid, args.proc_root,
                                            slot_fh, role_fh)
                                    except Exception:
                                        gproc = None
                                    started += 1
                                    failures = 0
                                    backoff = 5.0
                                    retry_at = 0.0
                                    begun = get_start_time(
                                        proc.pid, args.proc_root)
                                    update_lease_locked(
                                        args.control_dir, owner="muse",
                                        model_pid=proc.pid,
                                        model_start_time=begun,
                                        slot=slot, epoch=epoch,
                                        claimed=now_iso(),
                                        timeout_seconds=timeout,
                                        supervisor_pid=os.getpid(),
                                        guardian_pid=(gproc.pid
                                                      if gproc is not None
                                                      else None))
                                    child = {"proc": proc, "pid": proc.pid,
                                             "turn_start": time.monotonic(),
                                             "slot": slot, "slot_fh": slot_fh,
                                             "role_fh": role_fh,
                                             "guardian_proc": gproc,
                                             "guardian_pid": (
                                                 gproc.pid
                                                 if gproc is not None
                                                 else None),
                                             "epoch": epoch}
                                    note = "muse_coordinates"
                                    dispatcher_restore()
                lease = read_lease(args.control_dir)

        model_pid = child["pid"] if child is not None else None
        slot = child["slot"] if child is not None else None
        write_status(args.control_dir, pid=os.getpid(),
                     status="muse_coordinates" if child is not None
                     else "watching_foreground_heartbeat",
                     owner=(lease.get("owner", "codex")),
                     foreground_heartbeat_age_seconds=round(age, 1),
                     timeout_seconds=timeout, model_pid=model_pid, slot=slot,
                     bounded_turns_started=started,
                     consecutive_failures=failures, last_exit=last_exit,
                     paused=paused, note=note,
                     dispatcher_held=dispatcher_held)
        time.sleep(poll)
    # Budget end: exiting never stops a live fallback/group (its
    # inherited copies keep the slot/role); restore a held dispatcher so
    # the pool resumes, and leave adoption to the next supervisor.
    dispatcher_restore()
    final_lease = read_lease(args.control_dir)
    write_status(args.control_dir, pid=os.getpid(), status="budget_done",
                 owner=final_lease.get("owner", "codex"),
                 model_pid=(child["pid"] if child is not None else None),
                 slot=(child["slot"] if child is not None else None),
                 bounded_turns_started=started, last_exit=last_exit,
                 consecutive_failures=failures, note=note)
    return 0


def main(argv=None):
    args = parse_args(argv)
    if args.action == "heartbeat":
        return run_heartbeat(args)
    return run_supervise(args)


if __name__ == "__main__":
    raise SystemExit(main())
