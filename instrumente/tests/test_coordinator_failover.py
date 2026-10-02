#!/usr/bin/env python3
"""Tests for instrumente/coordinator-failover.py (lane 620).

Fixture dirs live inside the clone (never /tmp); only the standard library
is used. No real agents, no network, no live control files: the OpenCode
binary and the coordinator are generic fake scripts, and pid-identity cases
use fixture proc roots.
Run: python3 instrumente/tests/test_coordinator_failover.py
"""
import fcntl
import importlib.util
import json
import os
import signal
import subprocess
import tempfile
import threading
import time
import unittest
from pathlib import Path

SUPERVISOR = Path(__file__).resolve().parents[1] / "coordinator-failover.py"
CLONE_TMP = Path(__file__).resolve().parents[2] / ".tmp"
MODEL = "muse-spark-testmodel-620"
OPENCODE_NAME = "fakeopencode620"


def load_supervisor():
    spec = importlib.util.spec_from_file_location("coordinator_failover",
                                                  str(SUPERVISOR))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


CF = load_supervisor()


def make_args(**over):
    ns = dict(action="supervise", project_root="", control_dir="",
              pool_dir="", coordinator="", opencode="", model=MODEL,
              budget=3.0, timeout_seconds=300.0, turn_seconds=60.0,
              proc_root="/proc", prompt_file=None, poll_seconds=0.05)
    ns.update(over)
    return type("A", (), ns)()


class Fixture:
    def __init__(self):
        CLONE_TMP.mkdir(exist_ok=True)
        self.tmp = tempfile.TemporaryDirectory(prefix="fail620-",
                                               dir=str(CLONE_TMP))
        self.root = Path(self.tmp.name)
        self.control = self.root / "control"
        self.pool = self.root / "pool"
        self.proj = self.root / "proj"
        for d in (self.control, self.pool, self.proj):
            d.mkdir(parents=True, exist_ok=True)
        subprocess.run(["git", "init", "-q", str(self.proj)], check=True)
        subprocess.run(["git", "-C", str(self.proj), "config", "user.email",
                        "t@t.invalid"], check=True)
        subprocess.run(["git", "-C", str(self.proj), "config", "user.name",
                        "t"], check=True)
        self.coord_log = self.root / "coord.log"
        self.coord = self.root / "fake-coordinator.sh"
        self.coord.write_text(
            "#!/bin/sh\n"
            f'echo "coord $@" >> "{self.coord_log}"\n'
            "exit 0\n")
        self.coord.chmod(0o755)
        # The fake model binary name carries both identity markers, so the
        # real /proc cmdline identifies it like the production binary.
        self.opencode = self.root / f"{OPENCODE_NAME}-{MODEL}.sh"
        self.opencode.write_text("#!/bin/sh\nsleep 30\n")
        self.opencode.chmod(0o755)
        self.exiter = self.root / f"{OPENCODE_NAME}-{MODEL}-exiter.sh"
        self.exiter.write_text("#!/bin/sh\nexit 3\n")
        self.exiter.chmod(0o755)
        self.children = []

    def close(self):
        for pid in self.children:
            try:
                os.killpg(pid, signal.SIGKILL)
            except (ProcessLookupError, PermissionError, OSError):
                pass
        for pid in self.children:
            try:
                os.waitpid(pid, 0)
            except (ChildProcessError, OSError):
                pass
        self.tmp.cleanup()

    def args(self, **over):
        kw = dict(project_root=str(self.proj), control_dir=str(self.control),
                  pool_dir=str(self.pool), coordinator=str(self.coord),
                  opencode=str(self.opencode))
        kw.update(over)
        return make_args(**kw)

    def write_lease(self, **fields):
        doc = {"owner": "codex", "heartbeat": "2020-01-01T00:00:00+00:00",
               "timeout_seconds": 300.0}
        doc.update(fields)
        (self.control / "orchestrator-lease.json").write_text(
            json.dumps(doc))
        return doc

    def stale_lease(self):
        import datetime
        hb = (datetime.datetime.now(datetime.timezone.utc)
              - datetime.timedelta(seconds=301)).isoformat()
        return self.write_lease(owner="codex", heartbeat=hb)

    def read_lease(self):
        return json.loads(
            (self.control / "orchestrator-lease.json").read_text())

    def read_status(self):
        return json.loads(
            (self.control / "failover-status.json").read_text())

    def coord_calls(self):
        if not self.coord_log.is_file():
            return []
        return self.coord_log.read_text().splitlines()

    def track_children_from_lease(self):
        try:
            pid = self.read_lease().get("model_pid")
        except (FileNotFoundError, ValueError, OSError):
            return
        if pid:
            self.children.append(int(pid))

    def reap(self):
        for pid in list(self.children):
            try:
                os.waitpid(pid, 0)
            except (ChildProcessError, OSError):
                pass


class UnitTest(unittest.TestCase):
    def setUp(self):
        self.f = Fixture()

    def tearDown(self):
        self.f.close()

    def test_slot_files_share_contributor_names(self):
        self.assertEqual(CF.SLOT_COUNT, 15)
        slot, fh = CF.reserve_slot(str(self.f.pool))
        try:
            self.assertEqual(slot, 1)
            self.assertTrue(
                (self.f.pool / "locks" / "go-contributor-01").is_file())
            names = sorted(p.name for p in
                           (self.f.pool / "locks").iterdir())
            self.assertTrue(all(n.startswith("go-contributor-")
                                for n in names))
        finally:
            fh.close()

    def test_takeover_predicate(self):
        self.assertTrue(CF.should_takeover({"owner": "codex"}, False,
                                           False, 300.0, 300.0))
        self.assertFalse(CF.should_takeover({"owner": "codex"}, False,
                                            False, 299.9, 300.0))
        self.assertFalse(CF.should_takeover({"owner": "codex"}, True,
                                            False, 900.0, 300.0))
        self.assertFalse(CF.should_takeover({"owner": "codex"}, False,
                                            True, 900.0, 300.0))
        self.assertFalse(CF.should_takeover({"owner": "muse"}, False,
                                            False, 900.0, 300.0))

    def test_model_env_is_scoped_and_epoch_carries_role(self):
        args = self.f.args()
        env = CF.model_env(args, "epoch-1")
        self.assertEqual(env["GABBRO_COORDINATOR_ROLE"], "muse")
        self.assertEqual(env["GABBRO_COORDINATOR_EPOCH"], "epoch-1")
        self.assertTrue(env["OPENCODE_DB"].startswith(str(self.f.control)))
        self.assertTrue(env["TMPDIR"].startswith(str(self.f.pool)))
        self.assertNotIn("/tmp", env["TMPDIR"].replace(str(self.f.root), ""))

    def test_pid_identity_against_fixture_proc(self):
        proot = self.f.root / "proc"
        proot.mkdir()
        (proot / "meminfo").write_text("MemAvailable: 999999 kB\n")

        def add(pid, cmdline, state="S", start="12345"):
            d = proot / str(pid)
            d.mkdir(exist_ok=True)
            (d / "cmdline").write_bytes(cmdline)
            (d / "stat").write_text(
                f"{pid} (x) {state} 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 {start} 0 0")

        good = OPENCODE_NAME.encode() + b"\x00" + MODEL.encode()
        add(101, good + b"\x00run\x00")
        self.assertIsNotNone(CF.identify_model(
            101, str(proot), OPENCODE_NAME, MODEL, "12345"))
        # Reused pid running an unrelated binary never counts.
        add(102, b"sleep\x001000\x00")
        self.assertIsNone(CF.identify_model(
            102, str(proot), OPENCODE_NAME, MODEL))
        # Zombie / dead states never count.
        add(103, good, state="Z")
        self.assertIsNone(CF.identify_model(
            103, str(proot), OPENCODE_NAME, MODEL))
        add(104, good, state="X")
        self.assertIsNone(CF.identify_model(
            104, str(proot), OPENCODE_NAME, MODEL))
        # A reused pid with a different start time never counts.
        add(105, good, start="99999")
        self.assertIsNone(CF.identify_model(
            105, str(proot), OPENCODE_NAME, MODEL, "12345"))
        # A gone pid is not an error.
        self.assertIsNone(CF.identify_model(
            106, str(proot), OPENCODE_NAME, MODEL))

    def test_heartbeat_writes_foreground_lease(self):
        args = self.f.args(action="heartbeat")
        self.assertEqual(CF.run_heartbeat(args), 0)
        lease = self.f.read_lease()
        self.assertEqual(lease["owner"], "codex")
        self.assertIn("heartbeat", lease)

    def test_heartbeat_while_muse_owns_requests_handback(self):
        proc = subprocess.Popen([str(self.f.opencode), "run"],
                                start_new_session=True)
        self.f.children.append(proc.pid)
        try:
            started = CF.get_start_time(proc.pid, "/proc")
            self.assertIsNotNone(started)
            self.f.write_lease(owner="muse", model_pid=proc.pid,
                               model_start_time=started, slot=3,
                               epoch="e1", heartbeat="2020-01-01T00:00:00+00:00")
            args = self.f.args(action="heartbeat")
            self.assertEqual(CF.run_heartbeat(args), 2)
            self.assertTrue(
                (self.f.control / "return-to-codex.json").is_file())
            lease = self.f.read_lease()
            self.assertEqual(lease.get("model_pid"), proc.pid)
            self.assertEqual(lease.get("owner"), "muse")
        finally:
            pass

    def _kill(self, pid):
        # Kept for debugging; fixture teardown owns process cleanup.
        self.f.children.append(pid)

class SuperviseTest(unittest.TestCase):
    def setUp(self):
        self.f = Fixture()

    def tearDown(self):
        try:
            self.f.track_children_from_lease()
        finally:
            self.f.close()
        self.f.reap()

    def wait_for(self, pred, timeout=10.0):
        end = time.monotonic() + timeout
        while time.monotonic() < end:
            try:
                if pred():
                    return True
            except (FileNotFoundError, ValueError, OSError):
                pass
            time.sleep(0.05)
        return False

    def lease_owner_is(self, owner):
        try:
            return self.f.read_lease().get("owner") == owner
        except (FileNotFoundError, ValueError, OSError):
            return False

    def test_takeover_starts_once_and_holds_slot(self):
        self.f.stale_lease()
        done = []
        t = threading.Thread(target=lambda: done.append(
            CF.run_supervise(self.f.args(budget=30.0))), daemon=True)
        t.start()
        self.assertTrue(self.wait_for(lambda: self.lease_owner_is("muse")))
        lease = self.f.read_lease()
        pid = lease.get("model_pid")
        self.assertIsNotNone(pid)
        self.f.children.append(int(pid))
        os.kill(int(pid), 0)
        # While the fallback lives, its shared slot lock is held: a second
        # reservation of the same slot must fail.
        probe = open(CF.slot_path(str(self.f.pool), lease["slot"]), "a")
        with probe:
            self.assertRaises(BlockingIOError, fcntl.flock, probe,
                              fcntl.LOCK_EX | fcntl.LOCK_NB)
        # Dispatcher was paused for the reservation and resumed after launch.
        calls = self.f.coord_calls()
        self.assertIn("coord dispatch_stop", calls)
        self.assertIn("coord dispatch_start", calls)
        # Role epoch is unique and carried in the lease for the mutation gate.
        self.assertTrue(str(lease.get("epoch", "")))
        status = self.f.read_status()
        self.assertEqual(status["bounded_turns_started"], 1)
        self.assertEqual(status["slot"], lease.get("slot"))
        self.assertNotIn("secret", json.dumps(status))
        (self.f.control / "pool-paused.json").write_text('{"status":"x"}\n')
        t.join(timeout=20)
        self.assertFalse(t.is_alive())
        self.assertEqual(done, [0])
        with self.assertRaises(OSError):
            os.kill(int(pid), 0)

    def test_fresh_heartbeat_never_launches(self):
        before = self.f.write_lease(owner="codex",
                                    heartbeat="2999-01-01T00:00:00+00:00")
        rc = CF.run_supervise(self.f.args(budget=1.0))
        self.assertEqual(rc, 0)
        self.assertEqual(self.f.read_lease(), before)
        self.assertEqual(self.f.read_status()["bounded_turns_started"], 0)

    def test_pause_prevents_takeover(self):
        self.f.stale_lease()
        (self.f.control / "pool-paused.json").write_text('{"status":"x"}\n')
        rc = CF.run_supervise(self.f.args(budget=1.0))
        self.assertEqual(rc, 0)
        self.assertEqual(self.f.read_status()["status"], "paused_no_takeover")
        self.assertEqual(self.f.read_status()["bounded_turns_started"], 0)

    def test_pause_stops_role_at_safe_boundary(self):
        self.f.stale_lease()
        done = []
        t = threading.Thread(target=lambda: done.append(
            CF.run_supervise(self.f.args(budget=30.0))), daemon=True)
        t.start()
        self.assertTrue(self.wait_for(lambda: self.lease_owner_is("muse")))
        pid = int(self.f.read_lease()["model_pid"])
        self.f.children.append(pid)
        (self.f.control / "pool-paused.json").write_text('{"status":"x"}\n')
        t.join(timeout=20)
        self.assertFalse(t.is_alive())
        self.assertEqual(done, [0])
        with self.assertRaises(OSError):
            os.kill(pid, 0)

    def test_all_slots_occupied_means_no_launch(self):
        self.f.stale_lease()
        (self.f.pool / "locks").mkdir(parents=True, exist_ok=True)
        held = []
        for slot in range(1, 16):
            fh = open(CF.slot_path(str(self.f.pool), slot), "a")
            fcntl.flock(fh, fcntl.LOCK_EX | fcntl.LOCK_NB)
            held.append(fh)
        try:
            rc = CF.run_supervise(self.f.args(budget=1.0))
        finally:
            for fh in held:
                fh.close()
        self.assertEqual(rc, 0)
        self.assertEqual(self.f.read_status()["bounded_turns_started"], 0)
        self.assertEqual(self.f.read_status()["note"],
                         "slot_exhausted_dispatcher_held")

    def test_duplicate_supervisor_exits(self):
        self.f.stale_lease()
        guard = open(self.f.control / "failover-supervisor.lock", "a")
        fcntl.flock(guard, fcntl.LOCK_EX | fcntl.LOCK_NB)
        try:
            rc = CF.run_supervise(self.f.args(budget=1.0))
        finally:
            fcntl.flock(guard, fcntl.LOCK_UN)
            guard.close()
        self.assertEqual(rc, 4)
        self.assertEqual(self.f.read_status()["status"],
                         "duplicate_supervisor")

    def test_launch_failure_backs_off_without_storm(self):
        self.f.stale_lease()
        start = time.monotonic()
        rc = CF.run_supervise(self.f.args(budget=4.0,
                                          opencode="/nonexistent-binary"))
        elapsed = time.monotonic() - start
        self.assertEqual(rc, 0)
        self.assertEqual(self.f.read_status()["bounded_turns_started"], 0)
        stops = [c for c in self.f.coord_calls()
                 if c == "coord dispatch_stop"]
        self.assertLessEqual(len(stops), 3)
        self.assertGreaterEqual(elapsed, 3.5)
        self.assertIn("backing_off",
                      self.f.read_status().get("note", ""))

    def test_turn_expiry_kills_only_own_child(self):
        decoy = subprocess.Popen(["sleep", "30"], start_new_session=True)
        self.addCleanup(lambda: self._killpg(decoy.pid))
        self.f.stale_lease()
        rc = CF.run_supervise(self.f.args(budget=4.0, turn_seconds=1.0))
        self.assertEqual(rc, 0)
        status = self.f.read_status()
        self.assertGreaterEqual(status["bounded_turns_started"], 2)
        # The unrelated process was never touched.
        os.kill(decoy.pid, 0)
        try:
            last = int(self.f.read_lease().get("model_pid"))
            self.f.children.append(last)
        except (TypeError, ValueError):
            pass

    def test_dirty_root_blocks_stop_until_clean(self):
        self.f.stale_lease()
        done = []
        t = threading.Thread(target=lambda: done.append(
            CF.run_supervise(self.f.args(budget=30.0))), daemon=True)
        t.start()
        self.assertTrue(self.wait_for(lambda: self.lease_owner_is("muse")))
        pid = int(self.f.read_lease()["model_pid"])
        self.f.children.append(pid)
        (self.f.proj / "dirty.txt").write_text("uncommitted\n")
        (self.f.control / "return-to-codex.json").write_text(
            json.dumps({"requested": "test"}))
        time.sleep(1.5)
        # Still running: a dirty tree is not a safe boundary.
        os.kill(pid, 0)
        self.assertIn("waiting_for_safe_boundary",
                      self.f.read_status().get("note", ""))
        (self.f.proj / "dirty.txt").unlink()
        self.assertTrue(self.wait_for(lambda: self.lease_owner_is("codex")))
        with self.assertRaises(OSError):
            os.kill(pid, 0)
        lease = self.f.read_lease()
        self.assertEqual(lease.get("owner"), "codex")
        # End the watching supervisor through the pause marker.
        (self.f.control / "pool-paused.json").write_text('{"status":"x"}\n')
        t.join(timeout=20)
        self.assertFalse(t.is_alive())
        self.assertEqual(done, [0])

    def test_crash_restart_adopts_without_duplicate(self):
        self.f.stale_lease()
        first = []
        t = threading.Thread(target=lambda: first.append(
            CF.run_supervise(self.f.args(budget=2.0))), daemon=True)
        t.start()
        self.assertTrue(self.wait_for(lambda: self.lease_owner_is("muse")))
        pid = int(self.f.read_lease()["model_pid"])
        slot = self.f.read_lease()["slot"]
        t.join(timeout=10)
        # Supervisor budget ended; the fallback still lives. A restarted
        # supervisor must adopt it, not start a second one.
        rc = CF.run_supervise(self.f.args(budget=2.0))
        self.assertEqual(rc, 0)
        self.assertEqual(int(self.f.read_lease()["model_pid"]), pid)
        self.assertEqual(self.f.read_lease()["slot"], slot)
        self.assertEqual(self.f.read_status()["bounded_turns_started"], 0)
        self.f.children.append(pid)

    def _killpg(self, pid):
        try:
            os.killpg(pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError, OSError):
            pass
        try:
            os.waitpid(pid, 0)
        except (ChildProcessError, OSError):
            pass


class ClosureTest(unittest.TestCase):
    """Lane 636 closure: kernel-lock proof for the four required gaps."""

    def setUp(self):
        self.f = Fixture()

    def tearDown(self):
        try:
            self.f.track_children_from_lease()
            try:
                gpid = self.f.read_lease().get("guardian_pid")
            except (FileNotFoundError, ValueError, OSError):
                gpid = None
            if gpid:
                try:
                    os.killpg(int(gpid), signal.SIGKILL)
                except (ProcessLookupError, PermissionError, OSError):
                    pass
                try:
                    os.kill(int(gpid), signal.SIGKILL)
                except (ProcessLookupError, PermissionError, OSError):
                    pass
        finally:
            self.f.close()
        self.f.reap()

    def wait_for(self, pred, timeout=10.0):
        end = time.monotonic() + timeout
        while time.monotonic() < end:
            try:
                if pred():
                    return True
            except (FileNotFoundError, ValueError, OSError):
                pass
            time.sleep(0.05)
        return False

    def test_slot_survives_supervisor_exit_and_refuses_16th(self):
        self.f.stale_lease()
        done = []
        t = threading.Thread(target=lambda: done.append(
            CF.run_supervise(self.f.args(budget=1.5))), daemon=True)
        t.start()
        self.assertTrue(self.wait_for(
            lambda: self.f.read_lease().get("owner") == "muse"))
        lease = self.f.read_lease()
        pid = int(lease["model_pid"])
        slot = int(lease["slot"])
        gpid = lease.get("guardian_pid")
        self.assertIsNotNone(gpid)
        self.f.children.append(pid)
        t.join(timeout=10)
        self.assertFalse(t.is_alive())
        # Supervisor exited on budget; fallback and guardian still live.
        os.kill(pid, 0)
        os.kill(int(gpid), 0)
        # The recorded slot is still kernel-held: same-slot re-lock fails.
        probe = open(CF.slot_path(str(self.f.pool), slot), "a")
        with probe:
            self.assertRaises(BlockingIOError, fcntl.flock, probe,
                              fcntl.LOCK_EX | fcntl.LOCK_NB)
        # All remaining 14 slots can be taken, but a 16th model is refused:
        # with 14 held here plus the inherited one, no slot is free.
        held = []
        try:
            for s in range(1, 16):
                if s == slot:
                    continue
                fh = open(CF.slot_path(str(self.f.pool), s), "a")
                fcntl.flock(fh, fcntl.LOCK_EX | fcntl.LOCK_NB)
                held.append(fh)
            self.assertEqual(len(held), 14)
            extra_slot, extra_fh = CF.reserve_slot(str(self.f.pool))
            self.assertIsNone(extra_slot)
            self.assertIsNone(extra_fh)
        finally:
            for fh in held:
                fh.close()
        # Crash adoption recognises the still-held slot: no duplicate, no
        # different slot, zero new turns.
        rc = CF.run_supervise(self.f.args(budget=1.5))
        self.assertEqual(rc, 0)
        self.assertEqual(int(self.f.read_lease()["model_pid"]), pid)
        self.assertEqual(int(self.f.read_lease()["slot"]), slot)
        self.assertEqual(self.f.read_status()["bounded_turns_started"], 0)

    def test_group_strays_keep_slot_until_all_gone(self):
        self.f.stale_lease()
        done = []
        t = threading.Thread(target=lambda: done.append(
            CF.run_supervise(self.f.args(budget=30.0))), daemon=True)
        t.start()
        self.assertTrue(self.wait_for(
            lambda: self.f.read_lease().get("owner") == "muse"))
        lease = self.f.read_lease()
        pid = int(lease["model_pid"])
        slot = int(lease["slot"])
        self.f.children.append(pid)
        # Direct fallback has a same-group tool child (sh -> sleep): kill
        # ONLY the leader, leaving the orphaned grandchild in the group.
        try:
            os.kill(pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError, OSError):
            pass
        time.sleep(1.0)
        members = CF.group_members(pid, "/proc",
                                   exclude=(os.getpid(),))
        # The orphaned tool child keeps the group alive (real kernel scan).
        self.assertTrue(members)
        # Slot is still held by the guardian copy despite the dead leader.
        probe = open(CF.slot_path(str(self.f.pool), slot), "a")
        with probe:
            self.assertRaises(BlockingIOError, fcntl.flock, probe,
                              fcntl.LOCK_EX | fcntl.LOCK_NB)
        # Supervisor observes strays and keeps the lease; it must not hand
        # back or free the slot while descendants live.
        time.sleep(1.0)
        status = self.f.read_status()
        self.assertIn("descendants_remain", status.get("note", ""))
        # Drain every remaining group member; only then may the slot free.
        for m in members:
            try:
                os.kill(m, signal.SIGKILL)
            except (ProcessLookupError, PermissionError, OSError):
                pass
        try:
            os.killpg(pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError, OSError):
            pass
        self.assertTrue(self.wait_for(
            lambda: not CF.group_members(pid, "/proc",
                                         exclude=(os.getpid(),)),
            timeout=15.0))
        # Guardian exits on the empty group; the slot becomes free.
        self.assertTrue(self.wait_for(
            lambda: CF.lock_slot(str(self.f.pool), slot) is not None
            or not CF.group_members(pid, "/proc",
                                    exclude=(os.getpid(),)),
            timeout=15.0))
        fh = CF.lock_slot(str(self.f.pool), slot)
        if fh is not None:
            fh.close()
        (self.f.control / "pool-paused.json").write_text('{"status":"x"}\n')
        t.join(timeout=20)
        self.assertFalse(t.is_alive())

    def test_busy_action_blocks_kill_until_released(self):
        self.f.stale_lease()
        done = []
        t = threading.Thread(target=lambda: done.append(
            CF.run_supervise(self.f.args(budget=30.0))), daemon=True)
        t.start()
        self.assertTrue(self.wait_for(
            lambda: self.f.read_lease().get("owner") == "muse"))
        pid = int(self.f.read_lease()["model_pid"])
        self.f.children.append(pid)
        # Simulate a busy integration holding the action lock for its
        # whole run (actual kernel flock, not a probe).
        busy = open(self.f.control / "foreground-action.lock", "a")
        fcntl.flock(busy, fcntl.LOCK_EX)
        try:
            (self.f.control / "return-to-codex.json").write_text(
                json.dumps({"requested": "test"}))
            time.sleep(1.5)
            # Still alive: the supervisor holds no kill across the busy
            # tool; it waits at the safe boundary instead.
            os.kill(pid, 0)
            self.assertIn("waiting_for_safe_boundary",
                          self.f.read_status().get("note", ""))
            self.assertEqual(self.f.read_lease().get("owner"), "muse")
        finally:
            fcntl.flock(busy, fcntl.LOCK_UN)
            busy.close()
        # Released: the supervisor now holds the boundary locks across
        # the termination and hands back.
        self.assertTrue(self.wait_for(
            lambda: self.f.read_lease().get("owner") == "codex",
            timeout=45.0))
        with self.assertRaises(OSError):
            os.kill(pid, 0)
        (self.f.control / "pool-paused.json").write_text('{"status":"x"}\n')
        t.join(timeout=20)
        self.assertFalse(t.is_alive())
        self.assertEqual(done, [0])

    def test_busy_watch_requests_pause_and_kills_nothing_foreign(self):
        decoy = subprocess.Popen(["sleep", "30"], start_new_session=True)
        self.addCleanup(lambda: self._killpg(decoy.pid))
        self.f.stale_lease()
        done = []
        t = threading.Thread(target=lambda: done.append(
            CF.run_supervise(self.f.args(budget=30.0))), daemon=True)
        t.start()
        self.assertTrue(self.wait_for(
            lambda: self.f.read_lease().get("owner") == "muse"))
        pid = int(self.f.read_lease()["model_pid"])
        self.f.children.append(pid)
        busy = open(self.f.control / "watch.lock", "a")
        fcntl.flock(busy, fcntl.LOCK_EX)
        try:
            (self.f.control / "return-to-codex.json").write_text(
                json.dumps({"requested": "test"}))
            time.sleep(1.5)
            os.kill(pid, 0)
            os.kill(decoy.pid, 0)
            self.assertIn("waiting_for_safe_boundary",
                          self.f.read_status().get("note", ""))
            # Watch-busy requests the supervisor-owned pause boundary.
            self.assertTrue(
                (self.f.control / "coordinator-pause.json").is_file())
        finally:
            fcntl.flock(busy, fcntl.LOCK_UN)
            busy.close()
        self.assertTrue(self.wait_for(
            lambda: self.f.read_lease().get("owner") == "codex",
            timeout=45.0))
        with self.assertRaises(OSError):
            os.kill(pid, 0)
        # Foreign watcher/user group never signalled; owned pause restored.
        os.kill(decoy.pid, 0)
        self.assertFalse(
            (self.f.control / "coordinator-pause.json").is_file())
        (self.f.control / "pool-paused.json").write_text('{"status":"x"}\n')
        t.join(timeout=20)
        self.assertFalse(t.is_alive())

    def test_full_pool_keeps_dispatcher_stopped_without_churn(self):
        self.f.stale_lease()
        (self.f.pool / "locks").mkdir(parents=True, exist_ok=True)
        held = []
        for slot in range(1, 16):
            fh = open(CF.slot_path(str(self.f.pool), slot), "a")
            fcntl.flock(fh, fcntl.LOCK_EX | fcntl.LOCK_NB)
            held.append(fh)
        done = []
        try:
            t = threading.Thread(target=lambda: done.append(
                CF.run_supervise(self.f.args(budget=6.0))), daemon=True)
            t.start()
            time.sleep(2.5)
            calls = self.f.coord_calls()
            stops = [c for c in calls if c == "coord dispatch_stop"]
            starts = [c for c in calls if c == "coord dispatch_start"]
            # Exactly one stop, no start churn while awaiting the slot.
            self.assertEqual(len(stops), 1)
            self.assertEqual(len(starts), 0)
            self.assertEqual(self.f.read_status()["note"],
                             "slot_exhausted_dispatcher_held")
            # Free one slot: the held dispatcher reservation lets the
            # fallback take it without a provider storm.
            held[0].close()
            del held[0]
            self.assertTrue(self.wait_for(
                lambda: self.f.read_lease().get("owner") == "muse",
                timeout=10.0))
            try:
                self.f.track_children_from_lease()
            except (FileNotFoundError, ValueError, OSError):
                pass
            t.join(timeout=15)
            self.assertFalse(t.is_alive())
            calls = self.f.coord_calls()
            starts = [c for c in calls if c == "coord dispatch_start"]
            self.assertTrue(starts)
        finally:
            for fh in held:
                try:
                    fh.close()
                except OSError:
                    pass

    def _killpg(self, pid):
        try:
            os.killpg(pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError, OSError):
            pass
        try:
            os.waitpid(pid, 0)
        except (ChildProcessError, OSError):
            pass


class PauseDistinctionTest(unittest.TestCase):
    """Lane 636 repair (review 637): user pause vs internal marker.

    Only pool-paused.json (explicit user pause) may block takeover, stop
    the role, or exit the supervisor. coordinator-pause.json (internal
    transient registration / own safe-boundary request) must never do any
    of the three, and a leftover supervisor-owned marker must expire.
    """

    def setUp(self):
        self.f = Fixture()

    def tearDown(self):
        try:
            self.f.track_children_from_lease()
            try:
                gpid = self.f.read_lease().get("guardian_pid")
            except (FileNotFoundError, ValueError, OSError):
                gpid = None
            if gpid:
                try:
                    os.killpg(int(gpid), signal.SIGKILL)
                except (ProcessLookupError, PermissionError, OSError):
                    pass
                try:
                    os.kill(int(gpid), signal.SIGKILL)
                except (ProcessLookupError, PermissionError, OSError):
                    pass
        finally:
            self.f.close()
        self.f.reap()

    def wait_for(self, pred, timeout=10.0):
        end = time.monotonic() + timeout
        while time.monotonic() < end:
            try:
                if pred():
                    return True
            except (FileNotFoundError, ValueError, OSError):
                pass
            time.sleep(0.05)
        return False

    def _start_fallback(self, budget=30.0):
        self.f.stale_lease()
        done = []
        t = threading.Thread(target=lambda: done.append(
            CF.run_supervise(self.f.args(budget=budget))), daemon=True)
        t.start()
        self.assertTrue(self.wait_for(
            lambda: self.f.read_lease().get("owner") == "muse"))
        pid = int(self.f.read_lease()["model_pid"])
        self.f.children.append(pid)
        return t, done, pid

    def _stop_thread(self, t, done):
        (self.f.control / "pool-paused.json").write_text('{"status":"x"}\n')
        t.join(timeout=30)
        self.assertFalse(t.is_alive())
        self.assertEqual(done, [0])

    def test_internal_marker_never_stops_live_role(self):
        t, done, pid = self._start_fallback()
        try:
            (self.f.control / "coordinator-pause.json").write_text(
                json.dumps({"owner": "register_tasks-999",
                            "requested": "2026-01-01T00:00:00+00:00"}))
            time.sleep(2.5)
            os.kill(pid, 0)
            self.assertEqual(self.f.read_lease().get("owner"), "muse")
            self.assertNotIn("paused_by_coordinator-pause",
                             self.f.read_status().get("note", ""))
        finally:
            try:
                (self.f.control / "coordinator-pause.json").unlink()
            except OSError:
                pass
            self._stop_thread(t, done)
        with self.assertRaises(OSError):
            os.kill(pid, 0)

    def test_internal_marker_never_blocks_takeover(self):
        (self.f.control / "coordinator-pause.json").write_text(
            json.dumps({"owner": "register_tasks-999",
                        "requested": "2026-01-01T00:00:00+00:00"}))
        self.f.stale_lease()
        rc = CF.run_supervise(self.f.args(budget=3.0))
        self.assertEqual(rc, 0)
        self.assertEqual(self.f.read_lease().get("owner"), "muse")
        self.assertGreaterEqual(
            self.f.read_status()["bounded_turns_started"], 1)
        self.f.track_children_from_lease()

    def test_stale_own_pause_cleaned_and_never_blocks(self):
        (self.f.control / "coordinator-pause.json").write_text(
            json.dumps({"owner": "failover-99999999",
                        "requested": "2020-01-01T00:00:00+00:00",
                        "reason": "leftover from a dead supervisor"}))
        self.f.stale_lease()
        rc = CF.run_supervise(self.f.args(budget=3.0))
        self.assertEqual(rc, 0)
        self.assertEqual(self.f.read_lease().get("owner"), "muse")
        self.assertFalse(
            (self.f.control / "coordinator-pause.json").is_file())
        self.f.track_children_from_lease()

    def test_foreign_marker_untouched_but_never_blocks(self):
        marker = json.dumps({"owner": "register_tasks-999",
                             "requested": "2026-01-01T00:00:00+00:00"})
        (self.f.control / "coordinator-pause.json").write_text(marker)
        self.f.stale_lease()
        rc = CF.run_supervise(self.f.args(budget=3.0))
        self.assertEqual(rc, 0)
        self.assertEqual(self.f.read_lease().get("owner"), "muse")
        self.assertEqual(
            (self.f.control / "coordinator-pause.json").read_text(), marker)
        self.f.track_children_from_lease()
        try:
            (self.f.control / "coordinator-pause.json").unlink()
        except OSError:
            pass

    def test_internal_marker_during_busy_watch_then_removed(self):
        t, done, pid = self._start_fallback()
        busy = open(self.f.control / "watch.lock", "a")
        fcntl.flock(busy, fcntl.LOCK_EX)
        try:
            (self.f.control / "return-to-codex.json").write_text(
                json.dumps({"requested": "test"}))
            (self.f.control / "coordinator-pause.json").write_text(
                json.dumps({"owner": "register_tasks-999",
                            "requested": "2026-01-01T00:00:00+00:00"}))
            time.sleep(2.0)
            # Role survives: waiting at the safe boundary, not killed for
            # the internal registration marker.
            os.kill(pid, 0)
            self.assertEqual(self.f.read_lease().get("owner"), "muse")
            self.assertIn("waiting_for_safe_boundary",
                          self.f.read_status().get("note", ""))
            # Registration removes its marker; coverage continues.
            (self.f.control / "coordinator-pause.json").unlink()
            time.sleep(1.0)
            os.kill(pid, 0)
            self.assertEqual(self.f.read_lease().get("owner"), "muse")
        finally:
            fcntl.flock(busy, fcntl.LOCK_UN)
            busy.close()
        self.assertTrue(self.wait_for(
            lambda: self.f.read_lease().get("owner") == "codex",
            timeout=45.0))
        self.assertIn("stopped_at_boundary_return_requested",
                      self.f.read_status().get("note", ""))
        with self.assertRaises(OSError):
            os.kill(pid, 0)
        self._stop_thread(t, done)

    def test_user_pause_still_stops_live_role(self):
        t, done, pid = self._start_fallback()
        (self.f.control / "pool-paused.json").write_text('{"status":"x"}\n')
        t.join(timeout=45)
        self.assertFalse(t.is_alive())
        self.assertEqual(done, [0])
        with self.assertRaises(OSError):
            os.kill(pid, 0)
        self.assertEqual(self.f.read_lease().get("owner"), "codex")


class LaunchMessageEnvBackoffTest(unittest.TestCase):
    """Lane 706: deployed launcher defects (message, config pointer, backoff).

    The deployed supervisor started 27 bounded fallback turns that each
    exited 1: model_argv passed an attached --file but no positional
    message (the CLI vocabulary is MUST PROVIDE MESSAGE), the managed
    --pure/build/JSON/project shape was missing, no provider-config
    pointer existed, and the launch branch reset failures/backoff before
    the child proved productive so quick exits never backed off
    monotonically. All fixtures stay inside the clone; the strict stubs
    below mimic only the public CLI contract (never a real provider).
    """

    def setUp(self):
        self.f = Fixture()

    def tearDown(self):
        try:
            self.f.track_children_from_lease()
            try:
                gpid = self.f.read_lease().get("guardian_pid")
            except (FileNotFoundError, ValueError, OSError):
                gpid = None
            if gpid:
                try:
                    os.killpg(int(gpid), signal.SIGKILL)
                except (ProcessLookupError, PermissionError, OSError):
                    pass
                try:
                    os.kill(int(gpid), signal.SIGKILL)
                except (ProcessLookupError, PermissionError, OSError):
                    pass
        finally:
            self.f.close()
        self.f.reap()

    # -- strict stub scripts (public CLI contract only) --------------------

    STRICT_VALIDATE = (
        "import sys, json, os\n"
        "argv = sys.argv[1:]\n"
        "ok = True\nwhy = []\n"
        "for tok in ('--pure', '--model', '--agent', 'build',\n"
        "            '--format', 'json', '--dir', '--title', '--'):\n"
        "    if tok not in argv:\n"
        "        ok = False\nwhy.append('missing:' + tok)\n"
        "if '--' in argv:\n"
        "    tail = argv[argv.index('--') + 1:]\n"
        "    if not tail or not any(t.strip() for t in tail):\n"
        "        ok = False\nwhy.append('empty-message')\n"
        "rec = {'argv': argv, 'ok': ok, 'why': why}\n"
    )

    def _write_stub(self, name, log_name, mode):
        """A fake model binary whose name carries both identity markers.

        mode 'sleep': validate argv, log the attempt, sleep (a live child).
        mode 'quickexit': validate argv, log attempt with timestamp, exit 1.
        mode 'envdump': validate argv, dump the child env selection, sleep.
        Any argv without the managed flags or without a nonempty
        positional message after `--` exits 1 with MUST PROVIDE MESSAGE.
        """
        log = self.f.root / log_name
        if mode == "envdump":
            body = (
                "env = {k: os.environ.get(k) for k in (\n"
                "    'OPENCODE_CONFIG', 'OPENCODE_DB', 'TMPDIR',\n"
                "    'GABBRO_COORDINATOR_ROLE', 'GABBRO_COORDINATOR_EPOCH',\n"
                "    'OPENCODE_DISABLE_AUTOUPDATE')}\n"
                f"open({str(log)!r}, 'a').write("
                "json.dumps({'env': env, 'argv': argv}) + chr(10))\n"
                "import time as _t\n_t.sleep(30)\n"
            )
        elif mode == "quickexit":
            body = (
                "import time as _t\n"
                "rec['t'] = _t.time()\n"
                f"open({str(log)!r}, 'a').write("
                "json.dumps(rec) + chr(10))\n"
                "sys.exit(1)\n"
            )
        else:
            body = (
                f"open({str(log)!r}, 'a').write("
                "json.dumps(rec) + chr(10))\n"
                "if os.environ.get('STUB_NO_SLEEP') == '1':\n"
                "    sys.exit(0 if ok else 1)\n"
                "if not ok:\n"
                "    sys.stderr.write('error: MUST PROVIDE MESSAGE: '\n"
                "                     'positional coordination instruction '\n"
                "                     'required after --' + chr(10))\n"
                "    sys.exit(1)\n"
                "import time as _t\n_t.sleep(30)\n"
            )
        path = self.f.root / name
        path.write_text("#!/usr/bin/env python3\n" + self.STRICT_VALIDATE
                        + body)
        path.chmod(0o755)
        return path, log

    def _attempts(self, log):
        if not log.is_file():
            return []
        return [json.loads(line) for line in log.read_text().splitlines()]

    def wait_for(self, pred, timeout=10.0):
        end = time.monotonic() + timeout
        while time.monotonic() < end:
            try:
                if pred():
                    return True
            except (FileNotFoundError, ValueError, OSError):
                pass
            time.sleep(0.05)
        return False

    def _status(self):
        return json.loads(
            (self.f.control / "failover-status.json").read_text())

    # -- argv shape --------------------------------------------------------

    def test_model_argv_matches_managed_shape_with_message(self):
        args = self.f.args(prompt_file="/tmp/p.md")
        argv = CF.model_argv(args)
        self.assertEqual(argv[0], str(self.f.opencode))
        self.assertEqual(
            argv[1:13],
            ["run", "--pure", "--model", MODEL, "--agent", "build",
             "--format", "json", "--dir", str(self.f.proj), "--title",
             "gabbro-fallback-coordinator"])
        self.assertIn("--file", argv)
        sep = argv.index("--")
        self.assertGreater(sep, 12)
        tail = argv[sep + 1:]
        self.assertTrue(tail and all(t.strip() for t in tail),
                        "positional coordination message must be nonempty")
        self.assertEqual(tail, [CF.FALLBACK_MESSAGE])
        # Without a prompt file the message is still present.
        argv2 = CF.model_argv(self.f.args())
        self.assertNotIn("--file", argv2)
        self.assertEqual(argv2[-2:], ["--", CF.FALLBACK_MESSAGE])

    def test_strict_stub_rejects_absent_message(self):
        stub, _log = self._write_stub(
            f"{OPENCODE_NAME}-{MODEL}-strict.sh", "strict.log", "sleep")
        # The pre-706 shape (attached --file, no positional message) fails
        # exactly like the deployed launcher did.
        old = [str(stub), "run", "--model", MODEL,
               "--title", "gabbro-fallback-coordinator",
               "--file", "/tmp/prompt.md"]
        out = subprocess.run(old, text=True, capture_output=True, timeout=30)
        self.assertEqual(out.returncode, 1)
        self.assertIn("MUST PROVIDE MESSAGE", out.stderr)
        # The repaired argv passes the same strict contract (no sleep).
        env = dict(os.environ, STUB_NO_SLEEP="1")
        new = CF.model_argv(self.f.args(opencode=str(stub)))
        out2 = subprocess.run(new, text=True, capture_output=True, timeout=30,
                              env=env, cwd=str(self.f.proj),
                              stdin=subprocess.DEVNULL)
        self.assertEqual(out2.returncode, 0, out2.stderr)

    def test_full_launch_path_uses_message_through_subprocess(self):
        stub, log = self._write_stub(
            f"{OPENCODE_NAME}-{MODEL}-strict-live.sh", "live-argv.log",
            "sleep")
        self.f.stale_lease()
        done = []
        t = threading.Thread(target=lambda: done.append(
            CF.run_supervise(self.f.args(budget=30.0, opencode=str(stub)))),
            daemon=True)
        t.start()
        try:
            self.assertTrue(self.wait_for(
                lambda: self.f.read_lease().get("owner") == "muse",
                timeout=10.0))
            attempts = self._attempts(log)
            self.assertEqual(len(attempts), 1)
            self.assertTrue(attempts[0]["ok"], attempts[0]["why"])
            argv = attempts[0]["argv"]
            for tok in ("--pure", "--agent", "build", "--format", "json",
                        "--dir", "--title", "--"):
                self.assertIn(tok, argv)
            self.assertEqual(argv[argv.index("--") + 1:],
                             [CF.FALLBACK_MESSAGE])
            self.f.track_children_from_lease()
        finally:
            (self.f.control / "pool-paused.json").write_text('{"x":1}\n')
            t.join(timeout=20)
            self.assertFalse(t.is_alive())
            self.assertEqual(done, [0])

    # -- provider-config pointer -------------------------------------------

    def test_provider_config_pointer_forwarded_only_via_env(self):
        stub, log = self._write_stub(
            f"{OPENCODE_NAME}-{MODEL}-envdump.sh", "env.log", "envdump")
        pointer = self.f.root / "opencode-go.json"
        sentinel = '{"model":"muse-spark-testmodel-620"}\n'
        pointer.write_text(sentinel)
        self.f.stale_lease()
        done = []
        t = threading.Thread(target=lambda: done.append(
            CF.run_supervise(self.f.args(
                budget=30.0, opencode=str(stub),
                opencode_config=str(pointer)))), daemon=True)
        t.start()
        try:
            self.assertTrue(self.wait_for(
                lambda: self.f.read_lease().get("owner") == "muse",
                timeout=10.0))
            rows = self._attempts(log)
            self.assertEqual(len(rows), 1)
            env = rows[0]["env"]
            self.assertEqual(env["OPENCODE_CONFIG"], str(pointer))
            self.assertTrue(env["OPENCODE_DB"].startswith(
                str(self.f.control)))
            self.assertTrue(env["TMPDIR"].startswith(str(self.f.pool)))
            self.assertEqual(env["GABBRO_COORDINATOR_ROLE"], "muse")
            self.assertTrue(env["GABBRO_COORDINATOR_EPOCH"])
            # The pointer target is never read or copied: byte-identical,
            # and its contents appear in no lease, status or log.
            self.assertEqual(pointer.read_text(), sentinel)
            blob = (self.f.control / "failover-status.json").read_text()
            blob += json.dumps(self.f.read_lease())
            blob += (self.f.control / "fallback-model.log").read_text()
            self.assertNotIn("muse-spark-testmodel-620", blob)
            self.f.track_children_from_lease()
        finally:
            (self.f.control / "pool-paused.json").write_text('{"x":1}\n')
            t.join(timeout=20)
            self.assertFalse(t.is_alive())
            self.assertEqual(done, [0])

    def test_no_pointer_leaves_parent_env_untouched(self):
        had = "OPENCODE_CONFIG" in os.environ
        parent_val = os.environ.get("OPENCODE_CONFIG")
        got = CF.model_env(self.f.args(), "epoch-1")
        self.assertEqual("OPENCODE_CONFIG" in got, had)
        self.assertEqual(got.get("OPENCODE_CONFIG"), parent_val)

    # -- backoff ------------------------------------------------------------

    def test_next_backoff_monotonic_bounded(self):
        self.assertEqual(CF.next_backoff(5.0), 10.0)
        self.assertEqual(CF.next_backoff(10.0), 20.0)
        self.assertEqual(CF.next_backoff(20.0), 40.0)
        self.assertEqual(CF.next_backoff(150.0), 300.0)
        self.assertEqual(CF.next_backoff(1000.0), 300.0)
        self.assertEqual(CF.next_backoff(0.0), 10.0)

    def test_consecutive_quick_exits_back_off_monotonically(self):
        stub, log = self._write_stub(
            f"{OPENCODE_NAME}-{MODEL}-quickexit.sh", "quick.log",
            "quickexit")
        self.f.stale_lease()
        start = time.monotonic()
        rc = CF.run_supervise(self.f.args(budget=16.0, opencode=str(stub)))
        elapsed = time.monotonic() - start
        self.assertEqual(rc, 0)
        status = self._status()
        # Two genuine launches ~10 s apart: backoff, not a storm.
        self.assertEqual(status["bounded_turns_started"], 2)
        attempts = self._attempts(log)
        self.assertEqual(len(attempts), 2)
        for rec in attempts:
            self.assertTrue(rec["ok"], rec["why"])
        gap = attempts[1]["t"] - attempts[0]["t"]
        self.assertGreaterEqual(gap, 8.0)
        self.assertLess(len(attempts), 4)
        self.assertGreaterEqual(elapsed, 12.0)
        self.assertIn("backing_off", status.get("note", ""))
        self.assertGreaterEqual(status.get("consecutive_failures", 0), 1)
        # Dispatcher stop/start stays 1:1 with launches: no churn.
        calls = self.f.coord_calls()
        self.assertTrue(all(c in ("coord dispatch_stop",
                                  "coord dispatch_start") for c in calls))
        self.assertEqual(len([c for c in calls
                              if c == "coord dispatch_stop"]), 2)
        self.assertEqual(len([c for c in calls
                              if c == "coord dispatch_start"]), 2)

    def test_fresh_foreground_cancels_retry_then_pause_exits_promptly(self):
        import datetime
        stub, log = self._write_stub(
            f"{OPENCODE_NAME}-{MODEL}-quickexit2.sh", "quick2.log",
            "quickexit")
        self.f.stale_lease()
        done = []
        t = threading.Thread(target=lambda: done.append(
            CF.run_supervise(self.f.args(budget=30.0, opencode=str(stub)))),
            daemon=True)
        t.start()
        try:
            self.assertTrue(self.wait_for(
                lambda: self._status().get("consecutive_failures", 0) >= 1,
                timeout=10.0))
            # Fresh foreground heartbeat during backoff: the pending retry
            # must not fire even after the backoff delay elapses.
            hb = (datetime.datetime.now(datetime.timezone.utc)).isoformat()
            (self.f.control / "orchestrator-lease.json").write_text(
                json.dumps({"owner": "codex", "heartbeat": hb,
                            "timeout_seconds": 300.0}))
            time.sleep(12.0)
            self.assertEqual(self._status()["bounded_turns_started"], 1)
            self.assertEqual(len(self._attempts(log)), 1)
            # User pause then exits promptly: well before any new retry.
            begin = time.monotonic()
            (self.f.control / "pool-paused.json").write_text('{"x":1}\n')
            t.join(timeout=12)
            waited = time.monotonic() - begin
            self.assertFalse(t.is_alive())
            self.assertLess(waited, 8.0)
            self.assertEqual(done, [0])
            self.assertEqual(self._status()["status"], "paused_no_takeover")
            self.assertEqual(self._status()["bounded_turns_started"], 1)
            calls = self.f.coord_calls()
            self.assertTrue(all(c in ("coord dispatch_stop",
                                      "coord dispatch_start") for c in calls))
            stops = [c for c in calls if c == "coord dispatch_stop"]
            starts = [c for c in calls if c == "coord dispatch_start"]
            self.assertGreaterEqual(len(starts), len(stops))
        finally:
            if t.is_alive():
                (self.f.control / "pool-paused.json").write_text('{"x":1}\n')
                t.join(timeout=15)


if __name__ == "__main__":
    unittest.main(verbosity=2)
