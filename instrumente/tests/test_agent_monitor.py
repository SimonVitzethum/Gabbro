#!/usr/bin/env python3
"""Tests for instrumente/agent-monitor.py (lane 595).

Fixture dirs live inside the clone (never /tmp). Standard library only.
Run: python3 instrumente/tests/test_agent_monitor.py
"""
import importlib.util
import json
import os
import tempfile
import unittest
from pathlib import Path

MONITOR = Path(__file__).resolve().parents[1] / "agent-monitor.py"
CLONE_TMP = Path(__file__).resolve().parents[2] / ".tmp"
MODEL = "opencode-go/muse-spark-1.3-contributor"


def load_monitor():
    spec = importlib.util.spec_from_file_location("agent_monitor", str(MONITOR))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


AM = load_monitor()


class Fixture:
    def __init__(self):
        CLONE_TMP.mkdir(exist_ok=True)
        self.tmp = tempfile.TemporaryDirectory(prefix="mon595-", dir=str(CLONE_TMP))
        self.root = Path(self.tmp.name)
        self.state_dir = self.root / "state"
        self.proc_root = self.root / "proc"
        self.log_dir = self.root / "logs"
        self.report_dir = self.root / "reports"
        for d in (self.state_dir, self.proc_root, self.log_dir, self.report_dir):
            d.mkdir(parents=True, exist_ok=True)
        self.manifest_path = self.root / "manifest.json"
        self.status_out = self.root / "status.json"
        self.events_out = self.root / "events.jsonl"
        self.seen_file = self.root / "seen.json"
        (self.proc_root / "meminfo").write_text("MemAvailable:       16000000 kB\n")

    def close(self):
        self.tmp.cleanup()

    def write_manifest(self, lanes, reviews=None, max_active=15):
        self.manifest_path.write_text(json.dumps({
            "model": MODEL, "max_active": max_active,
            "lanes": lanes, "peer_reviews": reviews or [],
        }))

    def write_state(self, lane, **fields):
        doc = {"lane": lane, "status": "ready"}
        doc.update(fields)
        (self.state_dir / f"{lane}.json").write_text(json.dumps(doc))

    def write_proc(self, pid, cmdline: bytes):
        d = self.proc_root / str(pid)
        d.mkdir(exist_ok=True)
        (d / "cmdline").write_bytes(cmdline)

    def args(self, **over):
        ns = dict(state_dir=str(self.state_dir), manifest=str(self.manifest_path),
                  proc_root=str(self.proc_root), interval=60.0, once=True,
                  status_out=str(self.status_out), events_out=str(self.events_out),
                  seen_file=str(self.seen_file), pause_file=None, model_substr=None,
                  max_active=None, stale_secs=1800.0, mem_reserve_kib=8 * 1024 * 1024,
                  log_dir=str(self.log_dir), report_dir=str(self.report_dir))
        ns.update(over)
        return type("A", (), ns)()

    def run(self, **over):
        return AM.run_once(self.args(**over))

    def events(self):
        if not self.events_out.is_file():
            return []
        return [json.loads(x) for x in self.events_out.read_text().splitlines() if x.strip()]

    def status(self):
        return json.loads(self.status_out.read_text())


def lanes(*ids):
    return [{"lane": n, "title": f"lane {n}", "status": "ready", "kind": "lean"} for n in ids]


class MonitorTest(unittest.TestCase):
    def setUp(self):
        self.f = Fixture()

    def tearDown(self):
        self.f.close()

    def test_clean_running_counts_model_vs_runner(self):
        self.f.write_manifest(lanes(601), max_active=15)
        self.f.write_proc(111, b"python\x00coordinate.py\x00run\x00601\x00")
        self.f.write_proc(222, b"opencode\x00run\x00--title\x00muse-x86-601\x00")
        self.f.write_state(601, status="running", runner_pid=111, model_pid=222,
                           updated="2999-01-01T00:00:00+00:00")
        (self.f.log_dir / "601.log").write_text("x")
        status, events = self.f.run()
        by = {x["lane"]: x for x in status["lanes"]}[601]
        self.assertTrue(by["runner_alive"])
        self.assertTrue(by["model_alive"])
        self.assertFalse(by["dead"])
        self.assertEqual(status["counts"]["model_alive"], 1)
        self.assertEqual(status["counts"]["runner_alive"], 1)
        self.assertEqual(events, [])

    def test_finished_completion_with_verdict_and_dedup(self):
        self.f.write_manifest(lanes(602))
        head = "ab" * 20
        self.f.write_state(602, status="report_ready", candidate_refs={"602": head},
                           updated="2026-10-01T10:00:00+00:00")
        (self.f.report_dir / "MUSE-REPORT-602.md").write_text(
            f"work done\nCANDIDATE: 602 {head}\nVERDICT: ACCEPT\n")
        _, e1 = self.f.run()
        self.assertEqual(len(e1), 1)
        self.assertEqual(e1[0]["kind"], "completion")
        self.assertEqual(e1[0]["lane"], 602)
        self.assertEqual(e1[0]["verdict"], "ACCEPT")
        self.assertEqual(e1[0]["head"], {"602": head})
        _, e2 = self.f.run()
        self.assertEqual(e2, [])
        self.assertEqual(len(self.f.events()), 1)

    def test_no_verdict_inferred_from_build_alone(self):
        self.f.write_manifest(lanes(603))
        self.f.write_state(603, status="report_ready", updated="2026-10-01T10:00:00+00:00")
        _, events = self.f.run(report_dir=None)
        self.assertEqual(len(events), 1)
        self.assertIsNone(events[0]["verdict"])
        self.assertIsNone(events[0]["head"])

    def test_dead_process_detected(self):
        self.f.write_manifest(lanes(604))
        self.f.write_state(604, status="running", runner_pid=99991, model_pid=99992,
                           updated="2999-01-01T00:00:00+00:00")
        status, events = self.f.run()
        by = {x["lane"]: x for x in status["lanes"]}[604]
        self.assertTrue(by["dead"])
        self.assertFalse(by["model_alive"])
        kinds = {b["kind"] for b in status["blockers"] if b["lane"] == 604}
        self.assertIn("dead", kinds)
        self.assertTrue(any(e["kind"] == "dead" for e in events))

    def test_reused_pid_mismatch_not_counted(self):
        self.f.write_manifest(lanes(605))
        self.f.write_proc(333, b"init\x00")
        self.f.write_state(605, status="running", runner_pid=333, model_pid=333,
                           updated="2999-01-01T00:00:00+00:00")
        status, _ = self.f.run()
        by = {x["lane"]: x for x in status["lanes"]}[605]
        self.assertFalse(by["runner_alive"])
        self.assertFalse(by["model_alive"])
        self.assertTrue(by["wrong_model_or_reused_pid"])
        kinds = {b["kind"] for b in status["blockers"] if b["lane"] == 605}
        self.assertIn("reused_pid", kinds)
        self.assertEqual(status["counts"]["model_alive"], 0)

    def test_wrong_model_marker(self):
        self.f.write_manifest(lanes(606))
        self.f.write_proc(444, b"other-tool\x00run\x00606\x00")
        self.f.write_state(606, status="running", model_pid=444,
                           updated="2999-01-01T00:00:00+00:00")
        status, _ = self.f.run()
        by = {x["lane"]: x for x in status["lanes"]}[606]
        self.assertFalse(by["model_alive"])
        self.assertEqual(by["model_identity"], "mismatch")

    def test_paused_stops_auto_actions(self):
        self.f.write_manifest(lanes(607))
        self.f.write_state(607, status="ready")
        pause = self.f.root / "pool-paused.json"
        pause.write_text('{"by": "simon"}')
        status, _ = self.f.run(pause_file=str(pause))
        self.assertTrue(status["paused"])
        self.assertEqual(status["pause_file"], str(pause))
        kinds = {b["kind"] for b in status["blockers"] if b["lane"] is None}
        self.assertIn("paused", kinds)

    def test_restart_dedup_across_seen_reload(self):
        self.f.write_manifest(lanes(608))
        self.f.write_state(608, status="report_ready", updated="2026-10-01T10:00:00+00:00")
        _, e1 = self.f.run()
        self.assertEqual(len(e1), 1)
        seen = json.loads(self.f.seen_file.read_text())
        self.assertIn("608", seen)
        _, e2 = self.f.run()
        self.assertEqual(e2, [])

    def test_dependency_blocker_and_under_utilisation(self):
        self.f.write_manifest(lanes(609, 610), reviews=[{"reviewer": 610, "authors": [609]}])
        self.f.write_state(609, status="running", updated="2999-01-01T00:00:00+00:00")
        self.f.write_state(610, status="ready", updated="2999-01-01T00:00:00+00:00")
        status, _ = self.f.run()
        deps = [b for b in status["blockers"] if b["kind"] == "dependency" and b["lane"] == 610]
        self.assertTrue(deps)
        self.assertTrue(status["under_utilised"])
        self.assertIn(610, status["pending"])

    def test_stalled_heartbeat(self):
        self.f.write_manifest(lanes(611))
        self.f.write_proc(555, b"python\x00coordinate.py\x00run\x00611\x00")
        self.f.write_state(611, status="running", runner_pid=555,
                           updated="2020-01-01T00:00:00+00:00")
        old_log = self.f.log_dir / "611.log"
        old_log.write_text("old")
        os.utime(old_log, (1_000_000_000, 1_000_000_000))
        status, events = self.f.run(stale_secs=60.0)
        by = {x["lane"]: x for x in status["lanes"]}[611]
        self.assertTrue(by["stalled"])
        self.assertTrue(any(e["kind"] == "stalled" for e in events))

    def test_unreadable_cmdline_fails_closed(self):
        self.f.write_manifest(lanes(612))
        d = self.f.proc_root / "777"
        d.mkdir(exist_ok=True)
        (d / "cmdline").mkdir()
        self.f.write_state(612, status="running", model_pid=777,
                           updated="2999-01-01T00:00:00+00:00")
        status, _ = self.f.run()
        by = {x["lane"]: x for x in status["lanes"]}[612]
        self.assertTrue(by["model_alive"])
        self.assertEqual(by["model_identity"], "unknown")


if __name__ == "__main__":
    unittest.main(verbosity=2)
