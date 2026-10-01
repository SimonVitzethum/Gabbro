#!/usr/bin/env python3
"""Tests for instrumente/lane-cleanup.py (lane 622). Standard library only.

Fixtures live inside the clone (.tmp/), never /tmp. No live pool deletion.
Run: python3 instrumente/tests/test_lane_cleanup.py
"""
import hashlib
import importlib.util
import json
import os
import tempfile
import unittest
from pathlib import Path

TOOL = Path(__file__).resolve().parents[1] / "lane-cleanup.py"
CLONE_TMP = Path(__file__).resolve().parents[2] / ".tmp"


def load_tool():
    spec = importlib.util.spec_from_file_location("lane_cleanup", str(TOOL))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


LC = load_tool()


class Fixture:
    def __init__(self):
        CLONE_TMP.mkdir(exist_ok=True)
        self.tmp = tempfile.TemporaryDirectory(prefix="lc622-", dir=str(CLONE_TMP))
        self.root = Path(self.tmp.name)
        self.project = self.root / "proj"
        self.control = self.root / "ctrl"
        self.pool = self.root / "pool"
        self.proc = self.root / "proc"
        for d in (self.project, self.control, self.pool, self.proc):
            d.mkdir(parents=True, exist_ok=True)
        (self.control / "tasks").mkdir(exist_ok=True)
        (self.control / "state").mkdir(exist_ok=True)

    def close(self):
        self.tmp.cleanup()

    def manifest(self, lanes, reviews=None):
        (self.control / "manifest.json").write_text(json.dumps(
            {"lanes": lanes, "peer_reviews": reviews or []}))

    def state(self, lane, **fields):
        doc = {"lane": lane, "status": "ready"}
        doc.update(fields)
        (self.control / "state" / ("%d.json" % lane)).write_text(json.dumps(doc))

    def prompt(self, lane, text="HARD RULES\n# Lane %d\n"):
        bodies = {}
        targets = [
            self.project / "lanes" / ("%d.md" % lane),
            self.control / "tasks" / ("%d.md" % lane),
            self.project / ".claude" / "muse-arbeit" / "lanes5" / ("%d.md" % lane),
            self.project / ".claude" / "muse-sicherung" / ("%d.md" % lane),
            self.pool / "lanes" / ("%d.md" % lane),
            self.pool / ("a%d" % lane) / ".tmp" / "LANE.md",
        ]
        for path in targets:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text % lane if "%d" in text else text)
            bodies[str(path)] = path.read_bytes()
        return bodies

    def report(self, lane):
        path = self.project / "messung" / "muse" / ("MUSE-REPORT-%d.md" % lane)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("# report %d\nVERDICT: ACCEPT\n" % lane)
        return path

    def fake_proc(self, pid, live=True, zombie=False, start="12345"):
        d = self.proc / str(pid)
        d.mkdir(exist_ok=True)
        state = "Z" if zombie else "S"
        (d / "stat").write_text("1 (fake) %s 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 %s" % (state, start))
        (d / "cmdline").write_bytes(b"\x00" if not live else b"opencode\x00lane\x00")


class PlanCase(unittest.TestCase):
    def setUp(self):
        self.fx = Fixture()

    def tearDown(self):
        self.fx.close()

    def test_merged_lane_is_deletable(self):
        self.fx.manifest([{"lane": 601}])
        self.fx.state(601, status="merged")
        self.fx.prompt(601)
        self.fx.report(601)
        plan = LC.build_plan(self.fx.project, self.fx.control, self.fx.pool,
                             str(self.fx.proc), {"lanes": [{"lane": 601}],
                                                 "peer_reviews": []},
                             {601: {"status": "merged"}}, [601], {}, None, 50,
                             self.fx.project)
        lane = plan["lanes"][0]
        self.assertTrue(lane["deletable"], lane)


    def test_nonfinal_statuses_are_not_final(self):
        for status in ["report_ready", "incomplete", "runner_error", "paused",
                       "waiting_for_review", "needs_coordinator_fallback"]:
            ok, _why, _d = LC.completion_of(602, {"status": status})
            self.assertFalse(ok, status)

    def test_abandoned_needs_durable_flag(self):
        ok, _, _ = LC.completion_of(603, {"status": "abandoned"})
        self.assertFalse(ok)
        ok, why, _ = LC.completion_of(603, {"status": "abandoned", "terminal": True})
        self.assertTrue(ok, why)
        ok, _, _ = LC.completion_of(603, {"status": "final_refused",
                                          "durable_terminal": True})
        self.assertTrue(ok)

    def test_running_identity_blocks_merged_lane(self):
        self.fx.fake_proc(4242, live=True, start="999")
        state = {"status": "merged", "model_pid": 4242,
                 "model_start_ticks": "999"}
        self.assertEqual(len(LC.live_identities(state, str(self.fx.proc))), 1)
        plan = LC.build_plan(self.fx.project, self.fx.control, self.fx.pool,
                             str(self.fx.proc), {"lanes": [{"lane": 604}],
                                                 "peer_reviews": []},
                             {604: state}, [604], {}, None, 50, self.fx.project)
        self.assertFalse(plan["lanes"][0]["deletable"])
        self.assertIn("running_identity_present", plan["lanes"][0]["refused"])

    def test_pid_reuse_and_zombie_are_not_live(self):
        self.fx.fake_proc(4243, live=True, start="111")
        self.assertFalse(LC.is_pid_live(4243, expected_start="999",
                                        proc_root=str(self.fx.proc)))
        self.assertTrue(LC.is_pid_live(4243, expected_start="111",
                                       proc_root=str(self.fx.proc)))
        self.fx.fake_proc(4244, live=True, zombie=True, start="111")
        self.assertFalse(LC.is_pid_live(4244, proc_root=str(self.fx.proc)))
        self.assertFalse(LC.is_pid_live(999999, proc_root=str(self.fx.proc)))

    def test_pending_review_keeps_task_protected(self):
        manifest = {"lanes": [{"lane": 605}, {"lane": 606}],
                    "peer_reviews": [{"reviewer": 606, "authors": [605]}]}
        states = {605: {"status": "merged"},
                  606: {"status": "running", "candidate_refs": {}}}
        blockers = LC.pending_consumers(605, manifest["peer_reviews"], states)
        self.assertEqual(len(blockers), 1)
        self.fx.manifest(manifest["lanes"], manifest["peer_reviews"])
        self.fx.state(605, status="merged")
        self.fx.state(606, status="running")
        self.fx.prompt(605)
        self.fx.report(605)
        plan = LC.build_plan(self.fx.project, self.fx.control, self.fx.pool,
                             str(self.fx.proc), manifest, states, [605], {},
                             None, 50, self.fx.project)
        self.assertIn("pending_consumer_requires_task", plan["lanes"][0]["refused"])
        states[606] = {"status": "merged", "candidate_refs": {"605": "abc"}}
        plan2 = LC.build_plan(self.fx.project, self.fx.control, self.fx.pool,
                              str(self.fx.proc), manifest, states, [605], {},
                              None, 50, self.fx.project)
        self.assertTrue(plan2["lanes"][0]["deletable"])


    def test_symlink_attack_refused_and_reports_preserved(self):
        self.fx.manifest([{"lane": 607}])
        self.fx.state(607, status="merged")
        self.fx.prompt(607)
        victim = self.fx.project / "lanes" / "607.md"
        victim.unlink()
        os.symlink("/etc/hostname", victim)
        self.fx.report(607)
        states = {607: {"status": "merged"}}
        manifest = {"lanes": [{"lane": 607}], "peer_reviews": []}
        plan = LC.build_plan(self.fx.project, self.fx.control, self.fx.pool,
                             str(self.fx.proc), manifest, states, [607], {},
                             None, 50, self.fx.project)
        row = next(r for r in plan["candidates"]
                   if r["slot"] == "project_lane")
        self.assertEqual(row["decision"], "skip")
        self.assertIn("symlink", row["reason"])
        paths = [r["path"] for r in plan["candidates"]]
        self.assertFalse(any("MUSE-REPORT" in p for p in paths))
        self.assertFalse(any("logs" in p or p.endswith(".db") for p in paths))

    def test_private_task_needs_blob_or_archive(self):
        self.fx.manifest([{"lane": 608}])
        self.fx.state(608, status="merged")
        self.fx.prompt(608, text="HARD RULES prompt 608")
        self.fx.report(608)
        states = {608: {"status": "merged"}}
        manifest = {"lanes": [{"lane": 608}], "peer_reviews": []}
        plan = LC.build_plan(self.fx.project, self.fx.control, self.fx.pool,
                             str(self.fx.proc), manifest, states, [608], {},
                             None, 50, self.fx.project)
        row = next(r for r in plan["candidates"] if r["slot"] == "private_task")
        self.assertEqual(row["decision"], "hold")
        blob = row["git_blob"]
        plan2 = LC.build_plan(self.fx.project, self.fx.control, self.fx.pool,
                              str(self.fx.proc), manifest, states, [608],
                              {"608": blob}, None, 50, self.fx.project)
        row2 = next(r for r in plan2["candidates"] if r["slot"] == "private_task")
        self.assertEqual(row2["decision"], "delete")
        arch = self.fx.root / "arch"
        arch.mkdir(exist_ok=True)
        (arch / "608.md").write_bytes(
            (self.fx.control / "tasks" / "608.md").read_bytes())
        plan3 = LC.build_plan(self.fx.project, self.fx.control, self.fx.pool,
                              str(self.fx.proc), manifest, states, [608], {},
                              str(arch), 50, self.fx.project)
        row3 = next(r for r in plan3["candidates"] if r["slot"] == "private_task")
        self.assertEqual(row3["decision"], "delete")

    def test_apply_revalidates_stale_digest_and_is_idempotent(self):
        self.fx.manifest([{"lane": 609}])
        self.fx.state(609, status="merged")
        self.fx.prompt(609)
        self.fx.report(609)
        states = {609: {"status": "merged"}}
        manifest = {"lanes": [{"lane": 609}], "peer_reviews": []}
        blob = LC.git_blob_sha1((self.fx.control / "tasks" / "609.md").read_bytes())
        plan = LC.build_plan(self.fx.project, self.fx.control, self.fx.pool,
                             str(self.fx.proc), manifest, states, [609],
                             {"609": blob}, None, 50, self.fx.project)
        target = next(r for r in plan["candidates"] if r["slot"] == "lanes5")
        args = LC.build_parser().parse_args([
            "--project-root", str(self.fx.project), "--control-root", str(self.fx.control),
            "--pool-root", str(self.fx.pool), "--proc-root", str(self.fx.proc),
            "--lane", "609", "--apply", "--allow-tracked",
            "--select", target["path"]])
        (self.fx.project / ".claude" / "muse-arbeit" / "lanes5" / "609.md").write_text(
            "changed after plan")
        applied, errors = LC.apply_plan(plan, args)
        self.assertTrue(any(e["reason"] == "stale_content_digest_mismatch"
                            for e in errors), errors)
        self.assertFalse(any(a["path"] == target["path"] for a in applied))
        keep = [r for r in plan["candidates"]
                if r["slot"] == "pool_lane" and r["decision"] == "delete"][0]
        args2 = LC.build_parser().parse_args([
            "--project-root", str(self.fx.project), "--control-root", str(self.fx.control),
            "--pool-root", str(self.fx.pool), "--proc-root", str(self.fx.proc),
            "--lane", "609", "--apply", "--select", keep["path"]])
        applied2, errors2 = LC.apply_plan(plan, args2)
        self.assertEqual(errors2, [])
        self.assertEqual(len(applied2), 1)
        self.assertFalse(Path(keep["path"]).exists())
        applied3, errors3 = LC.apply_plan(plan, args2)
        self.assertEqual(applied3, [])
        self.assertTrue(any("revalidation_failed:missing" in e["reason"]
                            for e in errors3), errors3)

    def test_tracked_prompt_needs_allow_tracked_and_unregistered_refused(self):
        self.fx.manifest([{"lane": 610}])
        self.fx.state(610, status="merged")
        self.fx.prompt(610)
        self.fx.report(610)
        states = {610: {"status": "merged"}}
        manifest = {"lanes": [{"lane": 610}], "peer_reviews": []}
        blob = LC.git_blob_sha1((self.fx.control / "tasks" / "610.md").read_bytes())
        plan = LC.build_plan(self.fx.project, self.fx.control, self.fx.pool,
                             str(self.fx.proc), manifest, states, [610, 999],
                             {"610": blob}, None, 50, self.fx.project)
        self.assertEqual(plan["unregistered_selection"], [999])
        tracked = next(r for r in plan["candidates"] if r["slot"] == "project_lane")
        self.assertEqual(tracked["removal_via"], "coordinator_checkpoint")
        args = LC.build_parser().parse_args([
            "--project-root", str(self.fx.project), "--control-root", str(self.fx.control),
            "--pool-root", str(self.fx.pool), "--lane", "610",
            "--apply", "--select", tracked["path"]])
        _, errors = LC.apply_plan(plan, args)
        self.assertTrue(any("coordinator_checkpoint" in e["reason"] for e in errors))
        self.assertTrue(Path(tracked["path"]).exists())
        args2 = LC.build_parser().parse_args([
            "--project-root", str(self.fx.project), "--control-root", str(self.fx.control),
            "--pool-root", str(self.fx.pool), "--lane", "610",
            "--apply", "--allow-tracked", "--select", tracked["path"]])
        applied, errors2 = LC.apply_plan(plan, args2)
        self.assertEqual(errors2, [])
        self.assertEqual(len(applied), 1)

    def test_merged_lane_without_report_is_blocked(self):
        manifest = {"lanes": [{"lane": 611}], "peer_reviews": []}
        plan = LC.build_plan(self.fx.project, self.fx.control, self.fx.pool,
                             str(self.fx.proc), manifest,
                             {611: {"status": "merged"}}, [611], {}, None, 50,
                             self.fx.project)
        self.assertIn("needs_report_evidence", plan["lanes"][0]["refused"])

    def test_nonregular_file_refused_and_wrong_lane_kept(self):
        self.fx.manifest([{"lane": 612}])
        self.fx.state(612, status="merged")
        self.fx.prompt(612)
        self.fx.report(612)
        states = {612: {"status": "merged"}}
        manifest = {"lanes": [{"lane": 612}], "peer_reviews": []}
        pool_prompt = self.fx.pool / "lanes" / "612.md"
        pool_prompt.unlink()
        pool_prompt.mkdir()
        plan = LC.build_plan(self.fx.project, self.fx.control, self.fx.pool,
                             str(self.fx.proc), manifest, states, [612], {},
                             None, 50, self.fx.project)
        row = next(r for r in plan["candidates"] if r["slot"] == "pool_lane")
        self.assertEqual(row["gate"], "nonregular_file_refused")
        keep = next(r["path"] for r in plan["candidates"]
                    if r["slot"] == "lanes5" and r["decision"] == "delete")
        args = LC.build_parser().parse_args([
            "--project-root", str(self.fx.project), "--control-root", str(self.fx.control),
            "--pool-root", str(self.fx.pool), "--lane", "999",
            "--apply", "--select", keep])
        applied, _ = LC.apply_plan(plan, args)
        self.assertEqual(applied, [])
        self.assertTrue(Path(keep).exists())


if __name__ == "__main__":
    unittest.main()
