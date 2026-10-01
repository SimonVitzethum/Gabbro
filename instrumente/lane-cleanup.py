#!/usr/bin/env python3
"""Lane prompt cleanup planner (lane 622). Standard library only.

Plans (default) or applies (--apply) deletion of exact numeric owned lane
prompt copies after safe completion. Never deletes folders, logs, reports,
databases or clones; tracked root prompts go through the coordinator.
Run: python3 instrumente/lane-cleanup.py --help
"""
import argparse
import hashlib
import json
import os
import sys
from pathlib import Path

NON_FINAL = frozenset([
    "report_ready", "incomplete", "runner_error", "paused",
    "waiting_for_review", "needs_coordinator_fallback", "ready",
    "prepared", "running", "starting", "starting_feedback",
    "waiting_for_slot", "waiting_for_candidate",
])
MERGED_STATUS = "merged"
TERMINAL_ABANDONED = frozenset(["abandoned", "final_refused", "final-refused"])
TOOL_VERSION = "622.1"
MAX_CANDIDATES_DEFAULT = 50


def sha256_hex(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob_sha1(data: bytes) -> str:
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def is_pid_live(pid, expected_start=None, proc_root="/proc") -> bool:
    """True only for a verified live non-zombie process.

    Guards PID reuse: when the registry records an expected /proc start
    time (field 22 of stat), a mismatching live PID is stale, not live.
    Zombies (State Z/X) and unreadable entries are never live.
    """
    try:
        pid_int = int(pid)
    except (TypeError, ValueError):
        return False
    if pid_int <= 0:
        return False
    proc = Path(proc_root) / str(pid_int)
    try:
        if not proc.is_dir() or proc.is_symlink():
            return False
        stat_text = (proc / "stat").read_text(errors="replace")
        after = stat_text.rsplit(")", 1)[1].split()
        state = after[0] if after else ""
        if state in ("Z", "X"):
            return False
        if expected_start is not None and len(after) > 19:
            if str(expected_start) != after[19]:
                return False
        cmdline = (proc / "cmdline").read_bytes()
        if not cmdline.strip(b"\x00"):
            return False
        return True
    except (OSError, ValueError, IndexError):
        return False


def build_parser():
    p = argparse.ArgumentParser(description="Plan lane prompt cleanup (dry-run default).")
    p.add_argument("--project-root", required=True)
    p.add_argument("--control-root", required=True)
    p.add_argument("--pool-root", required=True)
    p.add_argument("--proc-root", default="/proc")
    p.add_argument("--manifest", default=None)
    p.add_argument("--state-dir", default=None)
    p.add_argument("--report-root", default=None,
                   help="Root holding messung/muse reports (default: <project-root>).")
    p.add_argument("--lane", action="append", type=int, default=None,
                   help="Select lane explicitly (repeatable). Default: all registered.")
    p.add_argument("--select", action="append", default=None,
                   help="Restrict --apply to this exact candidate path (repeatable).")
    p.add_argument("--dry-run", action="store_true", default=True)
    p.add_argument("--apply", action="store_true", default=False)
    p.add_argument("--allow-tracked", action="store_true", default=False,
                   help="Allow unlinking tracked project lanes/<n>.md (coordinator commits later).")
    p.add_argument("--task-blob-file", default=None,
                   help="JSON {lane: blob-sha1} proving private task prompt is in git history.")
    p.add_argument("--archive-dir", default=None,
                   help="Directory with externally archived <lane>.md prompt copies.")
    p.add_argument("--max-candidates", type=int, default=MAX_CANDIDATES_DEFAULT)
    p.add_argument("--output", default=None)
    return p


def load_json(path: Path):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None


def durable_terminal(state: dict) -> bool:
    return bool(state.get("terminal") or state.get("terminal_flag")
                or state.get("durable_terminal") or state.get("abandoned_final"))


def live_identities(state: dict, proc_root: str):
    """Return sorted list of verified live model/runner PIDs in a state record."""
    live = []
    for key in ("model_pid", "runner_pid", "model_start_ticks",
                "model_start_time"):
        _ = key  # documented: only PID keys below carry liveness
    for key in ("model_pid", "runner_pid"):
        pid = state.get(key)
        if pid is None:
            continue
        expected = state.get("model_start_ticks", state.get("model_start_time"))
        if is_pid_live(pid, expected, proc_root):
            live.append({"key": key, "pid": int(pid)})
    return sorted(live, key=lambda r: (r["key"], r["pid"]))


def completion_of(lane: int, state: dict):
    """Classify registry completion. Only merged or durable-terminal counts."""
    status = state.get("status")
    if status == MERGED_STATUS:
        return True, "merged_after_checked_integration", {}
    if status in TERMINAL_ABANDONED and durable_terminal(state):
        return True, "terminal_%s_with_durable_flag" % status, {}
    if status in NON_FINAL or status in TERMINAL_ABANDONED:
        return False, "not_final:%s" % status, {}
    if not status:
        return False, "not_final:unknown", {}
    return False, "not_final:%s" % status, {}


def pending_consumers(lane: int, peer_reviews, states: dict):
    """Reviewers/consumers that still require this lane's task copy."""
    blockers = []
    for entry in peer_reviews or []:
        authors = entry.get("authors", [])
        reviewer = entry.get("reviewer")
        if lane not in authors:
            continue
        rstate = states.get(reviewer, {})
        rstatus = rstate.get("status")
        refs = rstate.get("candidate_refs", {})
        pinned = refs.get(str(lane), refs.get(lane))
        if rstatus == MERGED_STATUS:
            continue
        if rstatus in TERMINAL_ABANDONED and durable_terminal(rstate):
            continue
        blockers.append({"reviewer": reviewer, "reviewer_status": rstatus,
                         "pinned_candidate": pinned,
                         "reason": "pending_review_keeps_task_protected"})
    return blockers


def candidate_specs(project_root: Path, control_root: Path, pool_root: Path, lane: int):
    name = "%d.md" % lane
    return [
        ("project_lane", project_root / "lanes" / name, "tracked:coordinator_checkpoint"),
        ("private_task", control_root / "tasks" / name, "needs_git_blob_or_archive"),
        ("lanes5", project_root / ".claude" / "muse-arbeit" / "lanes5" / name, "copy"),
        ("sicherung", project_root / ".claude" / "muse-sicherung" / name, "copy"),
        ("pool_lane", pool_root / "lanes" / name, "copy"),
        ("clone_tmp", pool_root / ("a%d" % lane) / ".tmp" / "LANE.md", "clone_tmp"),
    ]


def inside_root(path: Path, root: Path) -> bool:
    try:
        path.absolute().relative_to(root.absolute())
        return True
    except ValueError:
        return False


def check_candidate(path: Path, root: Path, expect_name: str):
    """Guard symlinks, traversal, registration and file kind. No following."""
    if path.name != expect_name:
        return False, "wrong_name"
    if ".." in path.parts:
        return False, "path_traversal"
    if not inside_root(path, root):
        return False, "outside_configured_root"
    try:
        st = os.lstat(path)
    except OSError:
        return False, "missing"
    if os.path.islink(path):
        return False, "symlink_refused"
    import stat as statmod
    if not statmod.S_ISREG(st.st_mode):
        return False, "nonregular_file_refused"
    try:
        resolved = path.resolve()
        if resolved != path.absolute() and not inside_root(resolved, root.resolve() if root.exists() else root.absolute()):
            return False, "symlink_escape_refused"
    except OSError:
        return False, "unresolvable"
    return True, "ok"


def report_evidence(project_root: Path, pool_root: Path, lane: int):
    """Surviving report evidence; prompt text stays reachable via history."""
    cands = [
        project_root / "messung" / "muse" / ("MUSE-REPORT-%d.md" % lane),
        pool_root / ("a%d" % lane) / ("MUSE-REPORT-%d.md" % lane),
    ]
    found = []
    for path in cands:
        try:
            if path.is_symlink() or not path.is_file():
                continue
            data = path.read_bytes()
            found.append({"path": str(path), "sha256": sha256_hex(data),
                          "bytes": len(data)})
        except OSError:
            continue
    return found


def build_plan(project_root: Path, control_root: Path, pool_root: Path, proc_root: str,
               manifest: dict, states: dict, select_lanes, task_blobs: dict,
               archive_dir, max_candidates: int, report_root: Path):
    lanes = manifest.get("lanes", []) if manifest else []
    peer_reviews = (manifest.get("peer_reviews", []) if manifest else []) + (
        manifest.get("delegated_peer_reviews", []) if manifest else [])
    registered = {int(j["lane"]) for j in lanes if "lane" in j}
    if select_lanes is not None:
        wanted = [n for n in select_lanes if n in registered]
        refused = [n for n in select_lanes if n not in registered]
    else:
        wanted = sorted(registered)
        refused = []
    plan_lanes = []
    candidates = []
    for lane in sorted(wanted):
        state = states.get(lane, states.get(str(lane), {}))
        complete, why, _ = completion_of(lane, state)
        live = live_identities(state, proc_root)
        blockers = pending_consumers(lane, peer_reviews, states)
        reports = report_evidence(report_root, pool_root, lane)
        lane_rec = {"lane": lane, "status": state.get("status"),
                    "complete": bool(complete and not live and not blockers),
                    "completion_reason": why, "live_identities": live,
                    "pending_consumers": blockers,
                    "reports": reports, "refused": []}
        if not complete:
            lane_rec["refused"].append("lane_not_complete:%s" % why)
        if live:
            lane_rec["refused"].append("running_identity_present")
        if blockers:
            lane_rec["refused"].append("pending_consumer_requires_task")
        if complete and not live and not blockers and not reports:
            lane_rec["refused"].append("needs_report_evidence")
        lane_rec["deletable"] = not lane_rec["refused"]
        deletable = lane_rec["deletable"]
        plan_lanes.append(lane_rec)
        for label, path, kind in candidate_specs(project_root, control_root, pool_root, lane):
            root = {"project_lane": project_root, "private_task": control_root,
                    "lanes5": project_root, "sicherung": project_root,
                    "pool_lane": pool_root, "clone_tmp": pool_root}[label]
            ok, gate = check_candidate(path, root, path.name)
            rec = {"lane": lane, "slot": label, "path": str(path),
                   "kind": kind, "gate": gate, "decision": "skip",
                   "reason": None, "sha256": None, "bytes": None,
                   "git_blob": None, "removal_via": None}
            if not deletable:
                rec["reason"] = "lane_protected:" + ";".join(lane_rec["refused"])
            elif not ok:
                rec["reason"] = gate
                if gate == "missing":
                    rec["reason"] = "already_absent"
            else:
                try:
                    data = path.read_bytes()
                    rec["sha256"] = sha256_hex(data)
                    rec["bytes"] = len(data)
                    rec["git_blob"] = git_blob_sha1(data)
                except OSError:
                    rec["reason"] = "unreadable"
                    candidates.append(rec)
                    continue
                if label == "project_lane":
                    rec["removal_via"] = "coordinator_checkpoint"
                if label == "private_task":
                    proven = False
                    blob_want = None
                    if task_blobs:
                        blob_want = task_blobs.get(str(lane), task_blobs.get(lane))
                        if isinstance(blob_want, dict):
                            blob_want = blob_want.get("blob", blob_want.get("sha1"))
                    if blob_want:
                        proven = (blob_want == rec["git_blob"])
                    if not proven and archive_dir is not None:
                        arch = Path(archive_dir) / ("%d.md" % lane)
                        try:
                            if not arch.is_symlink() and arch.is_file():
                                proven = (sha256_hex(arch.read_bytes()) == rec["sha256"])
                        except OSError:
                            proven = False
                    if not proven:
                        rec["decision"] = "hold"
                        rec["reason"] = "needs_git_blob_or_archive"
                        candidates.append(rec)
                        continue
                rec["decision"] = "delete"
                rec["reason"] = "approved_exact_prompt_copy"
            candidates.append(rec)
            if len(candidates) >= max_candidates:
                break
        if len(candidates) >= max_candidates:
            break
    candidates.sort(key=lambda r: r["path"])
    truncated = len(candidates) >= max_candidates
    return {"tool": "lane-cleanup", "version": TOOL_VERSION,
            "roots": {"project": str(project_root), "control": str(control_root),
                      "pool": str(pool_root), "proc": str(proc_root)},
            "unregistered_selection": sorted(refused),
            "lanes": sorted(plan_lanes, key=lambda r: r["lane"]),
            "candidates": candidates,
            "summary": {"lanes_selected": len(plan_lanes),
                        "lanes_deletable": sum(1 for r in plan_lanes if r["deletable"]),
                        "candidates_delete": sum(1 for r in candidates if r["decision"] == "delete"),
                        "candidates_hold": sum(1 for r in candidates if r["decision"] == "hold"),
                        "truncated": truncated}}


def apply_plan(plan, args):
    """Unlink only explicitly selected approved exact paths after revalidation."""
    if args.lane is None or not args.lane:
        return [], [{"reason": "apply_requires_explicit_lane_selection"}]
    wanted = set(args.select) if args.select else None
    roots = plan["roots"]
    project_root = Path(roots["project"])
    root_by_slot = {"project_lane": project_root, "private_task": Path(roots["control"]),
                    "lanes5": project_root, "sicherung": project_root,
                    "pool_lane": Path(roots["pool"]), "clone_tmp": Path(roots["pool"])}
    applied, errors = [], []
    for rec in plan["candidates"]:
        if rec["lane"] not in args.lane or rec["decision"] != "delete":
            continue
        if wanted is not None and rec["path"] not in wanted:
            continue
        if rec["slot"] == "project_lane" and not args.allow_tracked:
            errors.append({"path": rec["path"],
                           "reason": "tracked_prompt_needs_coordinator_checkpoint"})
            continue
        path = Path(rec["path"])
        root = root_by_slot.get(rec["slot"], project_root)
        ok, gate = check_candidate(path, root, path.name)
        if not ok:
            errors.append({"path": rec["path"], "reason": "revalidation_failed:" + gate})
            continue
        try:
            data = path.read_bytes()
        except OSError as exc:
            errors.append({"path": rec["path"], "reason": "unreadable:%s" % exc})
            continue
        if rec.get("sha256") and sha256_hex(data) != rec["sha256"]:
            errors.append({"path": rec["path"], "reason": "stale_content_digest_mismatch"})
            continue
        if path.name != ("%d.md" % rec["lane"]) and path.name != "LANE.md":
            errors.append({"path": rec["path"], "reason": "not_an_exact_prompt_copy"})
            continue
        try:
            path.unlink()
            applied.append({"path": rec["path"], "lane": rec["lane"],
                            "slot": rec["slot"], "sha256": sha256_hex(data)})
        except OSError as exc:
            errors.append({"path": rec["path"], "reason": "unlink_failed:%s" % exc})
    return applied, errors


def main(argv=None):
    args = build_parser().parse_args(argv)
    project_root = Path(args.project_root)
    control_root = Path(args.control_root)
    pool_root = Path(args.pool_root)
    manifest_path = Path(args.manifest) if args.manifest else control_root / "manifest.json"
    state_dir = Path(args.state_dir) if args.state_dir else control_root / "state"
    report_root = Path(args.report_root) if args.report_root else project_root
    manifest = load_json(manifest_path) or {}
    states = {}
    if state_dir.is_dir():
        for child in sorted(state_dir.glob("*.json")):
            try:
                lane_id = int(child.stem)
            except ValueError:
                continue
            doc = load_json(child)
            if isinstance(doc, dict):
                states[lane_id] = doc
                states[str(lane_id)] = doc
    task_blobs = load_json(Path(args.task_blob_file)) if args.task_blob_file else {}
    plan = build_plan(project_root, control_root, pool_root, args.proc_root,
                      manifest, states, args.lane, task_blobs or {},
                      args.archive_dir, args.max_candidates, report_root)
    if args.apply:
        applied, errors = apply_plan(plan, args)
        plan["applied"] = applied
        plan["apply_errors"] = errors
        plan["executed"] = True
    else:
        plan["executed"] = False
    out = json.dumps(plan, indent=2, sort_keys=True) + "\n"
    if args.output:
        Path(args.output).write_text(out, encoding="utf-8")
    else:
        sys.stdout.write(out)


if __name__ == "__main__":
    main()
