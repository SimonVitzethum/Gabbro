#!/usr/bin/env python3
"""Portable completion and workforce monitor (lane 595).

Read-only observer over registered lane state. It never launches, kills,
messages, reads credentials/configs/environments, scans private keys, prints
full cmdlines, or infers acceptance from a green build. A separate existing
coordinator owns bounded restoration/backfill; this monitor only reports.
"""
import argparse
import datetime
import json
import os
import re
import time
from pathlib import Path

MAX_ACTIVE_DEFAULT = 15
ACTIVE_STATES = {"running", "starting", "starting_feedback", "waiting_for_slot"}
TERMINAL_ATTENTION = {
    "runner_error",
    "incomplete",
    "needs_coordinator_fallback",
    "stopped_for_directory_audit",
}
VERDICT_RE = re.compile(r"^VERDICT:\s*(ACCEPT|REPAIR)\s*$", re.M)
CANDIDATE_RE = re.compile(r"^CANDIDATE:\s*(\S+)\s+(\S+)\s*$", re.M)


def now_iso():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def parse_args(argv=None):
    p = argparse.ArgumentParser(description="Read-only lane completion monitor.")
    p.add_argument("--state-dir", required=True, help="Directory with <lane>.json states.")
    p.add_argument("--manifest", required=True, help="Manifest JSON (lanes, peer_reviews, max_active, model).")
    p.add_argument("--proc-root", default="/proc", help="Process root (real /proc; fixture root in tests).")
    p.add_argument("--interval", type=float, default=60.0)
    p.add_argument("--once", action="store_true", help="Single scan, then exit.")
    p.add_argument("--status-out", required=True, help="JSON status destination (written atomically).")
    p.add_argument("--events-out", required=True, help="Append-only JSONL event destination.")
    p.add_argument("--seen-file", default=None, help="Persisted observation for restart dedup (JSON).")
    p.add_argument("--pause-file", default=None, help="Explicit pause marker; siblings auto-detected.")
    p.add_argument("--model-substr", default=None, help="Expected model process marker (default from manifest).")
    p.add_argument("--max-active", type=int, default=None, help="Override manifest max_active.")
    p.add_argument("--stale-secs", type=float, default=1800.0, help="Heartbeat staleness threshold.")
    p.add_argument("--mem-reserve-kib", type=int, default=8 * 1024 * 1024)
    p.add_argument("--log-dir", default=None, help="Optional directory with <lane>.log heartbeat files.")
    p.add_argument("--report-dir", default=None, help="Optional directory with MUSE-REPORT-<n>.md for verdict lines.")
    return p.parse_args(argv)


def parse_iso(value):
    try:
        return datetime.datetime.fromisoformat(str(value))
    except (ValueError, TypeError):
        return None


def load_manifest(path):
    data = json.loads(Path(path).read_text())
    lanes = {int(x["lane"]): x for x in data.get("lanes", [])}
    reviews = list(data.get("peer_reviews", [])) + list(data.get("delegated_peer_reviews", []))
    max_active = data.get("max_active", MAX_ACTIVE_DEFAULT)
    model = data.get("model", "")
    return {"lanes": lanes, "reviews": reviews, "max_active": max_active, "model": model}


def load_states(state_dir, registered):
    out = {}
    base = Path(state_dir)
    if not base.is_dir():
        return out
    for lane in sorted(registered):
        p = base / f"{lane}.json"
        if not p.is_file():
            continue
        try:
            out[lane] = json.loads(p.read_text())
        except (ValueError, OSError):
            out[lane] = {"lane": lane, "status": "unreadable"}
    return out


def read_cmdline_raw(proc_root, pid):
    try:
        return Path(proc_root, str(pid), "cmdline").read_bytes()
    except FileNotFoundError:
        return None
    except (PermissionError, ProcessLookupError, OSError):
        return b""
    except Exception:
        return b""


def pid_matches(raw, *needles):
    if raw is None:
        return False, "dead"
    if raw == b"":
        return True, "unknown"
    ok = all(n.encode() in raw for n in needles)
    return ok, ("matched" if ok else "mismatch")


def check_registered_pid(proc_root, pid, role, lane, model_substr):
    """Return dict with alive/identity info; never logs the cmdline itself."""
    if pid is None:
        return {"pid": None, "alive": False, "identity": "absent"}
    try:
        pid_int = int(pid)
    except (ValueError, TypeError):
        return {"pid": pid, "alive": False, "identity": "invalid"}
    raw = read_cmdline_raw(proc_root, pid_int)
    if raw is None:
        return {"pid": pid_int, "alive": False, "identity": "dead"}
    if role == "model":
        # The managed binary is the installed opencode runner; the manifest
        # model string ("opencode-go/muse-spark-...") names the provider/model,
        # not the binary, so match the binary marker plus the lane id.
        # A custom --model-substr without "opencode" overrides the marker.
        marker = "opencode"
        if model_substr and "opencode" not in model_substr:
            marker = model_substr
        needles = [marker, str(lane)]
    else:
        needles = ("coordinat", str(lane))
    ok, how = pid_matches(raw, *needles)
    if how == "unknown":
        return {"pid": pid_int, "alive": True, "identity": "unknown"}
    if ok:
        return {"pid": pid_int, "alive": True, "identity": "matched"}
    return {"pid": pid_int, "alive": False, "identity": "mismatch"}


def mem_available_kib(proc_root):
    try:
        for line in Path(proc_root, "meminfo").read_text().splitlines():
            if line.startswith("MemAvailable:"):
                return int(line.split()[1])
    except (FileNotFoundError, ValueError, IndexError, OSError):
        return None
    return None


def pause_state(state_dir, explicit):
    candidates = []
    if explicit:
        candidates.append(Path(explicit))
    base = Path(state_dir).parent
    candidates.append(base / "pool-paused.json")
    candidates.append(base / "coordinator-pause.json")
    for c in candidates:
        try:
            if c.is_file():
                return True, str(c)
        except OSError:
            continue
    return False, None


def report_verdict(report_dir, lane):
    """Read only the machine-readable VERDICT/CANDIDATE lines, if present."""
    if not report_dir:
        return None, {}
    p = Path(report_dir) / f"MUSE-REPORT-{lane}.md"
    try:
        text = p.read_text(errors="replace")
    except OSError:
        return None, {}
    verdicts = VERDICT_RE.findall(text)
    verdict = verdicts[0] if len(verdicts) == 1 else None
    heads = {m.group(1): m.group(2) for m in CANDIDATE_RE.finditer(text)}
    return verdict, heads


def lane_head(state):
    refs = state.get("candidate_refs")
    if isinstance(refs, dict) and refs:
        return dict(refs)
    for key in ("head", "candidate", "commit"):
        if state.get(key):
            return state.get(key)
    return None


def heartbeat_age_secs(state, log_dir, state_dir):
    ages = {}
    upd = parse_iso(state.get("updated"))
    if upd is not None:
        now = datetime.datetime.now(datetime.timezone.utc)
        if upd.tzinfo is None:
            upd = upd.replace(tzinfo=datetime.timezone.utc)
        ages["state"] = (now - upd).total_seconds()
    log_path = None
    if log_dir:
        cand = Path(log_dir) / f"{state.get('lane')}.log"
        if cand.is_file():
            log_path = cand
    else:
        raw = state.get("log")
        if raw:
            cand = Path(str(raw))
            name = cand.name
            sib = Path(state_dir).parent / "logs" / name
            if cand.is_file():
                log_path = cand
            elif sib.is_file():
                log_path = sib
    if log_path is not None:
        try:
            ages["log"] = time.time() - log_path.stat().st_mtime
        except OSError:
            pass
    if not ages:
        return None
    return max(ages.values())


def scan(args, manifest):
    state_dir = args.state_dir
    registered = set(manifest["lanes"].keys())
    for r in manifest["reviews"]:
        try:
            registered.add(int(r.get("reviewer")))
        except (TypeError, ValueError):
            pass
        for a in r.get("authors", []) or []:
            try:
                registered.add(int(a))
            except (TypeError, ValueError):
                pass
    states = load_states(state_dir, registered)
    max_active = args.max_active or manifest["max_active"] or MAX_ACTIVE_DEFAULT
    model_substr = args.model_substr or manifest["model"] or "opencode"
    model_marker = model_substr  # keep full string; matcher looks for "opencode" in it
    paused, pause_file = pause_state(state_dir, args.pause_file)
    mem_kib = mem_available_kib(args.proc_root)
    low_memory = mem_kib is not None and mem_kib < args.mem_reserve_kib

    by_lane = {}
    for lane in sorted(registered):
        st = states.get(lane, {"lane": lane, "status": "unregistered_no_state"})
        status = st.get("status", "unknown")
        model_chk = check_registered_pid(args.proc_root, st.get("model_pid"), "model", lane, model_marker)
        runner_chk = check_registered_pid(args.proc_root, st.get("runner_pid"), "runner", lane, model_marker)
        model_alive = bool(model_chk["alive"])
        runner_alive = bool(runner_chk["alive"])
        wrong_model = (
            st.get("model_pid") is not None
            and read_cmdline_raw(args.proc_root, st.get("model_pid")) not in (None, b"")
            and not model_alive
        )
        active = status in ACTIVE_STATES
        dead = active and not (model_alive or runner_alive)
        age = heartbeat_age_secs(st, args.log_dir, state_dir) if active else None
        stalled = age is not None and age > args.stale_secs
        verdict, _ = report_verdict(args.report_dir, lane)
        by_lane[lane] = {
            "lane": lane,
            "status": status,
            "kind": st.get("kind") or manifest["lanes"].get(lane, {}).get("kind"),
            "model_alive": model_alive,
            "runner_alive": runner_alive,
            "model_identity": model_chk["identity"],
            "runner_identity": runner_chk["identity"],
            "wrong_model_or_reused_pid": bool(wrong_model),
            "dead": bool(dead),
            "stalled": bool(stalled),
            "heartbeat_age_secs": age,
            "head": lane_head(st),
            "verdict": verdict,
            "updated": st.get("updated"),
        }

    active_count = sum(1 for v in by_lane.values() if v["status"] in ACTIVE_STATES)
    model_count = sum(1 for v in by_lane.values() if v["model_alive"])
    runner_count = sum(1 for v in by_lane.values() if v["runner_alive"])
    ready = sorted(n for n, v in by_lane.items() if v["status"] == "report_ready")
    merged = sorted(n for n, v in by_lane.items() if v["status"] == "merged")
    pending = sorted(
        n for n, v in by_lane.items() if v["status"] in ("ready", "prepared", "queued_isolated_restart")
    )
    attention = sorted(n for n, v in by_lane.items() if v["status"] in TERMINAL_ATTENTION)

    blockers = []
    if low_memory:
        blockers.append({"kind": "resource", "lane": None, "detail": f"MemAvailable {mem_kib} KiB below reserve {args.mem_reserve_kib}"})
    if paused:
        blockers.append({"kind": "paused", "lane": None, "detail": f"pause marker {pause_file}; auto-actions must stop"})
    state_by_lane = {n: states.get(n, {}) for n in registered}
    for r in manifest["reviews"]:
        try:
            rev = int(r.get("reviewer"))
        except (TypeError, ValueError):
            continue
        rev_status = state_by_lane.get(rev, {}).get("status")
        if rev_status in (None, "ready", "prepared", "queued_isolated_restart", "waiting_for_slot"):
            waiting = [a for a in r.get("authors", []) if state_by_lane.get(int(a), {}).get("status") != "report_ready"]
            if waiting:
                blockers.append({"kind": "dependency", "lane": rev, "detail": f"reviewer waits for authors {waiting}"})
    for n, v in by_lane.items():
        if v["status"] in TERMINAL_ATTENTION:
            blockers.append({"kind": "build", "lane": n, "detail": f"terminal status {v['status']} needs operator decision"})
        if v["dead"]:
            blockers.append({"kind": "dead", "lane": n, "detail": f"status {v['status']} but no live managed pid"})
        if v["wrong_model_or_reused_pid"]:
            blockers.append({"kind": "reused_pid", "lane": n, "detail": "pid alive but identity mismatch; not counted as managed"})
        if v["stalled"]:
            blockers.append({"kind": "stalled", "lane": n, "detail": f"no heartbeat for {v['heartbeat_age_secs']:.0f}s"})

    under = active_count < max_active and len(pending) > 0
    status_doc = {
        "generated": now_iso(),
        "state_dir": str(state_dir),
        "max_active": max_active,
        "paused": paused,
        "pause_file": pause_file,
        "counts": {
            "registered": len(registered),
            "observed": len(states),
            "active_or_starting": active_count,
            "model_alive": model_count,
            "runner_alive": runner_count,
            "report_ready": len(ready),
            "merged": len(merged),
            "pending": len(pending),
        },
        "report_ready": ready,
        "merged": merged,
        "pending": pending,
        "needs_attention": attention,
        "under_utilised": bool(under),
        "low_memory": bool(low_memory),
        "mem_available_kib": mem_kib,
        "lanes": [by_lane[n] for n in sorted(by_lane)],
        "blockers": blockers,
    }
    return status_doc


def load_seen(path):
    if not path:
        return {}
    try:
        return json.loads(Path(path).read_text())
    except (FileNotFoundError, ValueError, OSError):
        return {}


def save_seen(path, data):
    if not path:
        return
    p = Path(path)
    if p.parent and str(p.parent) not in ("", "."):
        p.parent.mkdir(parents=True, exist_ok=True)
    tmp = p.with_suffix(f".{os.getpid()}.tmp")
    tmp.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    tmp.replace(p)


def atomic_write_json(path, data):
    p = Path(path)
    if p.parent and str(p.parent) not in ("", "."):
        p.parent.mkdir(parents=True, exist_ok=True)
    tmp = p.with_suffix(f".{os.getpid()}.tmp")
    tmp.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    tmp.replace(p)


def append_events(path, events):
    if not events:
        return 0
    p = Path(path)
    if p.parent and str(p.parent) not in ("", "."):
        p.parent.mkdir(parents=True, exist_ok=True)
    with p.open("a", encoding="utf-8") as f:
        for e in events:
            f.write(json.dumps(e, sort_keys=True) + "\n")
        f.flush()
        try:
            os.fsync(f.fileno())
        except OSError:
            pass
    return len(events)


def derive_events(status_doc, seen):
    events = []
    for lane in status_doc["lanes"]:
        n = lane["lane"]
        key = f"{n}"
        prev = seen.get(key, {})
        cur_sig = json.dumps({"to": lane["status"], "updated": lane.get("updated"), "head": lane.get("head")}, sort_keys=True)
        if prev.get("sig") == cur_sig:
            continue
        kind = None
        if lane["status"] == "report_ready" and prev.get("to") != "report_ready":
            kind = "completion"
        elif prev and prev.get("to") != lane["status"]:
            kind = "transition"
        elif lane["dead"] and not prev.get("dead"):
            kind = "dead"
        elif lane["stalled"] and not prev.get("stalled"):
            kind = "stalled"
        if kind is None:
            continue
        events.append({
            "ts": now_iso(),
            "kind": kind,
            "lane": n,
            "from": prev.get("to"),
            "to": lane["status"],
            "head": lane.get("head"),
            "verdict": lane.get("verdict"),
            "updated": lane.get("updated"),
        })
        seen[key] = {"to": lane["status"], "sig": cur_sig, "dead": lane["dead"], "stalled": lane["stalled"]}
    return events


def run_once(args):
    manifest = load_manifest(args.manifest)
    status_doc = scan(args, manifest)
    seen_path = args.seen_file or str(Path(args.status_out).with_suffix(".seen.json"))
    seen = load_seen(seen_path)
    events = derive_events(status_doc, seen)
    atomic_write_json(args.status_out, status_doc)
    append_events(args.events_out, events)
    save_seen(seen_path, seen)
    return status_doc, events


def main(argv=None):
    args = parse_args(argv)
    if args.once:
        status_doc, events = run_once(args)
        print(f"lanes={status_doc['counts']['registered']} active={status_doc['counts']['active_or_starting']} models={status_doc['counts']['model_alive']} events={len(events)} paused={status_doc['paused']}")
        return 0
    while True:
        run_once(args)
        time.sleep(max(args.interval, 1.0))


if __name__ == "__main__":
    raise SystemExit(main())
