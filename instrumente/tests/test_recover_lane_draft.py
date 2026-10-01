#!/usr/bin/env python3
"""Tests for instrumente/recover-lane-draft.py (lane 642). Stdlib only.

Fixtures live inside the clone (.tmp/), never /tmp. The tool must never
execute recorded commands: tests assert marker files are absent.
Run: python3 instrumente/tests/test_recover_lane_draft.py
"""
import hashlib
import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

TOOL = Path(__file__).resolve().parents[1] / "recover-lane-draft.py"
CLONE_TMP = Path(__file__).resolve().parents[2] / ".tmp"

LT = chr(60)
GT = chr(62)


def load_tool():
    spec = importlib.util.spec_from_file_location("recover_lane_draft",
                                                  str(TOOL))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


RT = load_tool()


def xml_record(name, params):
    parts = [LT + 'invoke name="%s"' % name + GT]
    for key, value in params:
        parts.append(LT + 'parameter name="%s"' % key + GT + value
                     + LT + "/parameter" + GT)
    parts.append(LT + "/invoke" + GT)
    return "".join(parts)


class Scratch:
    def __init__(self):
        CLONE_TMP.mkdir(exist_ok=True)
        self.tmp = tempfile.TemporaryDirectory(prefix="rc642-",
                                               dir=str(CLONE_TMP))
        self.root = Path(self.tmp.name)

    def close(self):
        self.tmp.cleanup()

    def run_tool(self, log_text, target, extra=()):
        log = self.root / "log.txt"
        log.write_text(log_text)
        out = self.root / "out.txt"
        rep = self.root / "rep.json"
        cmd = [sys.executable, str(TOOL), "--input", str(log),
               "--target", target, "--output", str(out),
               "--report", str(rep)] + list(extra)
        proc = subprocess.run(cmd, capture_output=True, text=True)
        summary = json.loads(proc.stdout.strip())
        report = json.loads(rep.read_text()) if rep.exists() else None
        return proc, summary, report, out


class JsonEvents(unittest.TestCase):
    def setUp(self):
        self.fx = Scratch()

    def tearDown(self):
        self.fx.close()

    def test_write_then_edit_order(self):
        log = ('{"op": "write", "filePath": "T", "content": "a=1\\n"}\n'
               '{"op": "edit", "filePath": "T", "oldString": "a=1", '
               '"newString": "a=2"}\n')
        proc, summary, _rep, out = self.fx.run_tool(log, "T")
        self.assertEqual(proc.returncode, 0)
        self.assertEqual(out.read_text(), "a=2\n")
        self.assertEqual(summary["replayed"], 2)
        self.assertNotIn("a=2", proc.stdout)

    def test_edit_before_write_is_unreplayed(self):
        log = ('{"op": "edit", "filePath": "T", "oldString": "a", '
               '"newString": "b"}\n'
               '{"op": "write", "filePath": "T", "content": "a\\n"}\n')
        _proc, summary, report, out = self.fx.run_tool(log, "T")
        self.assertEqual(out.read_text(), "a\n")
        self.assertEqual(summary["replayed"], 1)
        self.assertEqual(summary["unreplayed"], 1)
        kinds = [e["kind"] for e in report["unreplayed"]]
        self.assertIn("edit_without_base", kinds)

    def test_edit_not_unique_without_flag(self):
        log = ('{"op": "write", "filePath": "T", "content": "xax\\n"}\n'
               '{"op": "edit", "filePath": "T", "oldString": "x", '
               '"newString": "y"}\n')
        _proc, summary, report, out = self.fx.run_tool(log, "T")
        self.assertEqual(out.read_text(), "xax\n")
        self.assertEqual(summary["unreplayed"], 1)
        self.assertTrue(report["unreplayed"][0]["kind"].startswith(
            "edit_not_unique"))

    def test_replace_all_replaces_every_match(self):
        log = ('{"op": "write", "filePath": "T", "content": "xax\\n"}\n'
               '{"op": "edit", "filePath": "T", "oldString": "x", '
               '"newString": "y", "replaceAll": true}\n')
        _proc, summary, _rep, out = self.fx.run_tool(log, "T")
        self.assertEqual(out.read_text(), "yay\n")
        self.assertEqual(summary["replayed"], 2)

    def test_exact_path_only(self):
        log = ('{"op": "write", "filePath": "IR.lean ", "content": "bad\\n"}\n'
               '{"op": "write", "filePath": "ir.lean", "content": "bad\\n"}\n'
               '{"op": "write", "filePath": "XIR.lean", "content": "bad\\n"}\n'
               '{"op": "write", "filePath": "IR.lean", "content": "good\\n"}\n')
        _proc, summary, _rep, out = self.fx.run_tool(log, "IR.lean")
        self.assertEqual(out.read_text(), "good\n")
        self.assertEqual(summary["replayed"], 1)

    def test_stdout_never_carries_content(self):
        secret = "secret-marker-642-xyz"
        log = '{"op": "write", "filePath": "T", "content": "%s\\n"}\n' % secret
        proc, _summary, _rep, _out = self.fx.run_tool(log, "T")
        self.assertNotIn(secret, proc.stdout)
        self.assertNotIn(secret, proc.stderr)


class XmlEvents(unittest.TestCase):
    def setUp(self):
        self.fx = Scratch()

    def tearDown(self):
        self.fx.close()

    def test_xml_write_with_entity(self):
        log = xml_record("write", [("filePath", "T"),
                                   ("content", "a&lt;b")]) + "\n"
        _proc, summary, _rep, out = self.fx.run_tool(log, "T")
        self.assertEqual(out.read_text(), "a<b")
        self.assertEqual(summary["replayed"], 1)

    def test_xml_replace_all_words(self):
        for raw in ("true", "1"):
            log = (xml_record("write", [("filePath", "T"),
                                        ("content", "q\n")]) + "\n"
                   + xml_record("edit", [("filePath", "T"),
                                         ("oldString", "q"),
                                         ("newString", "w"),
                                         ("replaceAll", raw)]) + "\n")
            _proc, _summary, _rep, out = self.fx.run_tool(log, "T")
            self.assertEqual(out.read_text(), "w\n", raw)

    def test_xml_incomplete_is_unsupported(self):
        log = xml_record("edit", [("filePath", "T"),
                                  ("oldString", "a")]) + "\n"
        _proc, summary, report, _out = self.fx.run_tool(log, "T")
        self.assertEqual(summary["replayed"], 0)
        self.assertEqual(summary["unsupported"], 1)
        self.assertEqual(report["unsupported"][0]["kind"], "xml_incomplete")


class HeredocEvents(unittest.TestCase):
    def setUp(self):
        self.fx = Scratch()

    def tearDown(self):
        self.fx.close()

    def test_quoted_heredoc_replays(self):
        log = "cat > 'T' <<'EOF'\none\ntwo\nEOF\n"
        _proc, summary, _rep, out = self.fx.run_tool(log, "T")
        self.assertEqual(out.read_text(), "one\ntwo\n")
        self.assertEqual(summary["replayed"], 1)

    def test_unquoted_heredoc_refused(self):
        log = "cat > T <<EOF\nhi\nEOF\n"
        _proc, summary, report, out = self.fx.run_tool(log, "T")
        self.assertFalse(out.exists())
        self.assertEqual(summary["unsupported"], 1)
        self.assertEqual(report["unsupported"][0]["kind"],
                         "unquoted_heredoc")

    def test_truncated_heredoc_refused(self):
        log = "cat > 'T' <<'EOF'\nhi\n"
        _proc, summary, report, out = self.fx.run_tool(log, "T")
        self.assertFalse(out.exists())
        kinds = [e["kind"] for e in report["unsupported"]]
        self.assertIn("truncated_heredoc", kinds)


class PythonBlocks(unittest.TestCase):
    def setUp(self):
        self.fx = Scratch()

    def tearDown(self):
        self.fx.close()

    def test_no_command_execution(self):
        marker = self.fx.root / "pwned.txt"
        log = ("```python\nimport os, subprocess\n"
               "os.system('touch %s')\n"
               "subprocess.run(['touch', '%s'])\n"
               "open('T', 'w').write('ok\\n')\n```\n" % (marker, marker))
        _proc, summary, _rep, out = self.fx.run_tool(log, "T")
        self.assertFalse(marker.exists())
        self.assertFalse(out.exists())
        self.assertEqual(summary["replayed"], 0)
        self.assertEqual(summary["unsupported"], 1)

    def test_other_path_write_is_not_executed(self):
        marker = self.fx.root / "pwned2.txt"
        log = ("```python\nopen('T', 'w').write('ok\\n')\n"
               "open('%s', 'w').write('pwned')\n```\n" % marker)
        _proc, summary, _rep, out = self.fx.run_tool(log, "T")
        self.assertEqual(out.read_text(), "ok\n")
        self.assertFalse(marker.exists())

    def test_literal_path_write_with_import(self):
        log = ("```python\nfrom pathlib import Path\n"
               "Path('T').write_text('v1\\n')\n```\n")
        _proc, summary, _rep, out = self.fx.run_tool(log, "T")
        self.assertEqual(out.read_text(), "v1\n")
        self.assertEqual(summary["replayed"], 1)

    def test_variable_content_refused(self):
        log = ("```python\nname = 'T'\n"
               "open(name, 'w').write('x')\n```\n")
        _proc, summary, report, out = self.fx.run_tool(log, "T")
        self.assertFalse(out.exists())
        kinds = [e["kind"] for e in report["unsupported"]]
        self.assertTrue(any(k.startswith("python_unsupported") for k in kinds))

    def test_alias_threading_replays(self):
        # Seed first via a preceding write, then the python block edits.
        seed = '{"op": "write", "filePath": "T", "content": "a\\n"}\n'
        block = ("```python\nfrom pathlib import Path\n"
                 "p = Path('T')\n"
                 "text = p.read_text()\n"
                 "fixed = text.replace('a', 'b')\n"
                 "p.write_text(fixed)\n```\n")
        _proc, summary, _rep, out = self.fx.run_tool(seed + block, "T")
        self.assertEqual(out.read_text(), "b\n")
        self.assertEqual(summary["replayed"], 2)


class PatchEvents(unittest.TestCase):
    def setUp(self):
        self.fx = Scratch()

    def tearDown(self):
        self.fx.close()

    def test_update_hunk_in_order(self):
        log = ("*** Begin Patch\n*** Update File: T\n"
               "@@ -1,2 +1,2 @@\n a\n-b\n+c\n*** End Patch\n")
        seed = '{"op": "write", "filePath": "T", "content": "a\\nb\\n"}\n'
        _proc, summary, _rep, out = self.fx.run_tool(seed + log, "T")
        self.assertEqual(out.read_text(), "a\nc\n")
        self.assertEqual(summary["replayed"], 2)

    def test_hunk_mismatch_is_unreplayed(self):
        log = ("*** Begin Patch\n*** Update File: T\n"
               "@@ -1,1 +1,1 @@\n-wrong\n+right\n*** End Patch\n")
        seed = '{"op": "write", "filePath": "T", "content": "actual\\n"}\n'
        _proc, summary, report, out = self.fx.run_tool(seed + log, "T")
        self.assertEqual(out.read_text(), "actual\n")
        kinds = [e["kind"] for e in report["unreplayed"]]
        self.assertIn("patch_hunk_mismatch", kinds)

    def test_delete_and_diff_are_refused(self):
        log = ("*** Begin Patch\n*** Delete File: T\n*** End Patch\n"
               "diff --git a/T b/T\n--- a/T\n+++ b/T\n@@ -1 +1 @@\n-x\n+y\n")
        seed = '{"op": "write", "filePath": "T", "content": "keep\\n"}\n'
        _proc, summary, report, out = self.fx.run_tool(seed + log, "T")
        self.assertEqual(out.read_text(), "keep\n")
        kinds = [e["kind"] for e in report["unsupported"]]
        self.assertIn("patch_refused", kinds)


class DigestAndSeed(unittest.TestCase):
    def setUp(self):
        self.fx = Scratch()

    def tearDown(self):
        self.fx.close()

    def test_digest_mismatch_refuses_success(self):
        log = '{"op": "write", "filePath": "T", "content": "a\\n"}\n'
        proc, summary, _rep, out = self.fx.run_tool(
            log, "T", extra=("--expect-md5", "0" * 32))
        self.assertEqual(proc.returncode, 3)
        self.assertFalse(summary["verified"])
        self.assertEqual(summary["reason"], "digest_mismatch")
        self.assertTrue(out.exists())

    def test_digest_match_verifies(self):
        digest = hashlib.md5(b"a\n").hexdigest()
        log = '{"op": "write", "filePath": "T", "content": "a\\n"}\n'
        proc, summary, _rep, _out = self.fx.run_tool(
            log, "T", extra=("--expect-md5", digest, "--expect-lines", "1"))
        self.assertEqual(proc.returncode, 0)
        self.assertTrue(summary["verified"])

    def test_read_event_seeds(self):
        log = ('{"op": "read", "filePath": "T", "content": "a\\n"}\n'
               '{"op": "edit", "filePath": "T", "oldString": "a", '
               '"newString": "b"}\n')
        _proc, summary, _rep, out = self.fx.run_tool(log, "T")
        self.assertEqual(summary["seeded"], "log_read")
        self.assertEqual(out.read_text(), "b\n")

    def test_unit_helpers(self):
        self.assertTrue(RT.parse_replace_all("true"))
        self.assertFalse(RT.parse_replace_all(0))
        self.assertIsNone(RT.parse_replace_all("maybe"))
        state, problem = RT.apply_edit("aa", "a", "b", False)
        self.assertIsNone(state)
        self.assertTrue(problem.startswith("not_unique"))
        state, problem = RT.apply_edit("aa", "a", "b", True)
        self.assertEqual((state, problem), ("bb", None))


if __name__ == "__main__":
    unittest.main()
