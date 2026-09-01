#!/usr/bin/env python3
"""**How many matches in the checker does the compiler FORCE, per AST enum?**

    ./instrumente/miss-erschoepfung.py [tree] [--kind fieldless|span] [--json out]

Gabbro forbids its users a catch-all branch: `parse.rs` answers the word `switch` with
*"`match` is exhaustive and has no catch-all branch"*, and `D005` refuses a non-exhaustive
`match` over a `tagged type`. **Its own checker holds 345 `_ =>` arms.** The house answer
is the exhaustive walkers in `lib.rs` -- one choke point, many non-exhaustive consumers --
and until this tool nothing measured whether the choke point holds.

The measurement: insert a probe variant into one AST enum, repair `gabbro-syntax` by the
compiler's own suggestion, and count the `E0004` the checker crates then raise. That count
is the number of sites the compiler would FORCE a reader to visit if the language grew this
form tomorrow.

**This is a `miss-` tool, not a `pruefe-` one, and the prefix is the whole statement.**
`abnahme.py` discovers `pruefe-*`, `mutiere-*` and `zaehle-*`; this name matches none of
them, on purpose. See WHY THERE IS NO RATCHET below.

THREE TRAPS, ALL THREE MEASURED
-------------------------------
Each of these ended a run early and left a number that looked like an answer.

1. **The build stops at the first failing crate.** A probe variant breaks `ast.rs` first,
   `gabbro-check` is then never compiled at all, and the count is a statement about
   `gabbro-syntax`. `gabbro-syntax` must be made to compile BEFORE the number means
   anything -- that is what `repair()` does, and it reports how many rounds it took.

2. **`rustc` reports BYTE offsets, and these sources carry umlauts and guillemets.**
   Splicing a Python `str` by them lands somewhere else in the line. The first run of this
   measurement shredded `ast.rs` into `expected item after doc comment` and read the
   wreckage as a finding. *Repairs are applied to `bytes`.*

3. **`rustc` suggests `&ast::WirkungArt::Zz…`, which does not resolve INSIDE `ast.rs`.**
   An arm that names a path nobody can reach is a resolution error, not an exhaustiveness
   error -- and resolution runs EARLIER, so it aborts the compilation before a single
   `E0004` is raised. The suggestion is normalised down to `Enum::Variant`.

*All three share one shape with `W16`: a measuring apparatus that damages its object and
then reports the damage.* A fourth of the same family lived in this file's own first
draft: `open(path, "w").write(insert_probe(...))` truncates the file before the argument
is evaluated, so the probe was inserted into an empty string.

WHAT THE NUMBER IS NOT
----------------------
**It is not a coverage figure, and it has no denominator.** It counts matches that are
exhaustive today. It says nothing about whether a pass that is NOT forced sees the form:
such a pass may have taken the node from a `lib.rs` walker and declined it (fine), or it
may descend by hand and never see the node or the whole subtree under it (a hole). Telling
those two apart is `pruefe-abstieg.py`'s question, and it asks it for `StmtArt` only.

WHY THERE IS NO RATCHET
-----------------------
The obvious next step -- store the numbers and refuse when one falls -- was considered and
**rejected**, because the ratchet would point at the wrong event:

* A new pass with its own hand-rolled `_ =>` walker leaves every number UNCHANGED. That is
  the event with four recorded instances in this tree (the 78 holes of one build,
  `LeanReason::ALL`, `zeugnis.rs`'s `_ => "traverse"`, and `wirkungen::liest_expr`).
* Folding two duplicated exhaustive matches into one shared walker LOWERS a number. That
  is the house design -- one choke point, many consumers -- so the ratchet would go red
  at exactly the repair it exists to encourage.

*A guard whose speech test passes in both directions can still be aimed at the wrong
event.* The count is worth having as a measurement; it is not worth having as a verdict.

WHERE IT RUNS
-------------
`cargo` belongs on `ki-pc-fisch-101` (`CLAUDE.md`), in the agent's OWN directory -- this
tool WRITES INTO `crates/gabbro-syntax/src/` and puts it back byte for byte, so a second
run in the same directory measures a mixture. Same hazard as `mutiere-pruefer.py`, and the
same rule: one run, one directory.
"""
import json
import os
import re
import subprocess
import sys

ENUMS = ["ExprArt", "StmtArt", "ItemArt", "TypExpr", "WirkungArt"]
PROBE = "ZzSondeVariante"
# **A deadline, because a hang looks like "still running" and not like a finding** (R14/W20).
FRIST = 900


def absage(satz):
    """**ABORT: NOTHING was measured -- and the return value says so.**

    Return value 2, not 1: a run that measured nothing must not look like a run that
    found something. The same three states `pruefe-abstieg.py` had to learn.
    """
    print(f"ABORT: {satz}", file=sys.stderr)
    print("  NOTHING was measured -- the table above is not a statement about the checker.",
          file=sys.stderr)
    sys.exit(2)


class Baum:
    """One tree under measurement, with its `gabbro-syntax` sources held in memory."""

    def __init__(self, wurzel):
        self.wurzel = os.path.abspath(wurzel)
        self.syndir = os.path.join(self.wurzel, "crates/gabbro-syntax/src")
        self.ast = os.path.join(self.syndir, "ast.rs")
        self.cargo = os.environ.get("CARGO", "cargo")
        if not os.path.exists(self.ast):
            absage(f"{self.ast} does not exist -- wrong tree?")

    def abzug(self):
        return {p: open(os.path.join(self.syndir, p), "rb").read()
                for p in sorted(os.listdir(self.syndir)) if p.endswith(".rs")}

    def zurueck(self, abzug):
        for p, b in abzug.items():
            pfad = os.path.join(self.syndir, p)
            if open(pfad, "rb").read() != b:
                open(pfad, "wb").write(b)

    def cargo_json(self, args):
        """`cargo check`, with a deadline, its diagnostics read as JSON."""
        try:
            p = subprocess.run(
                [self.cargo, "check", "--offline", "--message-format=json"] + args,
                cwd=self.wurzel, capture_output=True, text=True, timeout=FRIST)
        except subprocess.TimeoutExpired:
            absage(f"`cargo check {' '.join(args)}` exceeded {FRIST} s")
        aus = []
        for zeile in p.stdout.splitlines():
            try:
                j = json.loads(zeile)
            except ValueError:
                continue
            if j.get("reason") == "compiler-message":
                aus.append(j["message"])
        return aus


def kennung(m):
    c = m.get("code")
    return c.get("code") if c else None


def fehler(msgs, code=None):
    return [m for m in msgs
            if m.get("level") == "error" and (code is None or kennung(m) == code)]


def haupt_span(m):
    for s in m.get("spans", []):
        if s.get("is_primary"):
            return s
    return m["spans"][0] if m.get("spans") else None


def vorschlaege(m):
    aus = []
    for kind in m.get("children", []) + [m]:
        for s in kind.get("spans", []):
            if s.get("suggested_replacement") is not None:
                aus.append(s)
    return aus


def einsetzen(text, name, art):
    """The probe variant, appended to the enum's own arm list."""
    m = re.search(r"^pub enum %s \{$" % re.escape(name), text, re.M)
    if not m:
        absage(f"enum {name} not found in ast.rs")
    ende = text.index("\n}\n", m.end())
    arm = f"    {PROBE},\n" if art == "fieldless" else f"    {PROBE}(Span),\n"
    return text[:ende + 1] + arm + text[ende + 1:]


def normalisieren(text, name):
    """Trap 3: strip `&ast::Enum::Probe` down to `Enum::Probe`, which resolves in place."""
    voll = name + "::" + PROBE
    return re.sub(r"&?(?:\w+::)*" + re.escape(voll), voll, text)


def reparieren(baum, name, budget=12):
    """Make `gabbro-syntax` compile again -- trap 1. Returns the number of rounds."""
    for runde in range(budget):
        msgs = baum.cargo_json(["-p", "gabbro-syntax"])
        errs = fehler(msgs)
        if not errs:
            return runde
        e0004 = fehler(msgs, "E0004")
        if len(e0004) != len(errs):
            rest = [(kennung(m), m["message"][:80]) for m in errs if kennung(m) != "E0004"]
            absage(f"non-E0004 error while repairing gabbro-syntax: {rest[:3]}")
        edits = {}
        for m in e0004:
            v = vorschlaege(m)
            if not v:
                absage("E0004 in gabbro-syntax with no suggestion to apply")
            # ONE repair per diagnostic: `rustc` may offer alternatives, and applying
            # several to the same match shreds the file.
            edits.setdefault(v[0]["file_name"], []).append(v[0])
        for datei, spans in edits.items():
            pfad = os.path.join(baum.wurzel, datei)
            # Trap 2: BYTES, never characters.
            roh = open(pfad, "rb").read()
            spans = sorted(spans, key=lambda s: s["byte_start"], reverse=True)
            for a, b in zip(spans, spans[1:]):
                if b["byte_end"] > a["byte_start"]:
                    absage(f"overlapping repairs in {datei}")
            for s in spans:
                ersatz = normalisieren(s["suggested_replacement"], name).encode()
                roh = roh[:s["byte_start"]] + ersatz + roh[s["byte_end"]:]
            open(pfad, "wb").write(roh)
    absage(f"repair budget exhausted for gabbro-syntax ({budget} rounds)")


def varianten(baum, name):
    """The denominator, read from `ast.rs` -- a count beside a count."""
    text = open(baum.ast).read()
    m = re.search(r"^pub enum %s \{$" % re.escape(name), text, re.M)
    if not m:
        absage(f"enum {name} not found in ast.rs")
    rumpf = text[m.end():text.index("\n}\n", m.end())]
    rumpf = re.sub(r"///.*", "", rumpf)
    return len(re.findall(r"^    [A-Z]\w*", rumpf, re.M))


def messen(baum, name, art, ziele):
    abzug = baum.abzug()
    # **The denominator is read BEFORE the probe goes in.** Counted afterwards it counts
    # the probe too, and every enum reports one variant more than it has.
    n_var = varianten(baum, name)
    try:
        # Computed BEFORE the file is opened for writing: `open(…, "w")` truncates, and
        # Python evaluates the receiver before the argument.
        geprobt = einsetzen(open(baum.ast).read(), name, art)
        open(baum.ast, "w").write(geprobt)
        runden = reparieren(baum, name)
        msgs = baum.cargo_json(ziele)
        errs = fehler(msgs)
        e0004 = fehler(msgs, "E0004")
        fremd = sorted({(kennung(m), m["message"][:60])
                        for m in errs if kennung(m) != "E0004"})
        if fremd:
            absage(f"the checker failed for a reason that is not E0004: {fremd[:3]}")
        stellen = sorted((haupt_span(m)["file_name"], haupt_span(m)["line_start"])
                         for m in e0004)
        return {"enum": name, "kind": art, "variants": n_var,
                "n": len(stellen), "sites": stellen, "syntax_rounds": runden}
    finally:
        baum.zurueck(abzug)
        if baum.abzug() != abzug:
            absage("gabbro-syntax was NOT restored byte for byte -- the tree is a mixture")


def main():
    argv = sys.argv[1:]
    art, ziel_json = "fieldless", None
    if "--kind" in argv:
        i = argv.index("--kind")
        art = argv[i + 1]
        del argv[i:i + 2]
    if "--json" in argv:
        i = argv.index("--json")
        ziel_json = argv[i + 1]
        del argv[i:i + 2]
    if art not in ("fieldless", "span"):
        absage("--kind takes `fieldless` or `span`")
    wurzel = argv[0] if argv else os.path.join(os.path.dirname(
        os.path.abspath(__file__)), "..")
    baum = Baum(wurzel)
    ziele = ["-p", "gabbro-check", "-p", "gabbro-cli"]

    print(f"== the sites the compiler FORCES, per AST enum ({art} probe) ==")
    erg = [messen(baum, n, art, ziele) for n in ENUMS]
    for r in erg:
        je = {}
        for f, _ in r["sites"]:
            b = os.path.basename(f)
            je[b] = je.get(b, 0) + 1
        rest = " ".join(f"{k} {v}" for k, v in sorted(je.items(), key=lambda kv: -kv[1]))
        print(f"  {r['enum']:<11} {r['variants']:>2} variants -> {r['n']:>2} forced   {rest}")

    # **The workload beside the verdict** -- without it a green run and an empty one look
    # alike. Five probes, and the crates each one actually reached.
    print(f"  -- {len(erg)} enums probed, "
          f"{sum(r['n'] for r in erg)} forced sites in total, "
          f"targets: {' '.join(ziele)}")
    print("  -- NOT measured: whether an unforced pass sees the form. A `_ =>` may be a"
          " node declined")
    print("     (handed over by a `lib.rs` walker) or a node never seen (hand descent)."
          " See `pruefe-abstieg.py`.")
    if ziel_json:
        with open(ziel_json, "w") as fh:
            json.dump(erg, fh, indent=1)
        print(f"  -- written to {ziel_json}")


if __name__ == "__main__":
    main()
