#!/usr/bin/env python3
"""**The bridge count** -- how many corpus programs have a Lean-checked bridge from the goal
theorem's premise (b) to GabbroV's duty files (`dokumente/AUFTRAG-GABBROV-VERIFIKATION.md`).

    ./instrumente/zaehle-bruecke.py [--binary PATH] [--allow-stale] [--nicht-lean]

Two levels, both counted over `beispiele/*.gab`, and NEITHER counts unless Lean re-ran it:

  STATEMENTS CHECKED (S1 + S2). `bruecke/Bruecke/Instanz*.lean` carries a marker
      BRIDGE-INSTANCE <program.gab> <Module>
  and counts only when
    * the source string the instance's `verankert` theorem names (`uebersetzeAllg <src> = .ok ..`)
      IS the program's file, byte for byte (the pin is read the way `zaehle-kette.py` reads it);
    * the duty file `gabbro pflichten --lean <program.gab>` PRINTS now is byte-identical to the
      committed `programmlogik/Duty/*.lean` that names the program (so the check binds what the
      printer writes, not a stale copy);
    * `lake build <Module>` in `bruecke/` is green (the per-unit `rfl` checks against the Lean
      computation of `Bruecke/Pflichten.lean`).
  CLOSED BRIDGE (S3). The instance also carries
      BRIDGE-CLOSED <program.gab> <theorem>
  and the theorem is applied in the same module, and that module builds, and its build output
  carries the `#print axioms` line of the theorem with exactly the standard three (`propext`,
  `Classical.choice`, `Quot.sound`; a missing line is not measured, `sorryAx` is not closed). A
  closed bridge says: every duty GREEN implies the goal theorem's premise (b) for this program.
  Its planted defects: `./instrumente/mutiere-bruecke.py --s3`.
  ATOMIC RELY (S4). `BRIDGE-ATOMIC <program.gab> <theorem>`: the theorem is `NutzerPflichtA` of the
  unit (the parser's units have no shared atomic), measured exactly like a closed bridge.
  END TO END (S6). `BRIDGE-CHAIN <program.gab> <def>`: the def is the closed chain (`Kette src`:
  source text, checker Bool, goal theorem, correspondence to the C -- every field a theorem) with
  its premise (b) taken from the closed bridge; it counts under the same build + axioms rule, and
  only for a program whose bridge is CLOSED. `Kette` has no field that is not proved, so a built
  def is a closed chain AND a closed bridge for the program.
  Its planted defects: `./instrumente/mutiere-bruecke.py --s3`.

A COUNTER, not a guard: exit 0 once it measured, 2 (ABBRUCH) when it measured nothing (no binary,
a binary older than the sources, a failing speech test). `--nicht-lean` skips the build (a present
instance then reads "Lean not re-run" and counts as NOT closed).
"""
import argparse, importlib.util, os, pathlib, re, subprocess, sys

W = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import korpus  # noqa: E402

_S = importlib.util.spec_from_file_location("zaehle_kette", W / "instrumente" / "zaehle-kette.py")
ZK = importlib.util.module_from_spec(_S)
_S.loader.exec_module(ZK)

BR = W / "bruecke"
MARKE_I = re.compile(r"BRIDGE-INSTANCE\s+(\S+\.gab)\s+([\w.]+)")
MARKE_C = re.compile(r"BRIDGE-CLOSED\s+(\S+\.gab)\s+(\w+)")
MARKE_A = re.compile(r"BRIDGE-ATOMIC\s+(\S+\.gab)\s+(\w+)")
MARKE_K = re.compile(r"BRIDGE-CHAIN\s+(\S+\.gab)\s+(\w+)")
QUELLE = re.compile(r"uebersetzeAllg\s+(?:[\w.]*\.)?(\w+)\s*=")
STANDARD = "[propext, Classical.choice, Quot.sound]"
LEAN_FRIST = 1800


def duty_datei(programm):
    """The committed duty file that names `programm` in its `@duty` line."""
    for p in sorted((W / "programmlogik" / "Duty").glob("Duty*.lean")):
        if re.search(r"@duty \d+\s+" + re.escape(programm) + r"\s", p.read_text(encoding="utf-8")):
            return p
    return None


def gedruckt(binary, programm):
    try:
        r = subprocess.run([str(binary), "pflichten", "--lean", programm], capture_output=True,
                           text=True, cwd=W, timeout=ZK.FRIST, env=ZK.umgebung())
    except (OSError, subprocess.TimeoutExpired):
        return None
    return r.stdout if r.returncode == 0 else None


def lake(module, extra=()):
    try:
        r = subprocess.run(["lake", "build", module, *extra], capture_output=True, text=True, cwd=BR,
                           timeout=LEAN_FRIST, env={**ZK.umgebung(), "LEAN_NUM_THREADS": "4"})
    except (OSError, subprocess.TimeoutExpired):
        return False, ""
    return r.returncode == 0, r.stdout + r.stderr


def pruefe(instanz_text, programm, modul, binary, texte, lean):
    """(ok, detail) for one BRIDGE-INSTANCE."""
    prog_text = (W / programm).read_text(encoding="utf-8")
    m = QUELLE.search(instanz_text)
    if not m:
        return False, "no `uebersetzeAllg <src> =` anchor (a `verankert` theorem)"
    src = ZK.string_def(texte, m.group(1))
    if src is None:
        return False, "source string `%s` not found or not readable" % m.group(1)
    if src != prog_text:
        return False, "source string `%s` differs from the file (stale paste)" % m.group(1)
    d = duty_datei(programm)
    if d is None:
        return False, "no committed duty file names %s" % programm
    g = gedruckt(binary, programm)
    if g is None:
        return False, "`gabbro pflichten --lean` printed nothing"
    if g != d.read_text(encoding="utf-8"):
        return False, "the printer's duty file differs from the committed %s" % d.name
    if not lean:
        return False, "Lean not re-run"
    ok, _ = lake(modul)
    if not ok:
        return False, "`lake build %s` is red" % modul
    return True, "statements checked against %s" % d.name


def geschlossen(instanz_text, programm, modul, satz, lean):
    """A closed bridge: the theorem is APPLIED after its marker, the module builds, and the build
    prints `#print axioms` of that theorem as exactly the standard three (a `sorry` would show as
    `sorryAx`; a missing print is a missing measurement, not a pass)."""
    if not lean:
        return False, "Lean not re-run"
    if not re.search(r"\b" + re.escape(satz) + r"\b", instanz_text.split("BRIDGE-CLOSED", 1)[-1].split("\n", 1)[-1]):
        return False, "theorem `%s` is not applied in the instance" % satz
    ok, out = lake(modul)
    if not ok:
        return False, "`lake build %s` is red" % modul
    zeile = re.search(r"'([\w.]*\.)?" + re.escape(satz) + r"' depends on axioms: (\[[^\]]*\])", out)
    if not zeile:
        return False, "no `#print axioms %s` in the build output (not measured)" % satz
    if zeile.group(2) != STANDARD:
        return False, "`%s` depends on %s, not the standard three" % (satz, zeile.group(2))
    return True, "closed by `%s` (axioms standard)" % satz


def eingeloest(t, marke, programm, satz, modul, lean):
    """`geschlossen` for the marker text `marke` (BRIDGE-ATOMIC / BRIDGE-CHAIN): the theorem or def
    is APPLIED after its marker; the rest is the same build + axioms rule."""
    return geschlossen(t.replace("BRIDGE-CLOSED", "BRIDGE-X").replace(marke, "BRIDGE-CLOSED"),
                       programm, modul, satz, lean)


def duty_wurzeln_verfolgt():
    """P0 guard: every root of the `Duty` lib in `bruecke/lakefile.toml` is a TRACKED file, or a
    fresh clone fails with `bad import`. Returns the list of untracked roots."""
    t = (BR / "lakefile.toml").read_text(encoding="utf-8")
    m = re.search(r'name = "Duty".*?roots = \[([^\]]*)\]', t, re.S)
    if not m:
        return ["(no `Duty` lib found in lakefile.toml)"]
    fehlt = []
    for w in re.findall(r'"([\w.]+)"', m.group(1)):
        rel = "programmlogik/" + w.replace(".", "/") + ".lean"
        r = subprocess.run(["git", "ls-files", "--error-unmatch", rel], cwd=W, capture_output=True)
        if r.returncode != 0:
            fehlt.append(rel)
    return fehlt


def selbsttest():
    """The readers refuse what they should: a marker without an anchor, and a stale pin."""
    ok = MARKE_I.search("-- BRIDGE-INSTANCE beispiele/x.gab Bruecke.X") is not None
    ok = ok and QUELLE.search("uebersetzeAllg Foo.src104real = .ok") is not None
    ok = ok and QUELLE.search("nothing") is None
    ok = ok and ZK.string_def({}, "nope") is None
    return ok


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--binary", default=str(W / "target" / "release" / "gabbro"))
    ap.add_argument("--allow-stale", action="store_true")
    ap.add_argument("--nicht-lean", action="store_true")
    a = ap.parse_args()
    if not selbsttest():
        print("ABBRUCH: the speech test fell -- this run measures nothing")
        return 2
    fehlt = duty_wurzeln_verfolgt()
    if fehlt:
        print("ABBRUCH: bridge duty files not tracked (a fresh clone would not build): %s" % ", ".join(fehlt))
        return 2
    binary = pathlib.Path(a.binary)
    if not binary.exists():
        print("ABBRUCH: no binary at %s" % binary)
        return 2
    neuer = sorted(q for q in W.glob("crates/*/src/*.rs") if q.stat().st_mtime > binary.stat().st_mtime)
    if neuer and not a.allow_stale:
        print("ABBRUCH: the binary is OLDER than %d source file(s) under crates/ (first: %s)"
              % (len(neuer), neuer[0].relative_to(W)))
        return 2
    programme = sorted(p for p in (W / "beispiele").glob("*.gab") if korpus.verfolgt(p, W))
    if not programme:
        print("ABBRUCH: empty population")
        return 2
    texte = ZK.lean_texte()
    inst, schluss, atom, kette = {}, {}, {}, {}
    for p in sorted((BR / "Bruecke").glob("Instanz*.lean")):
        t = p.read_text(encoding="utf-8")
        modul = "Bruecke." + p.stem
        for m in MARKE_I.finditer(t):
            inst[pathlib.Path(m.group(1)).name] = (m.group(1), modul, t)
        for m in MARKE_C.finditer(t):
            schluss[pathlib.Path(m.group(1)).name] = (m.group(1), modul, t, m.group(2))
        for m in MARKE_A.finditer(t):
            atom[pathlib.Path(m.group(1)).name] = (m.group(1), modul, t, m.group(2))
        for m in MARKE_K.finditer(t):
            kette[pathlib.Path(m.group(1)).name] = (m.group(1), modul, t, m.group(2))
    lean = not a.nicht_lean
    n_stmt = n_zu = n_at = n_ke = 0
    for p in programme:
        eintrag = inst.get(p.name)
        if not eintrag:
            continue
        rel, modul, t = eintrag
        ok, detail = pruefe(t, rel, modul, binary, texte, lean)
        print("  [%s%s] %s: %s" % ("S" if ok else "-", "", p.name, detail))
        if not ok:
            continue
        n_stmt += 1
        c = schluss.get(p.name)
        if c:
            ok2, d2 = geschlossen(c[2], c[0], c[1], c[3], lean)
            print("        bridge: %s: %s" % ("CLOSED" if ok2 else "open", d2))
            n_zu += ok2
            for reg, marke, tag in ((atom, "BRIDGE-ATOMIC", "atomic rely"), (kette, "BRIDGE-CHAIN", "end to end")):
                e = reg.get(p.name)
                if not (e and ok2):
                    print("        %s: open" % tag)
                    continue
                ok3, d3 = eingeloest(e[2], marke, e[0], e[3], e[1], lean)
                print("        %s: %s: %s" % (tag, "CLOSED" if ok3 else "open", d3))
                if tag == "atomic rely":
                    n_at += ok3
                else:
                    n_ke += ok3
        else:
            print("        bridge: open (no BRIDGE-CLOSED marker: the simulation theorem is not instantiated)")
    n = len(programme)
    print("== BRIDGE COUNT: %d of %d programs have their duty statements checked against the Lean "
          "computation (S1+S2); %d of %d have a CLOSED bridge (S3) (unmeasured counts as not passed) =="
          % (n_stmt, n, n_zu, n))
    print("== ATOMIC RELY: %d of %d closed bridges carry NutzerPflichtA (S4) ==" % (n_at, n_zu))
    print("== END TO END: %d of %d programs have a closed chain AND a closed bridge (S6) ==" % (n_ke, n))
    return 0


sys.exit(main())
