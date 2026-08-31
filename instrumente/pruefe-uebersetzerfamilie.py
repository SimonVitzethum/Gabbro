#!/usr/bin/env python3
"""**Zwei Uebersetzer derselben Familie sind EIN Uebersetzer mit zwei Versionsnummern.**

Stufe 9 von `pruefe-emission.sh` und `pruefe-grammatiktafel.py` fordern beide dasselbe:
*jede Datei, die durch `emit` kommt, muss `cc -Werror` bestehen.* Gemessen wurde das mit
**gcc 13.3.0** auf `ki-pc-fisch-101` und **gcc 16.2.1** lokal -- beide gaben dieselbe
Antwort, und genau das steht als Beleg gebucht. **Ein `clang` ist nie gelaufen.**

> *Zwei Versionsnummern einer Familie sind eine Messung, keine zwei.* `cc` ist auf beiden
> Rechnern ein Symlink auf `gcc`; die Zusage „das erzeugte C uebersetzt" hing damit an einer
> einzigen Uebersetzerfamilie, ohne dass irgendeine Zeile das sagte.

Dieses Werkzeug faehrt die Stufe-9-Regel ueber ZWEI Uebersetzern und meldet die
**Abweichung**: welche Datei sagt der eine an, die der andere ablehnt. Es ersetzt Stufe 9
nicht -- es misst, was Stufe 9 mit einem einzigen Uebersetzer nicht sehen kann (W7: der
Gegenstand ist ein anderer, naemlich der UNTERSCHIED).

    ./instrumente/pruefe-uebersetzerfamilie.py [--a cc] [--b clang]

**Und was es NICHT sagt** (W10): dass ein `clang`-Fehler ein Erzeugerfehler ist. Er kann
auch eine Warnung sein, die `gcc` nicht kennt. Die Ausgabe nennt je Datei die erste Zeile
der Meldung, damit der Leser das selbst entscheidet -- die Zahl verpflichtet, sie spricht
nicht frei.
"""
import pathlib
import subprocess
import sys
import tempfile

W = pathlib.Path(__file__).resolve().parent.parent
FRIST = 300
# The same flags stage 9 uses -- a different flag set would measure the flags, not the
# compiler family.
FLAGGEN = ["-std=c11", "-Wall", "-Wextra", "-Werror", "-c"]
# The same prune list the stage-9 `find` uses.
AUS = {"target", ".claude", ".lake", "arbeitsprotokoll"}
UMGEKEHRT = "-- erwartet: cc"

# **The ratchet over the difference -- and it is DEBT, not a green tick.**
#
# Measured 2026-08-31, `cc` = gcc 16.2.1 against clang 22.1.8, over 99 emitting files
# (the one `-- erwartet: cc` probe excluded): **18 files that gcc accepts and clang
# rejects**, every one of them the same class --
#
#     error: unused function 'Vtd_FRR_FR_LO' [-Werror,-Wunused-function]
#
# The emitter writes `static inline` accessors for every field of a bit-format; gcc does not
# warn about an unused `static inline` in C, clang does. **Stage 9's green never meant "the
# emitted C compiles" -- it meant "it compiles with gcc",** and nothing said so, because
# both machines' `cc` is gcc (13.3.0 there, 16.2.1 here).
#
# They stand on the ratchet in the same sense `zaehle-karten.py`'s number does: *they are
# debt, not an achievement.* The fix belongs to the emitter (`crates/gabbro-check/src/emit.rs`
# -- another track), and the number may only FALL.
MARKE_FAMILIENUNTERSCHIED = 18
# The files both families reject. They are NOT this tool's finding -- stage 9 of
# `pruefe-emission.sh` owns them and reports them, and a second register over one thing is
# W7. They are counted here and printed, and they do not colour this run.
MARKE_BEIDE_ROT = 6


def fassung(werkzeug):
    """`(pfad, erste Zeile von --version)` -- oder `None`, wenn es das Werkzeug nicht gibt."""
    try:
        r = subprocess.run([werkzeug, "--version"], capture_output=True, text=True,
                           timeout=FRIST, env={"LC_ALL": "C", "PATH": "/usr/bin:/bin"})
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return None
    if r.returncode != 0:
        return None
    return (r.stdout or "").strip().splitlines()[:1] or ["(ohne Fassung)"]


def familie(text):
    """`gcc` · `clang` · `unbekannt` -- **die Frage, um die es hier ueberhaupt geht.**"""
    t = text.lower()
    if "clang" in t:
        return "clang"
    if "gcc" in t or "free software foundation" in t:
        return "gcc"
    return "unbekannt"


def quellen():
    return sorted(p for p in W.rglob("*.gab")
                  if not (AUS & set(p.relative_to(W).parts)))


def emittiert(q, ziel):
    """Erzeugt das C -- oder `False`, wenn `C001` sich weigert (eine ehrliche Antwort)."""
    r = subprocess.run(["cargo", "run", "-q", "--manifest-path", str(W / "Cargo.toml"),
                        "--bin", "gabbro", "--", "emit", str(q)],
                       capture_output=True, text=True, timeout=FRIST, cwd=W)
    if r.returncode != 0 or not r.stdout.strip():
        return False
    ziel.write_text(r.stdout, encoding="utf-8")
    return True


def uebersetzt(werkzeug, c):
    """`(ok, erste Meldungszeile)`. `LC_ALL=C`, weil die Meldung GELESEN wird (W16)."""
    r = subprocess.run([werkzeug] + FLAGGEN + ["-o", "/dev/null", str(c)],
                       capture_output=True, text=True, timeout=FRIST,
                       env={"LC_ALL": "C", "PATH": "/usr/bin:/bin"})
    zeilen = [z for z in (r.stderr or "").splitlines() if z.strip()]
    return r.returncode == 0, (zeilen[0][:120] if zeilen else "")


def main():
    a = sys.argv[sys.argv.index("--a") + 1] if "--a" in sys.argv else "cc"
    b = sys.argv[sys.argv.index("--b") + 1] if "--b" in sys.argv else "clang"
    fa, fb = fassung(a), fassung(b)
    print("== Die zwei Uebersetzer, mit Namen und Fassung ==")
    for name, f in ((a, fa), (b, fb)):
        print(f"  {name:<8} {f[0] if f else 'FEHLT'}")
    # **A missing compiler is not a passed test** (W1): nothing was measured.
    if not fa or not fb:
        print(f"ABBRUCH: `{a if not fa else b}` gibt es auf diesem Rechner nicht -- es wurde",
              file=sys.stderr)
        print("  NICHTS gemessen. Die Frage dieses Werkzeugs ist der UNTERSCHIED zwischen",
              file=sys.stderr)
        print("  zwei Uebersetzern; mit einem davon ist sie nicht gestellt.", file=sys.stderr)
        return 2
    ka, kb = familie(fa[0]), familie(fb[0])
    print(f"  Familien: {a} -> {ka}, {b} -> {kb}")
    # **The whole point of this tool, and it is a speech test.** Two versions of one family
    # answer the same question twice; running them proves nothing and looks like proof.
    if ka == kb:
        print(f"ABBRUCH: beide sind `{ka}` -- das ist EIN Uebersetzer mit zwei Versions-",
              file=sys.stderr)
        print("  nummern, und der Unterschied zwischen ihnen ist nicht der Unterschied,",
              file=sys.stderr)
        print("  nach dem hier gefragt wird. Es wurde NICHTS gemessen.", file=sys.stderr)
        return 2
    if not (W / "Cargo.toml").is_file():
        print("ABBRUCH: kein Cargo-Baum -- ein Erzeuger, den es nicht gibt, erzeugt nichts.",
              file=sys.stderr)
        return 2

    alle = quellen()
    print()
    print(f"== {len(alle)} `.gab`-Dateien im Baum -- dieselbe Reichweite wie Stufe 9 ==")
    n_emit = 0
    nur_a, nur_b, beide_rot, umgekehrt = [], [], [], []
    with tempfile.TemporaryDirectory() as d:
        c = pathlib.Path(d) / "probe.c"
        for q in alle:
            if not emittiert(q, c):
                continue
            n_emit += 1
            rel = str(q.relative_to(W))
            ok_a, m_a = uebersetzt(a, c)
            ok_b, m_b = uebersetzt(b, c)
            if q.read_text(encoding="utf-8", errors="replace").splitlines()[:1] == [UMGEKEHRT]:
                umgekehrt.append((rel, ok_a, ok_b))
                continue
            if ok_a and not ok_b:
                nur_b.append((rel, m_b))
            elif ok_b and not ok_a:
                nur_a.append((rel, m_a))
            elif not ok_a and not ok_b:
                beide_rot.append((rel, m_a))
    einig = n_emit - len(umgekehrt) - len(nur_a) - len(nur_b)
    print(f"  {n_emit} emittieren, {len(umgekehrt)} davon sind umgekehrte Proben "
          f"(`{UMGEKEHRT}`)")
    print()
    print(f"== {einig} von {n_emit - len(umgekehrt)} Dateien: die zwei Familien sind EINIG ==")
    print(f"   davon {len(beide_rot)} einig im NEIN -- das ist ein Erzeugerfehler, den beide")
    print("   sehen, und kein Familienunterschied.")
    for rel, m in beide_rot:
        print(f"     beide rot   {rel}")
        print(f"                 {m}")
    print()
    print(f"== {len(nur_a) + len(nur_b)} Dateien, an denen sie sich UNTERSCHEIDEN ==")
    for rel, m in nur_b:
        print(f"  nur `{b}` lehnt ab   {rel}")
        print(f"                       {m}")
    for rel, m in nur_a:
        print(f"  nur `{a}` lehnt ab   {rel}")
        print(f"                       {m}")
    if umgekehrt:
        print()
        print(f"== {len(umgekehrt)} umgekehrte Proben: ihr C SOLL fallen ==")
        for rel, ok_a, ok_b in umgekehrt:
            wort = ("beide lehnen ab" if not ok_a and not ok_b else
                    f"`{a}` {'nimmt an' if ok_a else 'lehnt ab'}, "
                    f"`{b}` {'nimmt an' if ok_b else 'lehnt ab'}")
            print(f"  {rel:<44} {wort}")
        print("   **Eine Probe, die nur unter EINER Familie beisst, misst die Familie.**")
    print()
    print("== Und was das NICHT heisst ==")
    print("   Eine Ablehnung durch den einen ist nicht ohne weiteres ein Erzeugerfehler --")
    print("   sie kann eine Warnung sein, die der andere nicht kennt. Darum steht je Datei")
    print("   die erste Meldungszeile daneben. *Die Zahl verpflichtet, sie spricht nicht")
    print("   frei* (W10). Und gemessen ist der Unterschied ZWEIER Uebersetzer, nicht der")
    print("   aller: eine dritte Familie kann eine dritte Antwort geben.")

    n_unt = len(nur_a) + len(nur_b)
    print()
    print(f"== Die Ratsche: {n_unt} Unterschiede, gebucht sind {MARKE_FAMILIENUNTERSCHIED} ==")
    print("   **Das ist SCHULD, kein Erfolg.** Die gebuchte Zahl steht auf dem gemessenen")
    print("   Stand, nicht auf null -- sie ist GEZOGEN, nicht geheilt, und sie darf nur")
    print("   fallen. Die Heilung gehoert dem Erzeuger (`emit.rs`).")
    print(f"   Und {len(beide_rot)} Dateien lehnen BEIDE ab, gebucht sind "
          f"{MARKE_BEIDE_ROT} -- die gehoeren Stufe 9 von `pruefe-emission.sh` und")
    print("   faerben diesen Lauf nicht: ein zweites Register ueber einer Sache ist W7.")
    rot = 0
    if n_unt > MARKE_FAMILIENUNTERSCHIED:
        print(f"   RATSCHE GEBROCHEN: {n_unt} > {MARKE_FAMILIENUNTERSCHIED}.")
        rot = 1
    elif n_unt < MARKE_FAMILIENUNTERSCHIED:
        print(f"   FUND: {n_unt} statt {MARKE_FAMILIENUNTERSCHIED} -- die Marke gehoert"
              " nachgezogen.")
        rot = 1
    if len(beide_rot) > MARKE_BEIDE_ROT:
        print(f"   DECKE DURCHBROCHEN: {len(beide_rot)} > {MARKE_BEIDE_ROT} lehnen beide ab.")
        rot = 1
    elif len(beide_rot) < MARKE_BEIDE_ROT:
        # **A mark below its subject measures nothing** -- and it is the GOOD case that
        # breaks it: somebody healed a file and the mark stayed. It is still a finding.
        print(f"   FUND: nur noch {len(beide_rot)} statt {MARKE_BEIDE_ROT} lehnen beide ab"
              " -- die Marke gehoert nachgezogen.")
        rot = 1
    return rot


if __name__ == "__main__":
    sys.exit(main())
