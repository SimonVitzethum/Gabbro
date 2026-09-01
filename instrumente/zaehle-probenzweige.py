#!/usr/bin/env python3
"""**Wie viele Instrumente haben einen Zweig, den nur die Sprechprobe je erreicht hat?**

Bei `abnahme.py` ist es nachgewiesen und es steht als offener Posten im Plan: der Zweig
`92 von 92` -- die Schlusszeile ohne benannte Luecke -- ist **nur** durch die Sprechprobe
belegt. Ein echter Lauf hat ihn nie erreicht, weil in jedem echten Lauf etwas ausgelassen
ist. *Der Satz, den ein Leser fuer das gute Ende haelt, ist bisher nur auf erfundenen
Waechtern gedruckt worden.*

> **Ein Zweig, den nur die Sprechprobe erreicht, ist nicht falsch -- er ist UNBELEGT.** Die
> Probe zeigt, dass er tut, was er soll, wenn man ihn erreicht. Sie zeigt nicht, dass die
> Welt ihn je erreicht. *Dieselbe Klasse wie ein Anker, der ins Leere zeigt: was daran
> haengt, wird nie geprueft, und der Nenner sagt es nicht.*

Gemessen wird mit einer **geteilten Zeilenspur**: der Waechter laeuft in einem eigenen
Prozess unter `sys.settrace`, und jede ausgefuehrte Zeile seiner eigenen Datei wird einer
von zwei Mengen zugeschlagen --

    PROBE   irgendein Rahmen auf dem Aufrufkeller ist eine Probenfunktion
    ECHT    keiner ist es

Was zaehlt, ist `PROBE ohne ECHT`, **abzueglich der Probenkoerper selbst**. Dass eine
Sprechprobe ihre eigenen Zeilen erreicht, ist kein Befund; dass sie eine Zeile in der
Nutzarbeit erreicht, die sonst niemand erreicht, ist einer.

    ./instrumente/zaehle-probenzweige.py [--anker] [--nur NAME]

`--anker` ist die billige Haelfte: **nur der Nenner**, kein einziger Lauf. Sie beantwortet
*wie viele der Instrumente kann diese Messung ueberhaupt sehen* -- und das ist die Zahl, die
hier wichtiger ist als das Ergebnis.

WAS DIESE MESSUNG NICHT SIEHT
------------------------------
*Der Nenner steht vor dem Zaehler* -- so, wie `zaehle-verdrahtung.py` sein *„blind bei 3 von
6"* nennt.

1. **Schalenwaechter.** Acht der Instrumente sind `sh`; hier laufen Python-Zeilen durch eine
   Python-Spur. Fuer sie ist die Zahl **kein Null, sondern kein Wert.**
2. **Wer keine Probenfunktion mit Namen hat.** Die Spur erkennt eine Probe an ihrem
   FUNKTIONSNAMEN. Ein Waechter, dessen Probe im Rumpf von `main` steht, hat eine leere
   PROBE-Menge -- und die Null darunter ist eine Aussage ueber diese Messung, nicht ueber
   ihn.
3. **Die Teuren.** Wer baut oder in Quellen schreibt, laeuft hier nicht (`SCHWER` aus
   `pruefe-waechter.py`). `mutiere-pruefer.py` laeuft mit `--anker` wie im Schnellauf -- was
   hinter dem vollen Lauf liegt, ist ungesehen.
4. **ANWEISUNGEN, nicht Zweige.** Ein `if` ohne `else`, dessen Bedingung nie greift, hat
   keine Zeile, die fehlen koennte. Was hier `Zweig` heisst, ist eine ausgefuehrte
   Anweisungszeile.
5. **EIN Lauf, EIN Satz Argumente.** Wer Betriebsarten hat, wird in einer gefahren. Eine
   Zeile, die nur `--voll` erreicht, steht nicht in ECHT -- beruehrt die Probe sie, faellt
   sie hier auf, und das ist eine Ueberschaetzung in die sichere Richtung.
6. **Den Zustand des Baumes am Messtag.** Ein Waechter, der heute ROT endet, erreicht sein
   gruenes Ende nicht -- und dessen Zeilen sehen dann probenbelegt aus. Die Tafel nennt
   darum den Ruecklaufwert jedes Laufs daneben.
7. **Sich selbst.** Dieses Werkzeug faehrt die anderen; sich selbst zu fahren hiesse, sich
   selbst zu fahren. *Dieselbe Klasse wie das `pgrep -f`, das sich in `CLAUDE.md` selbst
   gefunden hat* -- ein Messgeraet, das seinen eigenen Namen mitzaehlt.

**Und die Richtung der Vergroeberung:** eine Zeile, die BEIDE Mengen trifft, faellt heraus.
Der Zaehler ist damit eine UNTERE Schranke fuer das, was die Probe allein traegt, und die
Punkte 5 und 6 heben ihn nach oben. *Er irrt in beide Richtungen, und beide stehen hier.*
"""
import ast
import importlib.util
import json
import pathlib
import re
import runpy
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import abschnitt  # noqa: E402  -- the shared cut notice

W = pathlib.Path(__file__).resolve().parent.parent
INST = W / "instrumente"
SELBST = pathlib.Path(__file__).name
FRIST = 600

# A probe is recognised by the FUNCTION NAME, and the word set is the one this workshop
# already uses for the text (`pruefe-waechter.HAT_PROBE`), read at name level:
# anything carrying `sprechprobe` / `selbsttest` / `gegenprobe`, plus the German compound
# form that ENDS in `-probe` / `-proben`.
#
# **The trailing anchor is not decoration, it was measured.** A bare `probe` anywhere in the
# name pulls in `pruefe-waechter.stumme_probe_mit_eins`, which is a measuring function and
# not a probe, and `mutiere-pruefer.proben_laufen`, which runs `cargo test`. Both would then
# donate every line they touch to the PROBE side and the count would rise over nothing.
# *A rule with false alarms gets ignored, and then it protects nothing.*
PROBENNAME = re.compile(r"sprechprobe|selbsttest|gegenprobe|speech_test|probe[n]?$", re.I)


def register():
    """The registers out of `pruefe-waechter.py` and `abnahme.py` -- READ, never copied (W7).

    The hyphen in both file names rules out a plain `import`.
    """
    def lade(name):
        spec = importlib.util.spec_from_file_location(name.replace("-", "_").replace(".py", ""),
                                                      INST / name)
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        return mod
    return lade("pruefe-waechter.py"), lade("abnahme.py")


def probenkoerper(pfad):
    """Line numbers lexically inside a function whose NAME is a probe name.

    **These are subtracted from the count and that is the whole point of the measure.** A
    speech test reaches its own body; a speech test that reaches into the working code and
    nothing else does is the finding.
    """
    try:
        baum = ast.parse(pfad.read_text(encoding="utf-8", errors="replace"))
    except SyntaxError:
        return None
    drin = set()
    for k in ast.walk(baum):
        if isinstance(k, (ast.FunctionDef, ast.AsyncFunctionDef)) and PROBENNAME.search(k.name):
            drin.update(range(k.lineno, (k.end_lineno or k.lineno) + 1))
    return drin


def hat_probenfunktion(pfad):
    """Does this instrument carry a probe under a NAME the trace can see?"""
    koerper = probenkoerper(pfad)
    return bool(koerper)


def je_funktion(pfad):
    """`{line: (name, first, last)}` -- the INNERMOST function each line lies in.

    **This is what tells the two classes of an unproven branch apart**, and they are not the
    same thing:

    * a whole function that the real run never ENTERS -- `abnahme.schlusssatz` is one. The
      run has no path to it at all; the probe is the only caller there has ever been.
    * a line inside a function the run does enter, which the run never takes -- almost always
      a finding path in a guardian that finds nothing today. *Reachable, unproven, and it
      becomes proven the moment the tree breaks.*

    Both are unproven. Only the first says that nothing but the fixture can get there.
    """
    try:
        baum = ast.parse(pfad.read_text(encoding="utf-8", errors="replace"))
    except SyntaxError:
        return {}
    karte = {}
    for k in ast.walk(baum):
        if not isinstance(k, (ast.FunctionDef, ast.AsyncFunctionDef)):
            continue
        # **The span starts at the BODY, not at the `def`** -- and the probe caught it.
        # Executing a `def` line DEFINES the function; it happens at module level in every
        # run, so a span that included it made every function look entered and the sharper
        # class came out empty over the whole tree. *A rule that counts the definition counts
        # the file being read.*
        a, e = k.body[0].lineno, (k.end_lineno or k.lineno)
        for z in range(a, e + 1):
            vor = karte.get(z)
            # innermost wins: a nested def has the narrower span
            if vor is None or (e - a) < (vor[2] - vor[1]):
                karte[z] = (k.name, a, e)
    return karte


# ---------------------------------------------------------------- the child: one trace
def spur(ziel, ablage, argv):
    """Run one instrument under a split line trace and write the two sets to `ablage`.

    The state is kept per FRAME and inherited at the call: a frame is *in the probe* when its
    parent was, or when its own name is a probe name. So everything a speech test calls --
    however deep, and through however many files -- lands on the PROBE side, and the same
    function called from `main` lands on the ECHT side. *Attributing by function instead of
    by call chain would book every helper as probe-only the moment a probe touched it.*
    """
    zieltext = str(ziel)
    probe, echt, zustand = set(), set(), {}

    def lokal_still(frame, event, arg):
        if event == "return":
            zustand.pop(frame, None)
        return lokal_still

    def lokal(frame, event, arg):
        if event == "line":
            (probe if zustand.get(frame) else echt).add(frame.f_lineno)
        elif event == "return":
            zustand.pop(frame, None)
        return lokal

    def global_(frame, event, arg):
        if event != "call":
            return None
        drin = zustand.get(frame.f_back, False)
        if not drin and PROBENNAME.search(frame.f_code.co_name or ""):
            drin = True
        zustand[frame] = drin
        if frame.f_code.co_filename == zieltext:
            return lokal
        # Frames outside the instrument still carry the state on -- they merely do not get
        # their lines counted. `f_trace_lines = False` is what keeps that cheap.
        frame.f_trace_lines = False
        return lokal_still

    sys.argv = [zieltext] + list(argv)
    rc, sturz = 0, ""
    sys.settrace(global_)
    try:
        runpy.run_path(zieltext, run_name="__main__")
    except SystemExit as e:
        rc = e.code if isinstance(e.code, int) else 1
    except BaseException as e:                     # noqa: BLE001 -- a crash is a datum here
        rc, sturz = 1, f"{type(e).__name__}: {e}"
    finally:
        sys.settrace(None)

    koerper = probenkoerper(ziel) or set()
    nur_probe = sorted((probe - echt) - koerper)
    karte = je_funktion(ziel)
    betreten = {karte[z][0:2] for z in echt if z in karte}
    ganz = [z for z in nur_probe if z in karte and karte[z][0:2] not in betreten]
    ablage.write_text(json.dumps({
        "rc": rc, "sturz": sturz,
        "probe": len(probe), "echt": len(echt),
        "nur_probe": nur_probe,
        "ganz": ganz,
        "ganz_funktionen": sorted({karte[z][0] for z in ganz}),
        "im_koerper": len((probe - echt) & koerper),
    }), encoding="utf-8")


# ---------------------------------------------------------------- the parent: the census
def fahrbarkeit(pw, ab):
    """`{name: (fahrbar, grund, argumente)}` over every instrument BUT this one.

    **The denominator, and it is built from the same registers the acceptance uses** (W7):
    `SCHWER` says who is expensive and why, `SCHNELL_TEIL` says who has a cheap half,
    `ARGUMENTE` says who cannot start alone, `korpus_fehlt` says whose subject is absent.
    Nothing here is a second list over the same thing -- only the shell exclusion is this
    file's own, and it is a property of the measuring apparatus, not of the guardian.
    """
    aus = {}
    # **`abnahme.py` stands in the population, and it is the reason this file exists.** It is
    # not in `besetzung()` -- that register is the CAST, and the acceptance is the one who
    # drives it -- but `pruefe-waechter.TRAEGT_URTEIL` names it, and the branch this whole
    # measure was written after (its `92 of 92` branch) is its. *A yardstick that cannot see the one
    # case with a known answer is a claim.*
    for p in list(ab.besetzung(INST)) + [INST / "abnahme.py"]:
        if p.name == SELBST:
            continue
        if p.suffix == ".sh":
            aus[p.name] = (False, "Schalenwaechter -- diese Spur liest Python-Zeilen", [])
            continue
        fehlt = pw.korpus_fehlt(p.name)
        if fehlt:
            aus[p.name] = (False, f"fremder Korpus fehlt: {fehlt[1]}", [])
            continue
        args = [str(pw.korpus_ort(a)) if (a.startswith("~") or a.startswith("..")) else a
                for a in pw.ARGUMENTE.get(p.name, [])]
        if p.name in pw.SCHWER:
            if p.name not in ab.SCHNELL_TEIL:
                aus[p.name] = (False, "teuer: " + pw.SCHWER[p.name], [])
                continue
            args = ab.SCHNELL_TEIL[p.name]
        aus[p.name] = (True, "", args)
    return aus


def messe(fahrbar, nur=None):
    """Run every runnable instrument under the trace. `[(name, ergebnis|None, grund)]`."""
    aus = []
    with tempfile.TemporaryDirectory() as d:
        for name, (kann, grund, args) in sorted(fahrbar.items()):
            if nur and name != nur:
                continue
            if not kann:
                aus.append((name, None, grund))
                continue
            ablage = pathlib.Path(d) / (name + ".json")
            t0 = time.monotonic()
            try:
                subprocess.run(
                    [sys.executable, str(pathlib.Path(__file__).resolve()), "--spur",
                     str(INST / name), str(ablage)] + list(args),
                    cwd=W, capture_output=True, text=True, timeout=FRIST)
            except subprocess.TimeoutExpired:
                aus.append((name, None, f"HAENGT unter der Spur -- Frist {FRIST} s"))
                continue
            if not ablage.is_file():
                aus.append((name, None, "die Spur hat nichts abgelegt -- kein Wert"))
                continue
            e = json.loads(ablage.read_text(encoding="utf-8"))
            e["dauer"] = time.monotonic() - t0
            e["args"] = list(args)
            aus.append((name, e, ""))
    return aus


# **THE RATCHET -- it may only FALL, and either half moves it.**
# Measured 2026-09-01 over `acec1df`, locally (31 GB total / 13 available, 20 cores), over the
# 43 instruments this trace can see out of 52, in 5 min 30 s:
#
#     12 of 43 instruments carry such a branch      167 statement lines
#      4 of them a WHOLE function the run never enters, 37 lines
#
# The first number counts INSTRUMENTS: whoever carries one such branch carries the class. The
# second is there because one instrument moved 69 of the 167 on its own -- *a count of
# carriers says nothing about how much each one carries.*
#
# **And it is an upper bound over a tree in a given state** (point 6 of the header). A
# guardian that ends RED today does not reach its own green ending, and those lines then look
# probe-borne. The table prints every return code beside the count, so a rise can be told
# apart from a repair -- and a rise errs towards red, which is the direction a mark may err in.
MARKE = 12
MARKE_ZEILEN = 167

# **Booked instead of healed -- empty, and that is a measurement.**
# *An empty booking is the only honest starting state -- what goes in has to be argued for.*
GEBUCHT = {}


def sprechprobe():
    """**In sechs Richtungen, auf ERFUNDENEN Instrumenten.**

    Die Spur ist der ganze Waechter; eine Probe, die nur die Tafel prueft, prueft die
    Beschriftung. Also laufen hier vier gebaute Instrumente wirklich durch dieselbe Spur, die
    oben die echten misst -- *ein Waechter, dessen Probe die Regel nachbaut, beweist, dass die
    Kopie funktioniert.*

    Die letzte Richtung ist die, die den Zaehler ehrlich haelt: ein Instrument OHNE benannte
    Probenfunktion darf nicht als sauber durchgehen, sondern muss als blind auffallen. *Sonst
    misst diese Zahl die Abwesenheit einer Probe als Abwesenheit eines Befunds.*
    """
    proben = []
    with tempfile.TemporaryDirectory() as d:
        dp = pathlib.Path(d)
        # One branch that only the invented fixture reaches: `satz(True)` is called by the
        # probe alone, `satz(False)` by the run.
        (dp / "pruefe-blind.py").write_text(
            "import sys\n"
            "def satz(luecke):\n"
            "    if luecke:\n"
            "        return 'mit Luecke'\n"
            "    return 'ohne Luecke'\n"
            "def sprechprobe():\n"
            "    return satz(True) == 'mit Luecke'\n"
            "def main():\n"
            "    print(satz(False))\n"
            "    return 0\n"
            "if not sprechprobe():\n"
            "    sys.exit(2)\n"
            "sys.exit(main())\n", encoding="utf-8")
        # The counter-direction: the probe drives the SAME branch the run drives.
        (dp / "pruefe-belegt.py").write_text(
            "import sys\n"
            "def satz(luecke):\n"
            "    if luecke:\n"
            "        return 'mit Luecke'\n"
            "    return 'ohne Luecke'\n"
            "def sprechprobe():\n"
            "    return satz(False) == 'ohne Luecke'\n"
            "def main():\n"
            "    print(satz(False))\n"
            "    return 0\n"
            "if not sprechprobe():\n"
            "    sys.exit(2)\n"
            "sys.exit(main())\n", encoding="utf-8")
        # A probe whose own body is the only thing it reaches -- the body is subtracted, so
        # this must count as ZERO. Without that subtraction every instrument would score.
        (dp / "pruefe-nurkoerper.py").write_text(
            "import sys\n"
            "def sprechprobe():\n"
            "    a = 1\n"
            "    b = a + 1\n"
            "    return b == 2\n"
            "def main():\n"
            "    print('gemessen')\n"
            "    return 0\n"
            "if not sprechprobe():\n"
            "    sys.exit(2)\n"
            "sys.exit(main())\n", encoding="utf-8")
        # A whole function the real run never enters -- `abnahme.schlusssatz` in miniature.
        # It has to fall into the SHARPER class, and `pruefe-blind.py` above into the milder
        # one; a mark that calls every unproven line `ganz` would pass with one fixture.
        (dp / "pruefe-ganz.py").write_text(
            "import sys\n"
            "def ohne_luecke():\n"
            "    return 'alles gesehen'\n"
            "def sprechprobe():\n"
            "    return ohne_luecke() == 'alles gesehen'\n"
            "def main():\n"
            "    print('mit Luecke')\n"
            "    return 0\n"
            "if not sprechprobe():\n"
            "    sys.exit(2)\n"
            "sys.exit(main())\n", encoding="utf-8")
        # No probe under a name the trace can see. It must fall out as BLIND, never as clean.
        (dp / "pruefe-namenlos.py").write_text(
            "import sys\n"
            "def main():\n"
            "    print('gemessen')\n"
            "    return 0\n"
            "sys.exit(main())\n", encoding="utf-8")

        def eine(name, ziel):
            ablage = dp / (name + ".json")
            subprocess.run([sys.executable, str(pathlib.Path(__file__).resolve()), "--spur",
                            str(ziel), str(ablage)],
                           cwd=dp, capture_output=True, text=True, timeout=FRIST)
            return json.loads(ablage.read_text(encoding="utf-8")) if ablage.is_file() else None

        blind = eine("blind", dp / "pruefe-blind.py")
        belegt = eine("belegt", dp / "pruefe-belegt.py")
        koerper = eine("koerper", dp / "pruefe-nurkoerper.py")
        ganz = eine("ganz", dp / "pruefe-ganz.py")
        proben.append(("ein Zweig, den NUR die Probe erreicht, wird gefunden",
                       bool(blind) and blind["nur_probe"] == [4]))
        proben.append(("eine Funktion, die der echte Lauf nie betritt, faellt in die "
                       "SCHAERFERE Klasse",
                       bool(ganz) and ganz["ganz"] == [3]
                       and ganz["ganz_funktionen"] == ["ohne_luecke"]))
        proben.append(("und ein Zweig IN einer betretenen Funktion nicht -- "
                       "die zwei Klassen sind zwei",
                       bool(blind) and blind["ganz"] == []))
        proben.append(("und einer, den der echte Lauf AUCH erreicht, nicht -- "
                       "die Marke faellt nicht ueberall",
                       bool(belegt) and belegt["nur_probe"] == []))
        proben.append(("der Probenkoerper selbst zaehlt NICHT mit",
                       bool(koerper) and koerper["nur_probe"] == []
                       and koerper["im_koerper"] > 0))
        proben.append(("wer keine benannte Probe hat, faellt als BLIND auf und nicht als sauber",
                       hat_probenfunktion(dp / "pruefe-blind.py")
                       and not hat_probenfunktion(dp / "pruefe-namenlos.py")))
    return proben


def main():
    anker = "--anker" in sys.argv
    nur = None
    if "--nur" in sys.argv:
        nur = sys.argv[sys.argv.index("--nur") + 1]

    print("== Sprechprobe -- auf erfundenen Instrumenten, in sechs Richtungen ==")
    proben = sprechprobe()
    for was, ok in proben:
        print(f"  {'ok         ' if ok else 'GESCHEITERT'}  {was}")
    if not all(ok for _, ok in proben):
        print("\nABBRUCH: die Spur misst nicht, was sie behauptet -- es wurde NICHTS "
              "gemessen.", file=sys.stderr)
        return 2

    pw, ab = register()
    fahrbar = fahrbarkeit(pw, ab)
    if not fahrbar:
        print("\nABBRUCH: kein Instrument gefunden -- die Grundgesamtheit ist leer, und ein "
              "positives Urteil ueber nichts ist keines (W17).", file=sys.stderr)
        return 2

    kann = sorted(n for n, (k, *_) in fahrbar.items() if k)
    nicht = sorted((n, g) for n, (k, g, _) in fahrbar.items() if not k)
    ohne_probe = sorted(n for n in kann if not hat_probenfunktion(INST / n))

    print()
    print(f"== Nenner: {len(kann)} von {len(fahrbar)} Instrumenten sind ueberhaupt "
          f"spurbar ==")
    for n, g in nicht:
        print(f"   {n:<28} {g}")
    print(f"   Und {len(ohne_probe)} der {len(kann)} spurbaren tragen KEINE Probe unter "
          f"einem Namen,")
    print("   den diese Spur sieht -- ihre Null ist eine Aussage ueber die Messung und")
    print("   nicht ueber sie:")
    print("   " + (", ".join(ohne_probe) if ohne_probe else "(keiner)"))
    print(f"   **Dieses Werkzeug selbst steht nicht im Nenner.** Es faehrt die anderen; "
          f"sich")
    print("   selbst zu fahren hiesse, sich selbst zu fahren -- dieselbe Klasse wie das")
    print("   `pgrep -f`, das sich in `CLAUDE.md` selbst gefunden hat.")

    if anker:
        print()
        print("== ANKER: nur der Nenner, kein Lauf ==")
        print("   Der volle Lauf faehrt die spurbaren Instrumente einzeln unter")
        print("   `sys.settrace` und zaehlt die Zeilen, die nur die Sprechprobe erreicht.")
        abschnitt.fertig()
        return 0

    ergebnisse = messe(fahrbar, nur)
    gemessen = [(n, e) for n, e, _ in ergebnisse if e]
    if not gemessen:
        print("\nABBRUCH: kein einziger Lauf hat eine Spur hinterlassen -- es wurde NICHTS "
              "gemessen.", file=sys.stderr)
        return 2

    mit_zweig = [(n, e) for n, e in gemessen if e["nur_probe"]]
    mit_ganz = [(n, e) for n, e in gemessen if e["ganz"]]
    zeilen_gesamt = sum(len(e["nur_probe"]) for _, e in gemessen)
    ganz_gesamt = sum(len(e["ganz"]) for _, e in gemessen)

    print()
    print(f"== Gemessen: {len(gemessen)} Instrumente unter der geteilten Spur ==")
    print("   Spalten: nur-Probe-Zeilen · davon in einer Funktion, die der echte Lauf NIE")
    print("   betreten hat · [Probenzeilen/echte Zeilen]")
    for n, e in gemessen:
        z, g = e["nur_probe"], e["ganz"]
        marke = f"{len(z):>3}" if z else "  -"
        gm = f"{len(g):>3} ganz" if g else "       "
        wink = "" if e["rc"] == 0 else f"  (Lauf endete mit {e['rc']})"
        wo = ("  " + ", ".join(e["ganz_funktionen"][:4])) if g else ""
        print(f"  {n:<28} {marke} {gm}  [{e['probe']:>4}/{e['echt']:>4}]{wink}{wo}")

    print()
    print(f"== ANTWORT: {len(mit_zweig)} von {len(gemessen)} gemessenen Instrumenten tragen "
          f"einen Zweig, ==")
    print(f"   den nur die Sprechprobe je erreicht hat -- {zeilen_gesamt} Anweisungszeilen.")
    print(f"   Der Nenner der FRAGE ist {len(fahrbar)}: {len(nicht)} sind nicht spurbar und")
    print(f"   {len(ohne_probe)} tragen keine benannte Probe. **{len(gemessen)} von "
          f"{len(fahrbar)} ist die Zahl,")
    print("   fuer die diese Antwort gilt** (W25: eine Zahl belegt ihren Nenner).")
    print()
    print(f"   **Und es sind ZWEI Klassen, nicht eine.** {len(mit_ganz)} Instrumente / "
          f"{ganz_gesamt} Zeilen liegen in")
    print("   einer Funktion, die der echte Lauf NIE BETRETEN hat -- dort ist die Probe der")
    print("   einzige Aufrufer, den es je gab. Der Rest sind Zeilen in Funktionen, die der")
    print("   Lauf betritt und deren Weg er nicht nimmt: **fast immer der Befundweg eines")
    print("   Waechters, der heute nichts findet.** Der ist erreichbar und unbelegt; die")
    print("   erste Klasse ist unbelegt UND ohne Weg dorthin.")
    rote = [n for n, e in gemessen if e["rc"] != 0]
    if rote:
        print(f"   Und {len(rote)} der gemessenen Laeufe endeten selbst nicht mit 0 -- ihr")
        print("   gruenes Ende ist heute unerreicht, und seine Zeilen sehen darum")
        print("   probenbelegt aus: " + ", ".join(rote))

    abschnitt.fertig()
    if len(mit_zweig) > MARKE or zeilen_gesamt > MARKE_ZEILEN:
        print(f"\n  RATSCHE GEBROCHEN: {len(mit_zweig)} Instrumente / {zeilen_gesamt} Zeilen, "
              f"gebucht sind {MARKE} / {MARKE_ZEILEN}.")
        print("   Ein neuer Zweig, den nur eine erfundene Fixtur erreicht, ist eine Zusage")
        print("   ohne Beleg. *Entweder der echte Lauf erreicht ihn, oder er faellt weg.*")
        return 1
    if len(mit_zweig) < MARKE or zeilen_gesamt < MARKE_ZEILEN:
        print(f"\n  Die Ratsche ist GEFALLEN: {len(mit_zweig)} / {zeilen_gesamt} statt "
              f"{MARKE} / {MARKE_ZEILEN}.")
        print("   Marke nachziehen -- eine Ratsche, die nur am Anstieg gezogen wird, ist")
        print("   eine Marke und keine Ratsche.")
        return 1
    print(f"\n== PROBENZWEIGE: {len(mit_zweig)} Instrumente / {zeilen_gesamt} Zeilen -- "
          f"auf der Marke ==")
    print("   Und was das NICHT heisst: ein belegter Zweig ist nicht dadurch ein richtiger.")
    print("   Gemessen wird, WER ihn erreicht, nicht was er tut (W10).")
    return 0


if __name__ == "__main__":
    if "--spur" in sys.argv:
        i = sys.argv.index("--spur")
        spur(pathlib.Path(sys.argv[i + 1]).resolve(), pathlib.Path(sys.argv[i + 2]),
             sys.argv[i + 3:])
        sys.exit(0)
    sys.exit(abschnitt.fahre(main))
