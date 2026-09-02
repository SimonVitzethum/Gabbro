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
2. **Wer keine Probe traegt, die diese Spur SIEHT.** Zwei Wege hinein: ein FUNKTIONSNAME aus
   `PROBENNAME`, oder ein Markenpaar `# speech_test: begin` / `# speech_test: end` um einen
   Probenblock im Rumpf einer anderen Funktion. Wer keinen von beiden hat, hat eine leere
   PROBE-Menge -- und die Null darunter ist eine Aussage ueber diese Messung, nicht ueber
   ihn. *Am 2026-09-01 waren das 15 von 43; die Marke ist die Antwort darauf.*
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

# **THE SECOND WAY IN, AND IT EXISTS BECAUSE THE FIRST ONE WAS BLIND AT 15 OF 43.**
#
# The name rule above only sees a probe that lives in a function OF ITS OWN. Fifteen of the
# 43 traceable instruments run theirs in the body of `main`, and for those the measured zero
# said something about this trace and nothing about them (`messung/PROBENZWEIGE.md`).
#
# Two ways out were weighed. *Lifting the probe into a named function* touches the guardian
# itself -- fifteen refactorings of load-bearing code, each able to break a guardian, to make
# a measurement possible. *A marker pair* touches two comment lines per file, cannot change
# behaviour, and lives AT THE SITE, so it moves when the code moves. **Regel A: the cheaper
# apparatus first, and the subject stays untouched.**
#
#     # speech_test: begin
#     ...
#     # speech_test: end
#
# Inside the span the state is set PER LINE instead of per frame; everything called from
# there inherits it exactly as it would from a named function, and the marked lines
# themselves are subtracted like a probe body. *The two ways then measure the same thing,
# and neither is a second register over the other* (W7) -- one file uses one of them.
MARKE_ANFANG = re.compile(r"^\s*#.*\bspeech_test:\s*begin\b")
MARKE_ENDE = re.compile(r"^\s*#.*\bspeech_test:\s*end\b")


def probenspannen(pfad):
    """Line numbers between a `speech_test: begin` / `end` pair -- markers included.

    **An unbalanced pair is an error and not an empty span.** A `begin` without an `end`
    would silently swallow the whole rest of the file into the probe side, and the count
    would rise over nothing.
    """
    drin, offen = set(), None
    for nr, z in enumerate(pfad.read_text(encoding="utf-8", errors="replace").splitlines(), 1):
        if MARKE_ANFANG.search(z):
            if offen is not None:
                raise ValueError(f"{pfad.name}:{nr} zweites `begin` ohne `end`")
            offen = nr
        elif MARKE_ENDE.search(z):
            if offen is None:
                raise ValueError(f"{pfad.name}:{nr} `end` ohne `begin`")
            drin.update(range(offen, nr + 1))
            offen = None
    if offen is not None:
        raise ValueError(f"{pfad.name}:{offen} `begin` ohne `end`")
    return drin


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
    drin |= probenspannen(pfad)
    return drin


def hat_probenfunktion(pfad):
    """Does this instrument carry a probe this trace can SEE -- named or marked?"""
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
    # **The inherited half is kept apart from the effective one**, because inside a marked
    # span the effective state changes LINE BY LINE while the inherited one must not: a frame
    # called from a probe stays on the probe side even when it walks past the marker.
    geerbt = {}
    try:
        spann = probenspannen(ziel)
    except ValueError as e:
        print(f"MARKIERUNG KAPUTT: {e}", file=sys.stderr)
        spann = set()

    def lokal_still(frame, event, arg):
        if event == "return":
            zustand.pop(frame, None)
            geerbt.pop(frame, None)
        return lokal_still

    def lokal(frame, event, arg):
        if event == "line":
            if not geerbt.get(frame, False):
                zustand[frame] = frame.f_lineno in spann
            (probe if zustand.get(frame) else echt).add(frame.f_lineno)
        elif event == "return":
            zustand.pop(frame, None)
            geerbt.pop(frame, None)
        return lokal

    def global_(frame, event, arg):
        if event != "call":
            return None
        drin = zustand.get(frame.f_back, False)
        if not drin and PROBENNAME.search(frame.f_code.co_name or ""):
            drin = True
        zustand[frame] = drin
        geerbt[frame] = drin
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
#
# **12 -> 14 and 172 -> 188, and the rise is a CORRECTION, not a regression** (2026-09-01,
# same day, second reading). Nothing in the tree got worse: the marker pair took the blind
# spot from 15 of 43 down to 6, and two of the nine newly visible instruments turned out to
# carry the class after all --
#
#     pruefe-widerruf.py    2 lines   the recording path of a finding: every revoked
#                                     sentence in the tree is struck through today, so
#                                     only the poisoned copy reaches `treffer.append`
#     pruefe-zahlen.py     15 lines   8 of them the WHOLE of `lauf()`
#
# *A mark that may only fall would have hidden exactly this.* It is written down here rather
# than argued away, because the same rule protects both directions: a rise that comes from a
# sharper instrument has to say so, or it is indistinguishable from a rise that comes from
# worse code.
MARKE = 14
# **167 -> 172 within the hour, and the five are MINE** (2026-09-01). The interval that
# `abnahme.py` now prints instead of `hoechstens` brought `spanne()` and
# `unsichere_stellen()` with it -- and five of their lines are reached today only from the
# speech test, because this tree makes the acceptance end with `2` and it never gets to its
# own green ending. *The tool that counts the class caught the code written beside it in the
# same hour* -- which is what a ratchet over one's own workshop is for. The count of
# CARRIERS did not move: `abnahme.py` was already one of the twelve.
#
# **And `pruefe-zahlen.lauf()` is a THIRD form, which is why its eight lines are booked with
# a caveat and not celebrated.** The speech test drives `pruefe_eintraege(verstellen=nr)`
# over every entry, and that fills the command CACHE. The real pass afterwards reads the
# cache and never enters `lauf` at all. *The line was not unreachable -- the fixture got
# there first.* Booked as measured, because that is what the run did; named here, because
# "nothing but the fixture can get there" is exactly what it does NOT show.
# **188 -> 189 between two runs of the same hour, and the cause is point 6 of the header.**
# `pruefe-zahlen.py` ended RED in the first run (a guarded number in `TODO.md` that this very
# lane had invalidated by writing two files). Repaired, it reaches its own green ending -- and
# that ending is one more line only the probe gets to. *A guardian that goes green ADDS to
# this count, and a mark read without that sentence looks like a regression.*
#
# **189 -> 195 on 2026-09-02, and it is TWO steps with two different owners.** The mark was
# read once against a pristine `8a33ca0` (extracted with `git archive` into an empty
# directory, so nothing of the lane could reach it) and once against the lane's tree; the
# tool gives byte-identical output on a repeated run of either, so the two numbers are a
# difference and not a wobble.
#
#   189 -> 192   ALREADY STANDING at `8a33ca0`, before this lane touched anything. Not
#                measured to a cause here -- named so the next reader does not charge it to
#                the three below.
#   192 -> 195   this lane, and every one of the three is the sentence directly above:
#                `abnahme.py` goes from 16 to 19, because TWO guardians it drives stopped
#                being red. `pruefe-emission.sh` could not be PARSED at `8a33ca0` (a merge
#                had glued a mark line to its comment), and `pruefe-zahlen.py` was red on a
#                number this lane then pulled. With both green the acceptance no longer walks
#                its own abort arms, so those lines are reached by the speech test alone.
#
# *A count that rises because two guardians were repaired is the good case, and it is still a
# finding* -- which is why it stands here with its cause and not as a quiet larger number.
MARKE_ZEILEN = 195

# **Booked instead of healed -- empty, and that is a measurement.**
# *An empty booking is the only honest starting state -- what goes in has to be argued for.*
GEBUCHT = {}


def sprechprobe():
    """**In acht Richtungen, auf ERFUNDENEN Instrumenten.**

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
        # **The marker pair, and it has to measure the SAME thing the name does.** Same
        # program as `pruefe-blind.py`, except the probe lives in the body of `main` and is
        # bracketed instead of named. If the marked form found less, the fifteen would be
        # measured with a weaker instrument than the twenty-eight.
        (dp / "pruefe-markiert.py").write_text(
            "import sys\n"
            "def satz(luecke):\n"
            "    if luecke:\n"
            "        return 'mit Luecke'\n"
            "    return 'ohne Luecke'\n"
            "def main():\n"
            "    # speech_test: begin\n"
            "    if satz(True) != 'mit Luecke':\n"
            "        return 2\n"
            "    # speech_test: end\n"
            "    print(satz(False))\n"
            "    return 0\n"
            "sys.exit(main())\n", encoding="utf-8")
        # A marker pair that does not close. It must be REFUSED, not read as an empty span --
        # an unclosed `begin` would swallow the rest of the file onto the probe side.
        (dp / "pruefe-offen.py").write_text(
            "import sys\n"
            "def main():\n"
            "    # speech_test: begin\n"
            "    print('gemessen')\n"
            "    return 0\n"
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
        markiert = eine("markiert", dp / "pruefe-markiert.py")
        proben.append(("ein MARKIERTER Probenblock im Rumpf von `main` findet denselben "
                       "Zweig wie eine benannte Probe",
                       bool(markiert) and markiert["nur_probe"] == [4]
                       and hat_probenfunktion(dp / "pruefe-markiert.py")))
        try:
            probenspannen(dp / "pruefe-offen.py")
            offen_ok = False
        except ValueError:
            offen_ok = True
        proben.append(("ein `begin` ohne `end` wird ABGELEHNT und nicht als leere Spanne "
                       "gelesen", offen_ok))
    return proben


def main():
    anker = "--anker" in sys.argv
    nur = None
    if "--nur" in sys.argv:
        nur = sys.argv[sys.argv.index("--nur") + 1]

    proben = sprechprobe()
    print(f"== Sprechprobe -- auf erfundenen Instrumenten, in {len(proben)} Richtungen ==")
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
    schalen = [n for n, g in nicht if "Schalenwaechter" in g]
    ohne_probe = sorted(n for n in kann if not hat_probenfunktion(INST / n))

    print()
    print(f"== Nenner: {len(kann)} von {len(fahrbar)} Instrumenten sind ueberhaupt "
          f"spurbar ==")
    for n, g in nicht:
        print(f"   {n:<28} {g}")
    markiert = sorted(n for n in kann if probenspannen(INST / n))
    print(f"   Und {len(ohne_probe)} der {len(kann)} spurbaren tragen KEINE Probe, die diese "
          f"Spur sieht --")
    print("   weder unter einem Namen noch zwischen `speech_test: begin/end`. Ihre Null ist")
    print("   eine Aussage ueber die Messung und nicht ueber sie:")
    print("   " + (", ".join(ohne_probe) if ohne_probe else "(keiner)"))
    print(f"   {len(markiert)} tragen eine MARKIERTE Probe im Rumpf einer anderen Funktion:")
    print("   " + (", ".join(markiert) if markiert else "(keiner)"))
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
    print(f"   {len(ohne_probe)} tragen keine Probe, die diese Spur sieht. **{len(gemessen)} "
          f"von {len(fahrbar)} ist die Zahl,")
    print("   fuer die diese Antwort gilt** (W25: eine Zahl belegt ihren Nenner).")
    print()
    # **Die acht Schalenwaechter sind KEINE Null, und das muss in der Antwort stehen und
    # nicht in einer Fussnote** -- sonst liest sich `14 von 43` wie eine Aussage ueber die
    # Werkstatt. Die Absage ist GERECHNET (2026-09-01) und nicht geschaetzt.
    print(f"   **Und die {len(schalen)} Schalenwaechter sind keine Null, sondern KEIN WERT.**"
          f" Was sie zu")
    print("   messen kostete, ist ausgerechnet und nicht geschaetzt (2026-09-01, alle acht")
    print("   gruen gefahren): **142,7 s fuer EINEN Lauf je Waechter** --")
    print("     pruefe-lean-beweis.sh 78,3 · pruefe-emission.sh 33,5 · pruefe-p6-beweis.sh 19,3")
    print("     pruefe-beweise.sh 8,2 · pruefe-lean-programm.sh 2,6 · sonden 0,5 · syntax 0,3")
    print("     zaehle-fallen.sh 0,0")
    print("   **SIEBEN der acht rufen `cargo`, `cc`, `isabelle` oder `lake`.** Sie zu spuren")
    print("   hiesse, die ganze Bau- und Beweiskette in ein Messwerkzeug zu legen, das schon")
    print("   heute in `SCHWER` steht -- und `pruefe-emission.sh` steht dort selbst, wegen")
    print("   des ORTES und nicht der Zeit (`CLAUDE.md`). Dazu kaeme ein ZWEITER Spurer:")
    print("   `bash -x` misst Befehle, und die Rahmenvererbung dieser Messung braucht")
    print("   `${BASH_LINENO[*]}` in `PS4` samt Kellerrekonstruktion -- ein eigenes")
    print("   Instrument mit eigener Sprechprobe, kein Zusatz. *Abgesagt, gerechnet.*")
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
