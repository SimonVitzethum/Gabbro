#!/usr/bin/env python3
"""**FORM x ZUSTAENDIGKEIT aus der GRAMMATIK -- und `UNGEDECKT` muss leer sein.**

`gabbro blindstellen` rechnet Form mal Stellung ueber einem **Korpus** und nennt die leeren
Felder. Das beantwortet die Vollstaendigkeitsfrage nicht, und das Werkzeug sagt es selbst:
*der Korpus ist von der Sprache nach aussen geschrieben.* **Falle 80.**

Hier ist die Grundgesamtheit die **Grammatik**: `dokumente/SYNTAX.md` fuehrt 154 Regeln und
**219 Terminale**, und das ist die Menge, die „beliebig" meint. Je Terminal genau ein
Zustand:

    gesenkt       ein Programm mit diesem Wort emittiert C, das `cc -Werror` ANNIMMT
    abgesagt      der Erzeuger sagt es benannt ab, und ein PRUEFERFEHLER nennt es auch
    vom Pruefer   nur ein Prueferfehler nennt es; der Erzeuger sieht die Form nie
    UNGEDECKT     keines davon

> **`UNGEDECKT` ist die ganze Frage.** Alles andere ist Buchhaltung.

WARUM `gesenkt` GEMESSEN IST UND NICHT GELESEN
------------------------------------------------
Ein Wort gilt genau dann als abgesenkt, wenn es in einer `.gab`-Datei steht, die
**vollstaendig emittiert** (null Prueferfehler UND null `C001`) **und deren Erzeugnis
`cc -std=c11 -Wall -Wextra -Werror` bei `-O0` UND `-O2` annimmt**. Dann ist alles, was in
dieser Datei steht, durch den Erzeuger gegangen -- das Wort eingeschlossen -- und was dabei
herauskam, ist C. *Das ist kein Textabgleich, sondern zwei Laeufe.*

**Die zweite Haelfte kam am 2026-08-31 dazu, und sie ist eine BERICHTIGUNG.** Bis dahin hiess
`gesenkt` nur „die Datei emittiert" -- ob das Erzeugnis ueberhaupt C ist, fragte niemand.
`messung/fragmente/F06.gab` emittierte 161 Zeilen, die `cc -Werror=type-limits` zurueckwies
(*„comparison is always true due to limited range"*), und diese Tafel haette sein Wort
trotzdem als `gesenkt` gefuehrt -- siebzehn Tage lang. Die Gegenprobe gab es, aber sie lief in
Stufe 9 von `pruefe-emission.sh` ueber *Dateien*, und diese Tafel urteilt ueber *Woerter*;
**niemand hatte die beiden je aneinandergehalten.**

> *Gemessen beim Einbau: 80 von 80 uebersetzen, an zwei Uebersetzern (`gcc 13.3.0` und
> `gcc 16.2.1`), beide Stufen.* Kein Wort verlor seine Deckung. Die Verschaerfung kostete
> heute nichts -- **aber die Reichweite waechst um vier Dateien**, die Stufe 9 nie ansieht
> (`beispiele/gift/`, `messungen/`, `programmlogik/`), und ab jetzt kostet der naechste `F06`
> eine Zelle statt eines Zufalls. Die Adressen stehen in `messung/GRAMMATIKTAFEL.md` §7.

**Und es ist tragfaehig, weil der Wortschatz GESCHLOSSEN ist.** `kw.rs` fuehrt 213 der 222
Woerter als `res` -- reserviert, nirgends ein Bezeichner. Ein Vorkommen IST damit ein
Schluesselwort. Die neun `ctx`-Woerter koennen ein Bezeichner sein; **sechs von ihnen stehen
in dieser Tafel** (`r`, `w`, `x` sind einbuchstabig und fallen schon aus der Terminalmenge),
und der Lauf NENNT sie neben dem Urteil, statt sie still mitlaufen zu lassen.

DREI REGISTER, GELESEN STATT KOPIERT (W7)
-------------------------------------------
    die Terminale       `pruefe-wortschatz.py`   -- es haelt sie schon gegen die EBNF
    die Absageformen    `zaehle-absagen.py`      -- 139 Stellen, 130 Formen
    die Prueferfehler   `Absage::fehler(…)` in jeder `gabbro-check/src/*.rs` AUSSER `emit.rs`

*Ein zweites Register ueber derselben Sache laeuft weg* -- dieser Ordner hat das oft genug
bezahlt, dass es keine dritte Kopie der Terminalliste gibt.

WAS DIESE TAFEL NICHT SAGT
----------------------------
**Eine besetzte Zelle heisst, dass eine Absenkung LAEUFT und ihr Erzeugnis C IST -- nicht,
dass es das RICHTIGE C ist.** `cc -Werror` prueft die Sprache, nicht die Bedeutung: ein
`f32`-Ausdruck, der in `double` rechnet, uebersetzt tadellos (§3, Befund 1). Und ein Terminal
ist nicht dasselbe wie eine Form -- eine Regel, die aus lauter gedeckten Woertern eine
ungedeckte Kombination baut, faellt hier nicht auf. *Dafuer steht `gabbro blindstellen` ueber
dem Korpus.*

WARUM DAS TOR IM SCHNELLLAUF BLEIBT UND NICHT HINTER `--voll`
---------------------------------------------------------------
**Gemessen am 2026-08-31, nicht geschaetzt:** 0,85 s -> 5,0 s auf `ki-pc-fisch-101`, 1,0 s ->
5,7 s lokal. Der Uebersetzerdurchgang selbst kostet 1,8 s bzw. 4,0 s -- 160 `cc`-Aufrufe ueber
80 Erzeugnisse. `abnahme.py` gibt jedem leichten Waechter **600 s** (`FRIST_ABNAHME`), also
knapp ein Prozent davon.

*Die erste Fassung brauchte 9,8 s*, weil die Sprechprobe den ganzen Durchgang ein zweites Mal
fuhr, um EINE vergiftete Datei zu pruefen. **Eine Probe, die so viel kostet wie die Messung,
verdoppelt jede Abnahme** -- sie faehrt jetzt nur die eine Datei (`uebersetzende(nur=…)`) und
zeigt dieselbe Kette.

> Und der Grund ist nicht nur die Zahl: `pruefe-waechter.SCHWER` sagt ausdruecklich, dass
> keiner seiner vier Eintraege wegen der ZEIT dort steht -- es ist der **Ort** (Speicher,
> Rechenlast gehoert auf den Server) oder die **Wirkung** (es schreibt in Quellen). `cc -c`
> auf eine Uebersetzungseinheit tut weder das eine noch das andere. *Ein Waechter hinter
> `--voll`, den der Schnelllauf braucht, ist ein Waechter, den niemand faehrt.*

    ./instrumente/pruefe-grammatiktafel.py            die Tafel und das Urteil
    ./instrumente/pruefe-grammatiktafel.py --probe    nur die Sprechprobe
    ./instrumente/pruefe-grammatiktafel.py --tafel    alle 219 Zeilen
"""
import collections
import contextlib
import importlib.util
import io
import os
import pathlib
import re
import shutil
import subprocess
import sys
import time

W = pathlib.Path(__file__).resolve().parent.parent
SYNTAX = W / "dokumente" / "SYNTAX.md"
CHECK = W / "crates" / "gabbro-check" / "src"
KW = W / "crates" / "gabbro-syntax" / "src" / "kw.rs"

# **The SAME switches as stage 9 of `pruefe-emission.sh`, and that is deliberate.**
# Two guardians compiling the same erzeugnis with DIFFERENT switches give two answers to one
# question. `-Wtype-limits` sits inside `-Wextra`, and that is the diagnostic `F06` hung on.
CC_SCHALTER = ["-std=c11", "-Wall", "-Wextra", "-Werror"]
# **TWO levels, because they do not measure the same thing.** `-O2` switches on the dataflow
# analysis (`-Wmaybe-uninitialized`, `-Wstringop-overflow`); `-O0` catches what the optimiser
# folds away before it could warn about it.
CC_STUFEN = ("-O0", "-O2")
# **`LC_ALL=C`, and that is not cosmetic.** The probe below reads the MESSAGE TEXT
# ("limited range"), and a translated diagnostic turns a correct refusal into a failed probe.
# *A guardian whose verdict hangs on the locale measures the environment.*
CC_UMGEBUNG = dict(os.environ, LC_ALL="C", LANG="C", LANGUAGE="C")

# `Absage::fehler(code, span, text)` -- the message, and only the ERROR one. A `hinweis`
# does not reject: `beispiele/gift/166` carries `S007` as a hint, checks with zero errors
# and falls at `C001`. *A guardian that counts hints as refusals reads its own leniency as
# coverage.*
FEHLER = re.compile(r'Absage::fehler\([^,]+,[^,]+,\s*(?:format!\()?\s*"((?:[^"\\]|\\.)*)"', re.S)
WORT = re.compile(r"[A-Za-z_@][A-Za-z0-9_]*")


def _lade(name, argv):
    """Import an instrument as a MODULE -- its registers are read, never copied."""
    spec = importlib.util.spec_from_file_location(name.replace("-", "_").replace(".py", ""),
                                                  W / "instrumente" / name)
    mod = importlib.util.module_from_spec(spec)
    alt = sys.argv
    sys.argv = argv
    try:
        with contextlib.redirect_stdout(io.StringIO()):
            spec.loader.exec_module(mod)
    except SystemExit:
        pass          # `pruefe-wortschatz.py` ends in `sys.exit`; its globals stand
    finally:
        sys.argv = alt
    return mod


def terminale(syntax=None):
    """The EBNF terminals -- from `pruefe-wortschatz.py`, which already holds them."""
    return set(_lade("pruefe-wortschatz.py", ["x", str(syntax or SYNTAX), "--probe"]).term)


def kontextuell():
    """The `ctx` words of `kw.rs`: they may also be an identifier."""
    return {t for t, k in re.findall(r'=>\s*"([^"]+)",\s*(res|ctx);', KW.read_text()) if k == "ctx"}


def _in_ruecken(text):
    """Every word inside backticks -- that is how this folder names a Gabbro form."""
    aus = set()
    for w in re.findall(r"`([^`]+)`", text):
        aus |= set(re.findall(r"[A-Za-z_][A-Za-z0-9_]*", w))
    return aus


def absageworte():
    """The words the EMITTER names in a refusal."""
    za = _lade("zaehle-absagen.py", ["x"])
    return _in_ruecken(" ".join(t for _, t, _ in za.formen())), za


def prueferworte():
    """The words a CHECKER ERROR names -- every pass but the emitter."""
    texte = []
    for q in sorted(CHECK.glob("*.rs")):
        if q.name != "emit.rs":
            texte += FEHLER.findall(q.read_text())
    return _in_ruecken(" ".join(texte)), len(texte)


def volle_emission(korpus, wurzel=None):
    """The files that emit COMPLETELY -- 0 checker errors, 0 `C001`. Sorted."""
    wurzel = pathlib.Path(wurzel or W)
    return [d for d, e in sorted(korpus.items())
            if not e["codes"] and not e["c001"] and (wurzel / d).exists()]


def uebersetzt_c(text):
    """Does this C pass `cc -Werror` at BOTH levels? -> `(ok, first message)`.

    The C never touches the disk: `-x c -` reads it from the pipe. *A temporary file is a
    second place where a run can leave something behind*, and this one runs 160 times.
    """
    for stufe in CC_STUFEN:
        r = subprocess.run(["cc"] + CC_SCHALTER + [stufe, "-x", "c", "-c", "-o", os.devnull, "-"],
                           input=text, capture_output=True, text=True, env=CC_UMGEBUNG)
        if r.returncode != 0:
            zeilen = [z.strip() for z in r.stderr.split("\n") if ": error:" in z]
            erste = zeilen[0] if zeilen else (r.stderr.strip().split("\n") or [""])[0]
            return False, f"{stufe}  {erste}"
    return True, ""


def uebersetzende(korpus, wurzel=None, gabbro=None, verfaelsche=None, nur=None):
    """Of the completely emitting files: whose C does `cc -Werror` accept?

    Returns `(ok, schlecht)` -- a list and a `Datei -> Meldung` map.

    **The binary comes from `zaehle-absagen.binaer`, not from a second lookup here** (W7).
    That function carries the staleness latch: nothing older than any source. A second
    resolution beside it is the one that forgets it -- and a stale emitter answers for a
    lowering nobody built.

    `verfaelsche` is `(Datei, Ersatz-C)` and exists for the SPRECHPROBE: it puts an
    artificially broken erzeugnis through the very same gate the real run uses, instead of
    asserting what the gate would have done. `nur` narrows the pass to a few files --
    *a probe that costs as much as the measurement doubles every acceptance run*, and the
    probe needs one file, not eighty.
    """
    wurzel = pathlib.Path(wurzel or W)
    befehl = _lade("zaehle-absagen.py", ["x"]).binaer(wurzel, gabbro)
    ok, schlecht = [], {}
    for d in volle_emission(korpus, wurzel):
        if nur is not None and d not in nur:
            continue
        r = subprocess.run(befehl + ["emit", str(wurzel / d)], cwd=wurzel,
                           capture_output=True, text=True)
        c = r.stdout
        if verfaelsche and d == verfaelsche[0]:
            c = verfaelsche[1]
        if r.returncode != 0 or not c.strip():
            # **Zero checker errors, zero `C001`, and still no C** -- that is not coverage
            # but a hole in the emitter that does not announce itself.
            schlecht[d] = "emittiert nichts, obwohl weder Pruefer noch `C001` widersprechen"
            continue
        gut, meldung = uebersetzt_c(c)
        if gut:
            ok.append(d)
        else:
            schlecht[d] = meldung
    return ok, schlecht


def gesenkte_worte(korpus, wurzel=None, nur=None):
    """Every word of every `.gab` that emits COMPLETELY **and whose C compiles**.

    A file that produced C without a single `C001` has carried every construct in it
    through the emitter -- and if `cc -Werror` takes that C, what came out is C. *That is
    why this state is two runs and not a reading.*

    `nur` restricts the set to the files that passed the compiler; `None` means the old,
    weaker question (emission alone) and is used to MEASURE what the sharpening costs.
    """
    wurzel = pathlib.Path(wurzel or W)
    aus = set()
    dateien = []
    for d in volle_emission(korpus, wurzel):
        if nur is not None and d not in nur:
            continue
        dateien.append(d)
        # `--` to end of line is a comment: a word EXPLAINED is not a word WRITTEN.
        aus |= set(WORT.findall(re.sub(r"--.*$", "", (wurzel / d).read_text(), flags=re.M)))
    return aus, dateien


def traeger(korpus, term, pruefer, wurzel=None, dateien=None):
    """`Wort -> die Dateien, die es schreiben` -- nur fuer Woerter OHNE Prueferdeckung.

    Ein Wort, das auch ein Prueferfehler nennt, faellt nicht, wenn seine Datei ausfaellt.
    Diese Karte nennt darum genau die Woerter, fuer die die Uebersetzungsprobe die einzige
    Gegenprobe ist -- **und sie ist das, was aus einer Zahl eine Adresse macht.**
    """
    wurzel = pathlib.Path(wurzel or W)
    karte = collections.defaultdict(list)
    for d in (dateien if dateien is not None else volle_emission(korpus, wurzel)):
        worte = set(WORT.findall(re.sub(r"--.*$", "", (wurzel / d).read_text(), flags=re.M)))
        for t in worte & set(term):
            if t not in pruefer:
                karte[t].append(d)
    return karte


def tafel(term, gesenkt, absage, pruefer):
    """Terminal -> one of the four states."""
    aus = {}
    for t in sorted(term):
        if t in gesenkt:
            aus[t] = "gesenkt"
        elif t in absage and t in pruefer:
            aus[t] = "abgesagt"
        elif t in pruefer:
            aus[t] = "vom Pruefer"
        else:
            aus[t] = "UNGEDECKT"
    return aus


# **The artificial `F06` -- the very form the real one hung on** (2026-08-31).
#
# `messung/fragmente/F06.gab` lowered the field index of `elems of` as `uint32_t`, a copy
# from `slots of`. The generated comparison against the bound was therefore **always true**,
# and `cc` says so: *"comparison is always true due to limited range of data type"*
# (`-Wtype-limits`, contained in `-Wextra`). Under `-Werror` that is a rejection.
#
# *The emitter knew the form; what it made of it was not C.* This probe builds exactly that
# -- a range that forces the comparison -- and drives it through the SAME gate the real run
# uses. **Not asserted, compiled.**
GIFT_C = (
    "#include <stdint.h>\n"
    "/* die Form von `F06`: ein Index, dessen Bereich den Vergleich erzwingt */\n"
    "static uint32_t zzprobe_slots[8];\n"
    "uint32_t zzprobe_lies(uint8_t i) {\n"
    "    if (i < 256u) { return zzprobe_slots[i & 7u]; }\n"
    "    return 0u;\n"
    "}\n"
)
# **And the other direction**: a gate that says no to everything measures nothing either.
# Without this line a broken `cc` invocation (a typo in a switch, a missing `-x c`) shows up
# as *"no file compiles"* -- and that would look like 214 findings.
GUT_C = "unsigned zzprobe_gut(unsigned x) { return x + 1u; }\n"
# The message text by which the probe recognises that it fell for the RIGHT reason.
GIFT_GRUND = "limited range"


def sprechprobe(term, gesenkt, absage, pruefer, korpus=None, uebersetzt=None, wurzel=None):
    """**In DREI Richtungen seit dem 2026-08-31, und alle drei sind im Auftrag genannt.**

    * eine kuenstlich ENTFERNTE Absenkung muss die Tafel rot machen,
    * eine kuenstlich ERFUNDENE Grammatikregel auch,
    * **eine Datei, die emittiert und deren C NICHT uebersetzt, darf ihre Woerter nicht
      mehr decken** -- die Richtung, die `F06` siebzehn Tage lang offen fand,
    * und ein unveraenderter Lauf darf keines der Woerter nennen.

    *Ein Werkzeug, das ueber die Sprache urteilt und selbst ungeprueft ist, ist die
    teuerste Sorte Waechter.*
    """
    proben = []
    sauber = tafel(term, gesenkt, absage, pruefer)

    # (a) The REMOVED lowering. It takes a word that is `gesenkt` today -- the first in a
    #     fixed order, so that the probe does not travel with the corpus.
    kandidaten = sorted(t for t, z in sauber.items() if z == "gesenkt"
                        and t not in absage and t not in pruefer)
    if not kandidaten:
        proben.append(("kein Wort ist NUR durch Absenkung gedeckt -- die Probe misst nichts", False))
    else:
        w = kandidaten[0]
        gift = tafel(term, gesenkt - {w}, absage, pruefer)
        proben.append((f"entfernte Absenkung `{w}` faellt als UNGEDECKT",
                       gift[w] == "UNGEDECKT"))
        proben.append((f"und im sauberen Lauf ist `{w}` gesenkt", sauber[w] == "gesenkt"))

    # (b) The INVENTED grammar rule -- through a COPY of `SYNTAX.md`, hence through the very
    #     extraction that also yields the real 219, and not through a second one.
    import tempfile
    kopie = SYNTAX.read_text().replace("```ebnf\n", '```ebnf\nzzprobe = "zztafelprobe" ;\n', 1)
    with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False, encoding="utf-8") as f:
        f.write(kopie)
        name = f.name
    try:
        erfunden = terminale(name)
        t2 = tafel(erfunden, gesenkt, absage, pruefer)
        proben.append(("erfundene Grammatikregel `zztafelprobe` faellt als UNGEDECKT",
                       t2.get("zztafelprobe") == "UNGEDECKT"))
        proben.append(("und sie steht nicht schon in der echten Grammatik",
                       "zztafelprobe" not in term))
    finally:
        pathlib.Path(name).unlink()

    # (c) **THE COMPILER GATE -- the direction `F06` walked past.**
    #     First the gate itself: it has to reject the artificial `F06` C, and for the RIGHT
    #     reason, and it has to let valid C through. Then the CONSEQUENCE: the file that
    #     would have produced that C no longer covers its words.
    gift_ok, gift_meldung = uebersetzt_c(GIFT_C)
    proben.append(("kuenstliches `F06`-C faellt bei `cc -Werror` (beide Stufen)", not gift_ok))
    proben.append((f"und die Meldung nennt den erzwungenen Bereich ({GIFT_GRUND!r})",
                   GIFT_GRUND in gift_meldung))
    proben.append(("gueltiges C kommt durch -- das Tor sagt nicht zu allem nein",
                   uebersetzt_c(GUT_C)[0]))

    if korpus is None or uebersetzt is None:
        proben.append(("die FOLGE des Tors ist ungeprueft -- kein Korpus uebergeben", False))
        return proben

    # A file that carries a word ALONE. In a fixed order, so the probe does not travel with
    # the corpus -- the same caution as in (a).
    karte = traeger(korpus, term, pruefer, wurzel, dateien=uebersetzt)
    allein = sorted((d[0], t) for t, d in karte.items() if len(d) == 1)
    if not allein:
        proben.append(("keine Datei traegt ein Wort allein -- die Probe misst nichts", False))
        return proben
    datei, wort = allein[0]
    # **Through the SAME gate, not around it.** `verfaelsche` slips the broken C to exactly
    # this file; everything else is the real run. *A probe that SETS the result instead of
    # measuring it checks its own assumption.*
    _, schlecht2 = uebersetzende(korpus, wurzel, verfaelsche=(datei, GIFT_C), nur={datei})
    proben.append((f"`{datei}` mit `F06`-C faellt aus der Deckung", datei in schlecht2))
    proben.append(("und aus dem richtigen Grund",
                   GIFT_GRUND in schlecht2.get(datei, "")))
    gift, _ = gesenkte_worte(korpus, wurzel, nur=set(uebersetzt) - {datei})
    t3 = tafel(term, gift, absage, pruefer)
    proben.append((f"und das allein von ihr getragene `{wort}` faellt als UNGEDECKT",
                   t3.get(wort) == "UNGEDECKT"))
    proben.append((f"im sauberen Lauf ist `{wort}` gesenkt", sauber.get(wort) == "gesenkt"))
    return proben


def main():
    nur_probe = "--probe" in sys.argv
    volle_tafel = "--tafel" in sys.argv

    # **TOOTH 0 -- THE SUBJECT HAS TO BE THERE** (2026-08-31). Over a tree without
    # `dokumente/` this tool died INSIDE THE MODULE IT LOADS: `pruefe-wortschatz.py` read
    # `SYNTAX.md` at import time and the `FileNotFoundError` came back through
    # `exec_module` -- return code **1**, a traceback, and in a chain that reads like one
    # more uncovered cell. *A crash is not a refusal -- a NAMED refusal is*, and a missing
    # subject says the SETUP has to change, not the tree.
    gegenstand = [SYNTAX, KW]
    fehlend = [str(d.relative_to(W)) for d in gegenstand if not d.is_file()]
    if not CHECK.is_dir():
        fehlend.append(str(CHECK.relative_to(W)))
    if fehlend:
        print("ABBRUCH: es fehlen: %s -- es wurde NICHTS gemessen." % ", ".join(fehlend),
              file=sys.stderr)
        print("  Ohne Grammatik, Schluesselwoerter und Paesse hat die Tafel keine Achse;\n"
              "  `0 ungedeckt` waere ein Urteil ueber nichts (W1, W17).", file=sys.stderr)
        return 2

    # **And since 2026-08-31 `cc` belongs to the SUBJECT.** Without a compiler `gesenkt` is
    # yesterday's weaker question again -- and a table that does that silently reports 214
    # lowered words for a measurement it never made. *A missing tool is not a finding but an
    # environment* (W1): return code 2.
    if shutil.which("cc") is None:
        print("ABBRUCH: `cc` fehlt -- es wurde NICHTS gemessen.", file=sys.stderr)
        print("  `gesenkt` heisst seit dem 2026-08-31 *emittiert UND uebersetzt*. Ohne\n"
              "  Uebersetzer bliebe die schwaechere Frage von gestern uebrig, und die Tafel\n"
              "  saehe gruener aus, als sie geprueft hat (W1).", file=sys.stderr)
        return 2

    term = terminale()
    absage, za = absageworte()
    pruefer, n_fehler = prueferworte()

    # **The deadline sits with whoever executes, and is NAMED here instead of duplicated.**
    # `zaehle-absagen.korpuslauf` aborts per file after `za.FRIST` seconds -- and there an
    # expiry is an abort, not an empty result. *A second deadline beside it would be a
    # second register over the same thing* (W7).
    print(f"   (Frist je Datei: {za.FRIST} s, aus `zaehle-absagen.py` -- ein Ablauf bricht ab)",
          file=sys.stderr)
    korpus = za.korpuslauf()
    if korpus is None:
        print("== GRAMMATIKTAFEL: KEIN LAUF -- es wurde NICHTS gemessen ==")
        print("   Ohne `gabbro emit` ueber dem Korpus gibt es den Zustand `gesenkt` nicht,")
        print("   und ohne ihn ist jede Zelle UNGEDECKT. Das waere kein Befund, sondern")
        print("   ein fehlendes Werkzeug (W1).")
        # **2, not 1 -- and that single digit cost an hour on 2026-08-31.**
        # The refusal above says NOTHING was measured, and the return code said the opposite:
        # `1` is the colour of the four UNGEDECKT cells this tool reports on a good day. In
        # the collective run the two were indistinguishable, so a lost guardian read as a
        # known backlog. *A tool that measured nothing must not look like one that found
        # something.*
        return 2

    # **THE GATE: EMITTED IS NOT COMPILED.** Until 2026-08-31 the measurement stopped one
    # line above this, and `F06` walked past it for seventeen days.
    t_cc = time.monotonic()
    uebersetzt, faellt_durch = uebersetzende(korpus)
    t_cc = time.monotonic() - t_cc
    voll = volle_emission(korpus)
    # The old, weaker question stays COMPUTED -- it is the baseline against which the
    # sharpening names its price. *A mark without its "before" is an assertion.*
    gesenkt_alt, _ = gesenkte_worte(korpus)
    gesenkt, sauber = gesenkte_worte(korpus, nur=set(uebersetzt))

    print("== Sprechprobe -- in DREI Richtungen ==")
    proben = sprechprobe(term, gesenkt, absage, pruefer,
                         korpus=korpus, uebersetzt=uebersetzt)
    for was, ok in proben:
        print(f"  {'ok         ' if ok else 'GESCHEITERT'}  {was}")
    if not all(ok for _, ok in proben):
        print("\n! Die Tafel misst nicht, was sie behauptet. ABBRUCH.")
        return 2
    if nur_probe:
        return 0

    z = tafel(term, gesenkt, absage, pruefer)
    zahl = collections.Counter(z.values())
    ctx = kontextuell() & set(term)

    print()
    print(f"== {len(term)} EBNF-Terminale aus {SYNTAX.name}, gegen {len(sauber)} Dateien, "
          f"die emittieren UND uebersetzen ==")
    print(f"   {len(voll)} emittieren vollstaendig · {len(sauber)} davon nimmt "
          f"`cc {' '.join(CC_SCHALTER)}` an,")
    print(f"   bei {' und '.join(CC_STUFEN)} ({t_cc:.1f} s)")
    print(f"   {len(za.formen())} Absagestellen im Erzeuger · {n_fehler} Prueferfehlertexte")
    print()
    for name in ("gesenkt", "abgesagt", "vom Pruefer", "UNGEDECKT"):
        print(f"   {name:<12} {zahl.get(name, 0):>4}")

    if volle_tafel:
        print()
        for t in sorted(z):
            marke = " (ctx)" if t in ctx else ""
            print(f"   {z[t]:<12} {t}{marke}")

    offen = sorted(t for t, s in z.items() if s == "UNGEDECKT")
    print()
    if ctx:
        print(f"== {len(ctx)} KONTEXTUELLE Woerter -- ein Vorkommen kann ein Bezeichner sein ==")
        print("   " + ", ".join(sorted(ctx)))
        print("   `kw.rs` fuehrt sie als `ctx`. Fuer sie ist `gesenkt` eine OBERE Schranke;")
        print("   die anderen 213 sind reserviert, und dort ist ein Vorkommen ein Wort.")
        print()

    # **The files that emit and whose C is NOT C -- with address and message.**
    # *A cell that produces no C is an `UNGEDECKT` cell of the other kind: the emitter knows
    # the form, and what it makes of it is not one.* Whether that is the emitter's fault or
    # the program's, this table does NOT decide -- it names the address and the diagnostic,
    # and the verdict belongs to a human.
    if faellt_durch:
        print(f"== {len(faellt_durch)} Datei(en) emittieren, und ihr C faellt bei `cc -Werror` ==")
        for d in sorted(faellt_durch):
            print(f"   {d}")
            print(f"      {faellt_durch[d][:160]}")
        print("   Ihre Woerter zaehlen NICHT als gesenkt. Ob der Erzeuger die Form falsch")
        print("   absenkt oder das Programm sie falsch schreibt, steht hier nicht -- das ist")
        print("   eine Entscheidung und keine Messung.")
        print()
    else:
        print(f"== alle {len(voll)} vollstaendig emittierenden Dateien uebersetzen auch ==")
        print("   Kein Wort haengt an einem Erzeugnis, das keins ist.")
        print()

    # What the sharpening cost today -- and where it would bite.
    verloren = sorted((gesenkt_alt - gesenkt) & set(term))
    karte = traeger(korpus, term, pruefer, dateien=uebersetzt)
    allein = sorted(t for t, ds in karte.items() if len(ds) == 1)
    print("== Was diese Tafel NICHT sagt ==")
    print("   `gesenkt` heisst: das Wort steht in einer Datei, die emittiert UND deren C")
    print("   `cc -Werror` annimmt -- nicht, dass die Absenkung das RICHTIGE tut. Ein")
    print("   `f32`-Ausdruck, der in `double` rechnet, uebersetzt tadellos (§3 der Tafel).")
    print(f"   Und {len(allein)} Woerter haengen an je EINER Datei; faellt die aus der")
    print("   Uebersetzung, fallen sie mit. Die Adressen stehen in `messung/GRAMMATIKTAFEL.md` §7.")

    if offen:
        print()
        print(f"! GRAMMATIKTAFEL ROT: {len(offen)} von {len(term)} Terminalen sind UNGEDECKT.")
        print("  Die Grammatik erlaubt sie, kein Programm senkt sie ab, und keine Regel")
        print("  weist sie ab. **Das ist die Arbeitsmenge, und sie steht hier statt in")
        print("  einer Zahl:**")
        for t in offen:
            woher = []
            if t in verloren:
                # **The other kind of `UNGEDECKT`, and it needs its own sentence.**
                # Not "nobody writes it" but "it IS written, and what came of it is not C".
                # That is an address, not a hole in the corpus.
                wo = [d for d in sorted(faellt_durch) if t in
                      set(WORT.findall(re.sub(r"--.*$", "", (W / d).read_text(), flags=re.M)))]
                woher.append("steht in " + ", ".join(wo) + " -- deren C faellt bei `cc`")
            if t in absage:
                woher.append("der Erzeuger sagt ab, der Pruefer nicht")
            if t in ctx:
                woher.append("kontextuell")
            print(f"    {t:<16} {'; '.join(woher) if woher else 'niemand nennt es'}")
        return 1

    print()
    print(f"== GRAMMATIKTAFEL GRUEN: 0 von {len(term)} Terminalen UNGEDECKT ==")
    return 0


if __name__ == "__main__":
    sys.exit(main())
