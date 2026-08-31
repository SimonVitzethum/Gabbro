#!/usr/bin/env python3
"""**Die Abnahme -- EIN Befehl, der JEDEN Waechter faehrt und je Waechter ein Urteil nennt.**

Am 2026-08-30 gab es 26 `pruefe-*`-Waechter und **keinen Lauf, der alle faehrt**.
`dokumente/PLAN-AUTONOM.md` §1.7 nannte elf; jede Sitzung stellte sich den Rest aus dem
Gedaechtnis zusammen. Sieben standen in KEINER Liste und in keinem Sammellauf --
`pruefe-abstieg.py`, `pruefe-aufloesung.py`, `pruefe-reichweite.py`, `pruefe-widerruf.py`,
`pruefe-lean-beweis.sh`, `pruefe-lean-programm.sh`, `pruefe-p6-beweis.sh`. Zwei rote Ratschen
sind darunter **zwei Tage lang durch vier Zusammenfuehrungen** gelaufen.

> **Ein Waechter, den niemand faehrt, ist von einem, den es nicht gibt, nicht zu
> unterscheiden.**

ABGRENZUNG ZU `pruefe-waechter.py` -- ZWEI GEGENSTAENDE, NICHT ZWEI REGISTER
----------------------------------------------------------------------------
`pruefe-waechter.py` fragt: **ist das ein taugliches Instrument?** (Frist, Sprechprobe, roter
Abbruch, Arbeitsmenge, Gebietsschema). Sein `--lauf` fuehrt zwar aus, liest aber das URTEIL
nicht -- ein Ruecklaufwert 1 ist ihm ein ordentliches Ende, denn ein Waechter DARF rot werden.

Dieser Lauf fragt das andere: **steht der Baum gruen?** Er liest genau den Ruecklaufwert, den
der andere ignoriert. *Zwei Fragen, ein Verzeichnis.*

*Damit daraus nicht zwei Register ueber einer Sache werden* (W7), haelt diese Datei **keine
eigene Liste**: `SCHWER`, `ARGUMENTE`, `FREMDER_KORPUS`, `OHNE_URTEIL` und `FRIST` werden aus
`pruefe-waechter.py` GELESEN. Wer dort einen Eintrag pflegt, pflegt ihn hier mit.

DIE BESETZUNG KOMMT AUS DEM VERZEICHNIS, NICHT AUS DIESER DATEI
----------------------------------------------------------------
Eine Liste im Skript haette dasselbe Problem eine Ebene tiefer: sie veraltet lautlos --
genau so ist §1.7 bei elf von 26 stehengeblieben. Gelesen wird `instrumente/pruefe-*`,
`instrumente/mutiere-*` und `instrumente/zaehle-*`. **Ein neuer Waechter ist damit am Tag
seiner Entstehung dabei**, und einer, der ein Argument braucht, faellt BENANNT auf.

**DIE `zaehle-*` KAMEN AM 2026-08-31 DAZU, UND DIE GRENZE HAT SICH BEWEGT, WEIL SIE
GEDRUCKT WURDE.** Bis dahin stand hier *„die `zaehle-*` sind NICHT in der Abnahme -- sie
messen, sie bewachen nicht"*, und daneben ihre Zahl, damit jemand die Grenze verschieben
kann. Der Satz war eine Behauptung, und sie wurde gemessen:

* Ueber einem LEEREN Baum gab **keiner der 18** ein gruenes Urteil. Sechs starben an einem
  `FileNotFoundError` (Ruecklaufwert 1, ein Traceback), neun druckten eine Absage und
  endeten ebenfalls mit 1. *Sie tragen alle ein Urteil -- sie hatten nur keins bekommen.*
* `zaehle-karten.py` kam ueber einer gebrochenen Ratsche **rot bei `master` an**, und kein
  Sammellauf las ihn. Genau der Satz, auf dem diese Datei steht -- diesmal gegen die
  Grenze, die diese Datei selbst gezogen hat.

Was draussen bleibt, steht in `pruefe-waechter.py:OHNE_URTEIL`, mit Namen und Grund, und
wird hier mit seiner Zahl GEDRUCKT.

SECHS URTEILE, UND ZWEI DAVON SIND DER GRUND FUER DIESE DATEI
--------------------------------------------------------------
    gruen             Ruecklaufwert 0 -- gemessen, kein Befund
    ROT               Ruecklaufwert 1 -- ALLES gemessen, und es steht etwas offen
    TEILMESSUNG       er ist VOR seiner letzten Messung ausgestiegen und sagt, WO.
                      **Etwas gemessen, aber nicht alles** -- die Zahl der Befunde
                      daneben ist damit eine UNTERE Schranke. (2026-08-31, W26)
    ABBRUCH           er hat es versucht und konnte nicht: Ruecklaufwert 2, eine
                      ueberschrittene Frist, ein Absturz. **Es wurde NICHTS gemessen.**
    NICHT FAHRBAR     sein GEGENSTAND ist nicht hier (fremder Korpus) oder er laesst sich
                      gar nicht erst starten
    ausgelassen       teuer, und der Schnellauf SAGT es

**`ABBRUCH` kam am 2026-08-31 dazu, und er hat zweimal eine Stunde gekostet, bevor es ihn
gab.** `pruefe-grammatiktafel.py` brach ab (*„es wurde NICHTS gemessen"*) -- dieselbe Marke,
dieselbe Farbe und dieselbe letzte Zeile wie die vier `UNGEDECKT`-Zellen, die er sonst
meldet. `pruefe-luecken.py` verweigerte bei unsauberem `crates/`, und auch das war in der
Sammelabnahme von einem Rueckstand nicht zu unterscheiden.

> **Ein Werkzeug, das nichts gemessen hat, darf nicht so aussehen wie eines, das etwas
> gefunden hat.** *Null Dateien ist eine Absage, kein Ergebnis* (W1, W17).

`ABBRUCH` ist NICHT dasselbe wie `NICHT FAHRBAR`: „nicht fahrbar" heisst, dass der
Gegenstand fehlt -- ein Loch mit einem Namen, und der Lauf bleibt gruen. „Abbruch" heisst,
dass der Waechter angetreten ist und kein Urteil geliefert hat. **Das macht die Abnahme rot,
mit eigenem Wort und eigenem Ruecklaufwert.**

**Und der Abbruch ueberstimmt den Befund.** Wer einen Waechter verloren hat, weiss nicht, was
der gefunden haette -- die Zahl der Befunde daneben ist dann eine untere Schranke und kein
Stand. Erst die Messapparatur, dann der Baum (`CLAUDE.md`: *ein Abbruch aus Speichermangel
ist kein Befund*).

**Ein Absturz ist keine Absage.** `pruefe-wortschatz.py` stirbt ohne Dateiargument mit
`IndexError` -- Ruecklaufwert 1, und es sieht aus wie ein Befund. Es ist keiner: das Werkzeug
hat nichts angesehen. Wer den Unterschied nicht druckt, bucht eine Luecke als Fund. Seit dem
2026-08-31 faellt ein Absturz als `ABBRUCH` -- **rot wie vorher, aber benannt**. Ob sein
Argument in `ARGUMENTE` steht, aendert die Farbe nicht mehr; es steht als Grund daneben. *Ein
angemeldetes Argument ist eine Erklaerung, kein Freibrief:* wer es bekommt und trotzdem
stuerzt, hat nichts gemessen.

    ./instrumente/abnahme.py            der Schnellauf -- teure ausgelassen und GENANNT
    ./instrumente/abnahme.py --voll     alle, auch die teuren
    ./instrumente/abnahme.py --probe    nur die Sprechprobe

**W17 -- die Arbeitsmenge steht neben dem Urteil.** Der Lauf nennt, WIE VIELE Waechter er
gefahren hat, und **ein Lauf, der null faehrt, ist rot und nicht gruen**. Das ist keine
Vorsicht, sondern der dreimal bezahlte Fall: `isabelle build -D .` waehlte nichts und endete
gruen.
"""
import importlib.util
import pathlib
import subprocess
import sys
import tempfile
import time

W = pathlib.Path(__file__).resolve().parent.parent

# The registers live in `pruefe-waechter.py` and are READ, not copied -- a second list over
# the same thing is W7. The hyphen in the file name rules out a plain `import`.
_spec = importlib.util.spec_from_file_location("pw", W / "instrumente" / "pruefe-waechter.py")
_pw = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_pw)

_abschnitt = _pw._abschnitt          # the shared cut notice, through the one register (W7)

SCHWER = _pw.SCHWER
GEGENSTAND = _pw.GEGENSTAND
teilmessungen = _pw.teilmessungen      # the dangerous places, counted the ONE way (W7)
ARGUMENTE = _pw.ARGUMENTE
FRIST = _pw.FRIST
OHNE_URTEIL = _pw.OHNE_URTEIL
korpus_fehlt = _pw.korpus_fehlt

# **The heavy ones get their own deadline, and it is not a comfort setting.**
# `mutiere-pruefer.py` WRITES INTO SOURCES and puts them back byte for byte afterwards. Killed
# by a deadline halfway through, it leaves a mutated tree behind -- and the next measurement
# runs against a mixture, which is `W16` word for word. Measured 2026-08-30: the full run
# takes 10 min 25 s, well past `FRIST`. *A deadline that fires mid-write is worse than none.*
FRIST_VOLL = 1800

# **And the light ones get twice `pruefe-waechter.py`'s deadline, measured on 2026-08-30.**
# That tool uses 300 s to ask whether a guardian HANGS; this one runs the same guardians for
# their VERDICT, and the two questions do not share a budget. `pruefe-lean-beweis.sh` took
# 194 s and 205 s on an idle `fisch` and blew past 300 s in the `--voll` run, immediately
# after the mutation probe had loaded the machine -- reported as `HAENGT` when it was merely
# slow. *A deadline set at 1.5x the measured runtime turns LOAD into a finding*, and a false
# hang is the same class as a false green: it says something about the machine and prints it
# as a statement about the tree.
FRIST_ABNAHME = 2 * FRIST

# **The cheap half of an expensive guardian, so the quick run is not blind to it.**
# `--anker` counts text and builds nothing (`CLAUDE.md`), and it is the half that catches a
# dead anchor -- a mutation whose source line moved away silently shrinks the denominator and
# reads like coverage. The expensive half stays behind `--voll` and is named there.
SCHNELL_TEIL = {"mutiere-pruefer.py": ["--anker"]}

# A Python interpreter that dies in its own prologue has not rendered a verdict. This is the
# ONE signal that separates "did not run" from "found something".
ABSTURZ = "Traceback (most recent call last)"

# **THE HALF-MEASUREMENT -- the fourth mark, and it took two weeks to earn its name.**
#
# `pruefe-emission.sh` died on 2026-08-31 at `F06`'s `N043` in the fourth of ten stages with
# `exit 1`. Stages 9 and 10 never ran; two findings sat behind the cut unseen for two weeks.
# **This run would have shown it as `ROT` with the fourth stage's summary beside it** -- the
# same line, the same colour and the same shape as a guard that had measured everything and
# found something.
#
# > *An empty population is a green judgement over nothing (W17). A TRUNCATED one looks like
# > a judgement over everything.* The three marks knew "nothing measured"; they did not know
# > "half measured".
#
# The return code cannot say it: `1` means *finding*, and a finding in stage 4 is at the same
# time an abort for stages 5 to 10. **So the guard says it in its output**, and this run
# reads it -- `pruefe-emission.sh` through its own `trap`, every Python guard through
# `instrumente/abschnitt.py`.
#
# **It is a separate MARK, not a separate colour.** A truncated run has measured something,
# so it is not an `ABBRUCH`; and it has not measured everything, so its finding count is a
# lower bound. `messung/RUECKLAUFWERTE.md` counts the surface (251 exit sites behind a first
# one) and the danger underneath it (94 that leave a partial measurement looking whole).
SCHNITT = "ABGESCHNITTEN in:"


def besetzung(wurzel):
    """Every guardian in `wurzel` -- from the DIRECTORY, never from a list in here.

    **The `zaehle-*` came in on 2026-08-31, and the boundary moved because it was printed.**
    Until then this run drove `pruefe-*` and `mutiere-*` only, and the 18 counters stood
    outside with the sentence *"they measure, they do not guard -- no return code of theirs
    carries a verdict"*. The sentence was a claim, and it was measured:

    * Over an EMPTY tree not one of the 18 returned a green verdict. Six died of a
      `FileNotFoundError` (return code 1, a traceback), nine printed a refusal and returned
      1 as well. **Every one of them carries a verdict -- none of them had been GIVEN one.**
    * `zaehle-karten.py` had been reaching `master` RED over a broken ratchet, and no
      collective run read it. *A guardian nobody drives is indistinguishable from one that
      does not exist* -- the sentence this file was built on, against a boundary this file
      itself drew.

    What stays out is named in `pruefe-waechter.py:OHNE_URTEIL` and PRINTED with its count,
    exactly as the old boundary was.
    """
    return sorted(
        (set(wurzel.glob("pruefe-*")) | set(wurzel.glob("mutiere-*"))
         | {p for p in wurzel.glob("zaehle-*") if p.name not in OHNE_URTEIL}),
        key=lambda p: p.name,
    )


def fahre_einen(p, voll, arbeitsverzeichnis):
    """One guardian. Returns `(marke, ruecklauf, dauer, bemerkung)`.

    `marke` is one of `gruen` · `ROT` · `ABBRUCH` · `NICHT FAHRBAR` · `ausgelassen`.
    """
    teuer = p.name in SCHWER
    args = [str(pathlib.Path(a).expanduser()) if a.startswith("~") else a
            for a in ARGUMENTE.get(p.name, [])]
    angemeldet = p.name in ARGUMENTE
    nachsatz = ""
    if teuer and not voll:
        if p.name not in SCHNELL_TEIL:
            return "ausgelassen", None, 0.0, SCHWER[p.name]
        args = SCHNELL_TEIL[p.name]
        nachsatz = f"nur `{' '.join(args)}` -- der volle Lauf steht unter `--voll`"
    fehlt = korpus_fehlt(p.name)
    if fehlt:
        ort, was = fehlt
        return "NICHT FAHRBAR", None, 0.0, f"fremder Korpus fehlt: {was} ({ort})"
    frist = FRIST_VOLL if teuer else FRIST_ABNAHME
    t0 = time.monotonic()
    try:
        r = subprocess.run([str(p)] + args, cwd=arbeitsverzeichnis, capture_output=True,
                           text=True, timeout=frist)
    except subprocess.TimeoutExpired:
        # **A hang is an ABORT, not a named hole.** It looks like "still running", and the
        # tree it was asked about got no verdict at all -- requirement (1) of
        # `pruefe-waechter.py`, one level up.
        return "ABBRUCH", None, time.monotonic() - t0, f"HAENGT -- Frist {frist} s"
    except (PermissionError, OSError) as e:
        return "NICHT FAHRBAR", None, time.monotonic() - t0, f"nicht startbar: {e}"
    dauer = time.monotonic() - t0
    if angemeldet and not nachsatz:
        nachsatz = f"braucht ein Argument, bekommt `{' '.join(args)}`"
    if ABSTURZ in (r.stderr or ""):
        zeilen = [z for z in r.stderr.strip().splitlines() if z.strip()]
        grund = zeilen[-1] if zeilen else "Absturz"
        return "ABBRUCH", r.returncode, dauer, "; ".join(
            x for x in (f"ABGESTUERZT, kein Urteil -- {grund}", nachsatz) if x)
    if r.returncode == 0:
        return "gruen", 0, dauer, nachsatz
    # **An abort names its reason on STDERR** -- that is where every `ABBRUCH:` line in this
    # directory is printed. Reading stdout only would show the last row of the table instead
    # of the refusal, and that is word for word the confusion this mark exists against.
    marke = "ROT" if r.returncode == 1 else "ABBRUCH"
    roh = r.stdout or ""
    if marke == "ABBRUCH" and (r.stderr or "").strip():
        roh = r.stderr
    kopf = [z for z in roh.splitlines() if z.strip()]
    schluss = kopf[-1].strip()[:80] if kopf else ""
    # **The cut is read from the OUTPUT, and it overrides the last line as the remark.**
    # Without this the announcement's closing line would replace the finding's summary --
    # the guard would have said where it stopped and this run would have printed a pointer
    # to a document instead.
    #
    # **And only over a FINDING.** An abort's own refusal is the stronger statement -- it
    # says nothing was measured at all, and the cut notice must not push it out of the line.
    schnitt = next((z.strip() for z in reversed(roh.splitlines()) if SCHNITT in z), None)
    if schnitt and marke == "ROT":
        marke = "TEILMESSUNG"
        schluss = schnitt.strip("= ").strip()[:80]
    if marke == "ABBRUCH" and r.returncode != 2:
        nachsatz = "; ".join(x for x in (f"beendet mit {r.returncode} -- kein Urteil",
                                         nachsatz) if x)
    return marke, r.returncode, dauer, "; ".join(x for x in (schluss, nachsatz) if x)


def fahre(wurzel, voll, arbeitsverzeichnis):
    """The whole cast. Returns the list of `(name, marke, ruecklauf, dauer, bemerkung)`."""
    return [(p.name,) + fahre_einen(p, voll, arbeitsverzeichnis)
            for p in besetzung(wurzel)]


def urteil(ergebnisse):
    """`(ruecklaufwert, gemessen, gruen, rot, abbruch, nicht_fahrbar, ausgelassen)`.

    Drei Ruecklaufwerte, dieselben drei, die jeder einzelne Waechter fuehren soll:

        0   gemessen, kein Befund
        1   gemessen, und mindestens einer meldet etwas
        2   ABBRUCH -- ein Waechter hat kein Urteil geliefert, oder es wurde gar nichts
            gemessen

    **Die gezaehlte Arbeitsmenge ist `gemessen`, nicht `gestartet`.** Ein Abbruch faellt aus
    ihr heraus, denn er hat nichts angesehen; bis zum 2026-08-31 zaehlte er mit und hob damit
    genau die Zahl, die gegen das leere Urteil steht.

    **Null gemessene Waechter sind ein ABBRUCH.** Ein positives Urteil ueber nichts sieht aus
    wie ein Ergebnis und ist keines (W17).
    """
    gruen = sum(1 for e in ergebnisse if e[1] == "gruen")
    rot = sum(1 for e in ergebnisse if e[1] == "ROT")
    # **A truncated run counts among those that MEASURED, and among the red ones.** It saw
    # something and it found something -- it merely did not see everything, and that is why
    # it gets its own line and its own count instead of its own colour.
    teil = sum(1 for e in ergebnisse if e[1] == "TEILMESSUNG")
    ab = sum(1 for e in ergebnisse if e[1] == "ABBRUCH")
    nf = sum(1 for e in ergebnisse if e[1] == "NICHT FAHRBAR")
    aus = sum(1 for e in ergebnisse if e[1] == "ausgelassen")
    gemessen = gruen + rot + teil
    code = 2 if (ab or gemessen == 0) else (1 if (rot or teil) else 0)
    return code, gemessen, gruen, rot, ab, nf, aus, teil


def gegenstand(wurzel, ergebnisse):
    """`(gesehen, gesamt, ungesehen_je_waechter)` -- the OBJECT, not the cast.

    **The closing line counted guardians, and a tree is not measured in guardians.** On
    2026-08-31 the quick run reported `45 von 49 Waechtern haben GEMESSEN` while the three it
    had left out carried 47 of the 92 dangerous places between them -- 45 in
    `pruefe-emission.sh` alone. *The number was right and its denominator was the wrong
    thing* (W25), and whoever read it read a verdict on the tree.

    **The unit is the one this workshop already counts.** `pruefe-waechter.teilmessungen()`
    walks every guardian for the places where a run leaves with `1` and output would still
    follow -- the same sieve, the same code, merely split per guardian instead of summed. So
    this is not a second register over the same thing (W7): it is the same register read a
    second way, and a guardian that gains a place gains it in both numbers at once.

    **`gesehen` is an UPPER bound, and it says so where it is printed.** A guardian run with
    only half its arguments (`SCHNELL_TEIL`) counts as seen because it started; the places
    behind the half that did not run were not visited. A `TEILMESSUNG` counts as seen for the
    same reason and for the same lie -- it stopped somewhere in the middle. *Both push the
    number up, never down, which is the direction a bound may err in.*
    """
    je = {p.name: teilmessungen([p])[3] for p in besetzung(wurzel)}
    gesamt = sum(je.values())
    # **Whoever did not MEASURE did not visit his places either.** The three marks are the
    # same three that fall out of the work quantity in `urteil()` -- one boundary, drawn once.
    ungesehen = {n: je.get(n, 0) for n, m, *_ in ergebnisse
                 if m in ("ausgelassen", "NICHT FAHRBAR", "ABBRUCH") and je.get(n, 0)}
    return gesamt - sum(ungesehen.values()), gesamt, ungesehen


def schlusssatz(gemessen, gruen, wieviele, gesehen, g_gesamt, luecke):
    """The closing sentence, as a list of lines -- **two sentences, not one with a suffix.**

    **Green with a named gap is not the same as green, and it is not red either**
    (2026-08-31). A quick run that can never look green again is no help: nobody drives it,
    and then the four expensive guardians are the only measurement there is -- which is
    exactly the road by which they stopped being driven at all. So the word stays `GRUEN` and
    the return code stays `0`. What changes is that the sentence now says HOW MUCH OF THE
    OBJECT this green covers, and that the two cases are visibly different sentences.

    *It is a function and not four `print` calls inside `main` so that the speech test can
    read both directions* -- the number underneath was already provable, the SENTENCE was not.
    """
    anteil = f" -- {round(100 * gesehen / g_gesamt)} %" if g_gesamt else ""
    if luecke:
        return [f"  ABNAHME GRUEN MIT BENANNTER LUECKE: {gemessen} von {wieviele} Waechtern,",
                f"  und hoechstens {gesehen} von {g_gesamt} gefaehrlichen Stellen{anteil}."
                "  **Gruen heisst hier:",
                "  was gefahren wurde, ist sauber** -- nicht, dass der Baum es ist. Der",
                "  Rest steht oben mit Namen und Zahl, und `--voll` faehrt ihn."]
    return [f"  ABNAHME GRUEN: {gruen} von {gruen} messenden Waechtern -- und",
            f"  {gesehen} von {g_gesamt} gefaehrlichen Stellen. **Kein Wort davon ist",
            "  ausgelassen, und keiner ist ungesehen geblieben.**"]


def sprechprobe():
    """**In alle Richtungen, auf ERFUNDENEN Waechtern.**

    Ein Sammellauf, der nur die eigenen Waechter liest, misst, wie gut sie zu ihm passen.
    Gepruefte Behauptung: ein kuenstlich rot gemachter Waechter macht den Sammellauf rot,
    ein gruener nicht, ein abstuerzender faellt als eigener Fall auf -- und **ein leeres
    Verzeichnis ist rot, nicht gruen**.

    **Und seit dem 2026-08-31 in der Richtung, die der Grund fuer diese Datei ist:** ein
    kuenstlich ABBRECHENDER Waechter muss als `ABBRUCH` erscheinen und NICHT als Befund, ein
    kuenstlich roter weiter als Befund. *Zwei Proben, denn eine allein liesse sich mit einer
    Marke bestehen, die alles rot nennt.*
    """
    proben = []
    with tempfile.TemporaryDirectory() as d:
        dp = pathlib.Path(d)
        (dp / "pruefe-gruen.sh").write_text("#!/bin/sh\necho '== 3 von 3 =='\nexit 0\n")
        (dp / "pruefe-rot.sh").write_text("#!/bin/sh\necho '! RATSCHE: 28, erlaubt 27'\nexit 1\n")
        # The abort prints its reason on stderr, exactly as the real ones do -- so this probe
        # also measures that the reason is READ from there and not from the last table row.
        (dp / "pruefe-halt.sh").write_text(
            "#!/bin/sh\necho '== 0 von 0 Zellen =='\n"
            "echo 'ABBRUCH: der Korpus ist leer -- es wurde NICHTS gemessen.' >&2\nexit 2\n")
        (dp / "pruefe-sturz.py").write_text(
            "#!/usr/bin/env python3\nimport sys\nsys.argv[1]\n")
        # **The fourth mark, and BOTH directions.** A guard that stops before its last
        # measurement and says so must not read like one that measured everything; and a
        # guard that measured everything and found something must stay a plain finding.
        # *One direction alone passes with a mark that calls every red a half-measurement.*
        (dp / "pruefe-halb.sh").write_text(
            "#!/bin/sh\necho '== Stufe 4: der Differenztest =='\n"
            "echo '  F06 faellt an N043'\n"
            "echo '== ABGESCHNITTEN in: Stufe 4 -- Ruecklaufwert 1 =='\nexit 1\n")
        for f in dp.iterdir():
            f.chmod(0o755)
        erg = fahre(dp, voll=True, arbeitsverzeichnis=dp)
        rc, gemessen, gruen, rot, ab, nf, _, teil = urteil(erg)
        marken = {n: m for n, m, *_ in erg}
        bem = {n: b for n, _, _, _, b in erg}
        proben.append(("fuenf Waechter gefunden und gefahren", len(erg) == 5))
        proben.append(("der gruene ist gruen", marken.get("pruefe-gruen.sh") == "gruen"))
        proben.append(("der rote ist ROT", marken.get("pruefe-rot.sh") == "ROT"))
        # **The direction this whole mark exists for.** An abort must not be booked as a
        # finding -- and the printed reason must be the REFUSAL, not the last row above it.
        proben.append(("der abbrechende ist ABBRUCH und kein Befund",
                       marken.get("pruefe-halt.sh") == "ABBRUCH" and rot == 1))
        proben.append(("und er nennt seine Absage, nicht die letzte Tabellenzeile",
                       "es wurde NICHTS gemessen" in bem.get("pruefe-halt.sh", "")))
        proben.append(("der abstuerzende faellt als ABBRUCH auf",
                       marken.get("pruefe-sturz.py") == "ABBRUCH"))
        proben.append(("der abgeschnittene ist TEILMESSUNG und kein blosser Befund",
                       marken.get("pruefe-halb.sh") == "TEILMESSUNG" and rot == 1))
        proben.append(("und er nennt die STELLE, nicht die letzte Zeile davor",
                       "Stufe 4" in bem.get("pruefe-halb.sh", "")))
        proben.append(("der VOLLE Befund bleibt ein Befund -- die Marke faellt nicht ueberall",
                       marken.get("pruefe-rot.sh") == "ROT"))
        proben.append(("drei von fuenf haben ueberhaupt GEMESSEN",
                       gemessen == 3 and gruen == 1 and ab == 2 and nf == 0))
        # **Both directions of the return code**, because one alone passes with a mark that
        # calls everything red: an abort ends with 2, a mere finding with 1.
        proben.append(("ein Abbruch macht den Lauf rot -- mit 2, nicht mit 1", rc == 2))
        nur_rot = [e for e in erg if e[0] in ("pruefe-gruen.sh", "pruefe-rot.sh")]
        rc1, _, _, rot1, ab1, *_ = urteil(nur_rot)
        proben.append(("ein roter ALLEIN macht 1 -- er wird nicht zum Abbruch",
                       rc1 == 1 and rot1 == 1 and ab1 == 0))
        leer = dp / "leer"
        leer.mkdir()
        rc0, gemessen0, *_ = urteil(fahre(leer, voll=True, arbeitsverzeichnis=leer))
        proben.append(("null gemessen ist ABBRUCH, nicht gruen", rc0 == 2 and gemessen0 == 0))
    # **AND THE OBJECT COUNT ON ITS OWN CARRIER -- three directions** (2026-08-31).
    #
    # Its own directory, because the probes above assert `len(erg) == 5` and a sixth invented
    # guardian would break them. *A probe that changes the run it sits in measures that run
    # and not its subject* -- the reentrancy fault this file paid for the same evening.
    #
    # `pruefe-tief.sh` carries two dangerous places (three `exit 1` with output on both
    # sides, the first one not counted); `pruefe-flach.sh` carries none. **The third
    # direction is the one that keeps the number honest:** leaving out a guardian with an
    # EMPTY object must not open a gap, or the line measures the omission instead of the
    # object -- and then every quick run reads as blind, which is no help either.
    with tempfile.TemporaryDirectory() as d:
        gp = pathlib.Path(d)
        (gp / "pruefe-tief.sh").write_text(
            "#!/bin/sh\necho 'Stufe 1'\nexit 1\necho 'Stufe 2'\nexit 1\n"
            "echo 'Stufe 3'\nexit 1\necho 'Stufe 4'\n")
        (gp / "pruefe-flach.sh").write_text("#!/bin/sh\necho 'alles gesehen'\nexit 0\n")
        for f in gp.iterdir():
            f.chmod(0o755)
        voll_erg = [("pruefe-tief.sh", "ROT", 1, 0.0, ""),
                    ("pruefe-flach.sh", "gruen", 0, 0.0, "")]
        g1, ges1, off1 = gegenstand(gp, voll_erg)
        proben.append(("der GEGENSTAND wird gezaehlt, nicht die Besetzung: 2 Stellen",
                       ges1 == 2 and g1 == 2 and not off1))
        aus_erg = [("pruefe-tief.sh", "ausgelassen", None, 0.0, ""),
                   ("pruefe-flach.sh", "gruen", 0, 0.0, "")]
        g2, ges2, off2 = gegenstand(gp, aus_erg)
        proben.append(("ein ausgelassener Waechter NIMMT SEINEN GEGENSTAND MIT: 0 von 2",
                       ges2 == 2 and g2 == 0 and off2 == {"pruefe-tief.sh": 2}))
        leer_erg = [("pruefe-tief.sh", "gruen", 0, 0.0, ""),
                    ("pruefe-flach.sh", "ausgelassen", None, 0.0, "")]
        g3, ges3, off3 = gegenstand(gp, leer_erg)
        proben.append(("und eine Auslassung OHNE Gegenstand oeffnet keine Luecke: 2 von 2",
                       ges3 == 2 and g3 == 2 and not off3))
    # **AND THE SENTENCE ITSELF, in both directions.** The number above was provable, the
    # closing line was not -- and the closing line is what a reader actually reads. Two
    # requirements, and the second is the one that is easy to lose: a gap must be visible,
    # AND a run without a gap must not carry the gap wording. *A sentence that always warns
    # says nothing; one that never warns says less.*
    mit = "\n".join(schlusssatz(45, 44, 49, 45, 92, luecke=True))
    ohne = "\n".join(schlusssatz(49, 49, 49, 92, 92, luecke=False))
    proben.append(("die Luecke steht IM Satz, mit beiden Zahlen",
                   "MIT BENANNTER LUECKE" in mit and "45 von 49" in mit
                   and "45 von 92" in mit and "49 %" in mit))
    proben.append(("und ohne Luecke traegt der Satz KEINE -- 92 von 92",
                   "LUECKE" not in ohne and "92 von 92" in ohne))
    proben.append(("beide bleiben GRUEN -- die Luecke ist kein Befund",
                   mit.lstrip().startswith("ABNAHME GRUEN")
                   and ohne.lstrip().startswith("ABNAHME GRUEN") and mit != ohne))
    return proben


def main():
    voll = "--voll" in sys.argv
    proben = sprechprobe()
    print("== Sprechprobe -- auf erfundenen Waechtern, in alle Richtungen ==")
    for was, ok in proben:
        print(f"  {'ok         ' if ok else 'GESCHEITERT'}  {was}")
    if not all(ok for _, ok in proben):
        print("\n! Der Sammellauf misst nicht, was er behauptet. ABBRUCH.")
        return 2
    if "--probe" in sys.argv:
        return 0

    inst = W / "instrumente"
    alle = besetzung(inst)
    zaehler = sorted(p for p in inst.glob("zaehle-*") if p.name not in OHNE_URTEIL)
    print()
    print(f"== Abnahme ueber {len(alle)} Waechter aus {inst.name}/ "
          f"{'(VOLL)' if voll else '(Schnellauf)'} ==")
    print()

    erg = fahre(inst, voll, W)
    for name, marke, rc, dauer, bem in erg:
        rcs = "" if rc is None else f"[{rc}]"
        print(f"  {marke:<14} {name:<26} {dauer:6.1f} s {rcs:<4} {bem}")

    code, gemessen, gruen, rot, ab, nf, aus, teil = urteil(erg)

    print()
    print(f"== Arbeitsmenge: {gemessen} von {len(alle)} Waechtern haben GEMESSEN -- "
          f"{gruen} gruen, {rot} ROT, {teil} TEILMESSUNG ==")
    print(f"   {ab} ABBRUCH, {nf} nicht fahrbar, {aus} ausgelassen -- **die drei haben")
    print("   NICHTS gemessen und stehen darum nicht in der Zahl davor.**")

    # **AND THE SECOND NUMBER, over the OBJECT** (2026-08-31). The line above counts
    # guardians; a tree is not measured in guardians. See `gegenstand()` for why the unit is
    # the dangerous places and why the count is an upper bound.
    gesehen, g_gesamt, ungesehen = gegenstand(inst, erg)
    anteil = f" -- {round(100 * gesehen / g_gesamt)} %" if g_gesamt else ""
    print(f"== Und ihr GEGENSTAND: hoechstens {gesehen} von {g_gesamt} gefaehrlichen "
          f"Stellen besucht{anteil} ==")
    # **And the ones whose object is NOT in this unit get named anyway.** `zaehle-b3.py`
    # carries zero dangerous places and 105 files of a foreign tree: it costs nothing in the
    # fraction and everything in the thing measured. *Whoever prints only the fraction loses
    # exactly the guardian whose absence has no place to show up in.*
    benannt = {n: (ungesehen.get(n, 0), GEGENSTAND[n]) for n, m, *_ in erg
               if m in ("ausgelassen", "NICHT FAHRBAR", "ABBRUCH") and n in GEGENSTAND}
    for n, k in ungesehen.items():
        benannt.setdefault(n, (k, ""))
    if benannt:
        print(f"   {sum(ungesehen.values())} davon stehen in Waechtern, die dieser Lauf "
              f"nicht gefahren hat -- und was mit ihnen ungemessen bleibt:")
        for name, (n, was) in sorted(benannt.items(), key=lambda r: (-r[1][0], r[0])):
            print(f"     {name:<26} {n:>3} Stellen   {was}")
    else:
        print("   Kein ungefahrener Waechter traegt eine -- der Lauf hat den ganzen")
        print("   gezaehlten Gegenstand angesehen.")
    print(f"   **`{gemessen} von {len(alle)} Waechtern` und `{gesehen} von {g_gesamt} "
          f"Stellen` sind ZWEI Zahlen.**")
    print("   Die erste stand hier seit jeher, die zweite nicht -- und die zweite ist die")
    print("   ueber den GEGENSTAND (W25: eine Zahl belegt ihren Nenner, nicht ihre")
    print("   Beschriftung). *Hoechstens*, weil ein halb gefahrener Waechter und eine")
    print("   TEILMESSUNG hier als gesehen zaehlen -- die Schranke irrt nach OBEN.")

    teilweise = [n for n, m, _, _, b in erg if n in SCHNELL_TEIL and "--voll" in b]
    if aus or teilweise:
        print()
        print(f"== {aus + len(teilweise)} teure AUSGELASSEN oder halbiert -- "
              f"und sie stehen hier, statt zu fehlen ==")
        for name, marke, _, _, bem in erg:
            if marke == "ausgelassen" or name in teilweise:
                print(f"   {name:<26} {bem}")
        print("   `--voll` faehrt sie mit. **Ein Sammellauf, der die teuren stillschweigend")
        print("   auslaesst, ist genau der Waechter, gegen den dieser Lauf gebaut ist.**")

    braucht_arg = [n for n, _, _, _, b in erg if b.startswith("braucht ein Argument")]
    if braucht_arg:
        print()
        print(f"== {len(braucht_arg)} Waechter sind NICHT selbststaendig fahrbar ==")
        print("   " + ", ".join(braucht_arg))
        print("   Ihr Argument steht in `pruefe-waechter.py:ARGUMENTE` und wird von hier")
        print("   gestellt. **Ohne es stuerzen sie ab und der Absturz sieht aus wie ein")
        print("   Befund** -- ein Ruecklaufwert 1 aus einem `IndexError` ist kein Urteil.")

    print()
    print(f"== Die {len(zaehler)} `zaehle-*` sind seit dem 2026-08-31 DRIN, "
          f"{len(OHNE_URTEIL)} stehen mit Grund draussen ==")
    for name, grund in sorted(OHNE_URTEIL.items()):
        print(f"   {name:<28} {grund}")
    print("   Bis dahin stand hier *sie messen, sie bewachen nicht* -- mit ihrer Zahl,")
    print("   damit jemand die Grenze verschieben KANN. **Die Messung hat sie verschoben:**")
    print("   ueber einem leeren Baum gab KEINER der 18 ein gruenes Urteil, sechs starben an")
    print("   einem `FileNotFoundError` und neun druckten eine Absage mit Ruecklaufwert 1.")
    print("   *Sie tragen alle ein Urteil -- sie hatten nur keins bekommen.* Und einer,")
    print("   `zaehle-karten.py`, kam ueber einer gebrochenen Ratsche ROT bei `master` an,")
    print("   ohne dass ein Sammellauf ihn las.")

    print()
    print("== Und was das NICHT heisst ==")
    print("   Gruen heisst: jeder gefahrene Waechter endete mit 0. Was KEIN Waechter")
    print("   ansieht, faellt auch hier nicht auf -- die Abnahme verpflichtet, sie")
    print("   spricht nicht frei (W10). Und `nicht fahrbar` ist eine LUECKE mit einem")
    print("   Namen, kein gruener Haken.")
    # **From here on nothing more is measured** -- what follows is the verdict chain, and
    # every one of its ends is a complete one. It sits BEFORE that chain and not before the
    # last `return`: a red acceptance that has seen everything is not a truncated run.
    _abschnitt.fertig()
    if gemessen == 0:
        print("\n! NULL Waechter haben gemessen. Ein positives Urteil ueber nichts ist "
              "keines (W17).")
    # **The abort comes FIRST and it has its own word.** An acceptance in which an abort
    # passes as a finding has lost a guardian without saying so.
    if ab:
        print(f"\n! ABNAHME ABGEBROCHEN: {ab} Waechter haben KEIN Urteil geliefert.")
        for name, marke, rc, _, bem in erg:
            if marke == "ABBRUCH":
                print(f"   {name:<26} [{rc if rc is not None else '-'}]  {bem}")
        print("   **Das ist kein Befund.** Diese Waechter haben nichts angesehen -- was sie")
        print("   gefunden haetten, weiss niemand, und die Zahl der Befunde daneben ist")
        print("   damit eine untere Schranke und kein Stand. *Erst die Messapparatur, dann")
        print("   der Baum.*")
    # **The half-measurement gets its own block, between the abort and the finding.**
    # It measured something, so it is not an abort; it did not measure everything, so the
    # findings beside it are a LOWER BOUND. *A run that measured half must not look like one
    # that measured all of it.*
    if teil:
        print(f"\n! {teil} Waechter haben nur die HAELFTE gemessen -- sie sind VOR ihrer")
        print("  letzten Messung ausgestiegen und sagen, WO:")
        for name, marke, rc, _, bem in erg:
            if marke == "TEILMESSUNG":
                print(f"   {name:<26} [{rc}]  {bem}")
        print("   **Ihr Ruecklaufwert sagt `Befund`, und er ist zugleich ein Abbruch fuer")
        print("   alles dahinter.** Was hinter dem Schnitt stand, wurde weder bejaht noch")
        print("   verneint -- die Zahl der Befunde ist damit eine untere Schranke. Am")
        print("   2026-08-31 waren es zwei Befunde und zwei Wochen (`pruefe-emission.sh`,")
        print("   Stufe 4 von 10). *Erst zu Ende messen, dann den Baum lesen.*")
    if rot:
        wort = "und ausserdem" if (ab or teil) else "! ABNAHME ROT:"
        print(f"\n{wort} {rot} von {gemessen} messenden Waechtern melden einen Befund.")
        for name, marke, rc, _, bem in erg:
            if marke == "ROT":
                print(f"   {name:<26} [{rc}]  {bem}")
    if not ab and not rot and not teil:
        # The sentence lives in `schlusssatz()`, where the speech test can read BOTH of its
        # directions -- see there for why green with a named gap stays green.
        print()
        for zeile in schlusssatz(gemessen, gruen, len(alle), gesehen, g_gesamt,
                                 bool(benannt or nf)):
            print(zeile)
    return code


# **AND THE COLLECTIVE RUN ANNOUNCES ITS OWN CUT** -- since 2026-08-31.
# It prints the `TEILMESSUNG` count for all 49 and was not itself under the form. A crash
# after twenty guards would have left twenty rows on screen and no line saying that
# twenty-nine were never asked -- *a half acceptance that reads like a whole one*, which is
# the exact shape this mark exists for. **The tool that names a class does not get to stand
# outside it.**
if __name__ == "__main__":
    sys.exit(_abschnitt.fahre(main))
