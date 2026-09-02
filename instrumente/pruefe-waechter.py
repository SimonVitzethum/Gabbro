#!/usr/bin/env python3
"""**Der Waechter ueber den Waechtern -- weil vier von ihnen aufgehoert hatten zu messen.**

Am 2026-08-20 wurden an einem einzigen Tag vier Instrumente dabei erwischt, dass sie nicht
mehr messen:

* `pruefe-emission.sh` **hing** an seiner eigenen Sprechprobe. `baum41`s Gift lenkt den
  Abstieg von `erstes_kind` auf `elter`, der Lauf klettert zur Wurzel und dreht dort -- ohne
  Frist. Auf `ki-pc-fisch-101` standen **einundzwanzig** Laeufe nebeneinander, der aelteste
  seit dreieinhalb Stunden.
* `zaehle-pflichten.py` **verweigerte** die Ableitung (*„15 Bloecke statt 10"*), seit «F0» und
  «K2» in derselben Datei stehen -- und der Modus, der noch antwortete, lief VOR der Pruefung.
* `gift/214` **prueft etwas anderes** als es behauptete; der Mutationslauf hat es gesagt.
* die B22-Sonde in `pruefe-notation.py` **mass einen fremden Fehler** (`gates g` mit
  undeklariertem `g`) und meldete die Luecke als offen.

> **Ein Haenger sieht aus wie „laeuft noch", nicht wie ein Befund.** Und ein Waechter, der
> still abbricht, sieht aus wie einer, der nichts gefunden hat. *Beide Male wird nichts rot.*

Drei Forderungen, und sie stehen hier, weil keine von ihnen sich selbst durchsetzt:

1. **FRIST** -- wer etwas ausfuehrt, tut es mit einer Frist. Sonst ist ein Haenger ein Zustand
   und kein Befund.
2. **SPRECHPROBE** -- in beide Richtungen: was fallen soll, faellt; was nicht, faellt nicht.
   *Ein Waechter, der nicht rot werden kann, misst nichts* (R14).
3. **ROT BEI ABBRUCH** -- ein Abbruch verlaesst mit einem Ruecklaufwert ungleich null. `set -e`
   mit `timeout` ist genau die Falle, in die `pruefe-emission.sh` am selben Tag noch lief:
   die Frist beendete den Waechter STILL, mit Ruecklaufwert 0 und einer Ausgabe, die mit `ok`
   endete.
4. **ARBEITSMENGE** -- neben dem Urteil steht, WIE VIEL angesehen wurde. *Ohne sie ist ein
   gruener Lauf von einem leeren nicht zu unterscheiden.*
5. **GEBIETSSCHEMA** -- whoever calls a foreign tool and reads its MESSAGE pins
   `LC_ALL=C`. Measured 2026-08-25: under `de_DE.UTF-8` the linker says
   `Mehrfachdefinition von`, not `multiple definition`. `pruefe-emission.sh` searched for
   the English words, did not find them and reported *„der Binder faellt aus anderem
   Grund"* -- **an error that did not exist.** The same class as `W16`: a tool that measures
   its own locale and looks plausible doing it.

**Zu (4) gehoert eine eigene Klasse, und sie hat am 2026-08-20 dreimal zugeschlagen:**

| | |
|---|---|
| `isabelle build -D .` | waehlte NICHTS und endete gruen |
| `zaehle-b3.py` | druckte `! ABBRUCH` und endete mit 0 |
| das README-Muster fuer die Waechterzahl | traf nichts mehr und meldete „sauber" |

**Drei Faelle, eine Form: ERFOLG OHNE ARBEIT.** Nicht ein falsches Urteil, sondern ein
*positives Urteil ueber nichts* -- und das ist gefaehrlicher, weil es wie ein Ergebnis
aussieht. Die Vorkehrung ist die Zahl neben dem Urteil (W11: jede Quote nennt ihr N).

    ./instrumente/pruefe-waechter.py [--lauf]

**Und was das NICHT heisst:** die statische Haelfte liest QUELLTEXT. Dass ein `timeout` im
Text steht, heisst nicht, dass es an der richtigen Stelle steht. `--lauf` fuehrt die leichten
Waechter wirklich aus und verlangt einen bestimmten Ruecklaufwert innerhalb der Frist -- die
schweren stehen mit Grund daneben. *Eine Flaeche, die kein Werkzeug erreicht, faellt in keiner
Statistik auf.*

**Nachgetragen 2026-08-20, und der Befund gehoert dem Waechter selbst:** derselbe `--lauf` war
hier gruen und auf `ki-pc-fisch-101` rot -- bei identischen Quellen. Nicht der Code, sondern
der **Gegenstand** fehlte: `zaehle-b3.py` und `zaehle-narrow.py` messen FREMDE Baeume
(Caprock-Messbasis, SEL4Lake), und die liegen nur auf dem Arbeitsrechner. *Ein Waechter,
dessen Urteil davon abhaengt, auf welchem Rechner er laeuft, ohne es zu sagen, misst den
Rechner.* Die zwei stehen jetzt in `FREMDER_KORPUS`, und ein fehlender Baum wird als **nicht
gemessen** gezaehlt statt als Befund gedruckt -- mit seiner Zahl in der Schlusszeile.

*Dieselbe Falle noch einmal, eine Ebene tiefer:* `../caprock-messbasis` ist ein RELATIVER
Pfad. In einem `git worktree` zeigt er neben den Arbeitsbaum -- und `zaehle-b3.py` lief bis
heute darueber bis in eine `ZeroDivisionError`.
"""
import importlib.util
import pathlib
import re
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import abschnitt as _abschnitt   # noqa: E402  -- the shared cut notice

W = pathlib.Path(__file__).resolve().parent.parent
FRIST = 300

# **Waechter, die NICHT im `--lauf` stehen -- und der Grund ist seit dem 2026-08-20 GEMESSEN.**
#
# Bis dahin standen hier fuenf Eintraege mit geschaetzten Kosten, und **vier von fuenf waren
# falsch** -- am schlimmsten `pruefe-emission.sh` mit *„46 Einheiten … ~25 min"*. Gemessen auf
# `ki-pc-fisch-101`: **13,7 Sekunden.** Die 25 Minuten stammen vom Vormittag desselben Tages,
# als der Waechter an `baum41` HING; die Frist hat den Haenger beseitigt, und die Zahl, die ihn
# beschrieb, blieb stehen -- **als Begruendung dafuer, ihn nicht zu messen.**
#
# > **Eine Ausnahme, deren Grund niemand nachrechnet, ist dieselbe Klasse wie eine Zahl, die
# > niemand nachrechnet** -- nur teurer, weil sie eine ganze Messung abschaltet statt sie zu
# > verfaelschen. *Erfolg ohne Arbeit, eine Ebene ueber dem Urteil: die Arbeit wird gar nicht
# > erst angeordnet.*
#
# Was blieb, steht jetzt mit dem RICHTIGEN Grund da, und der ist in keinem der vier die Zeit:
# es ist der ORT (Speicher, Rechenlast gehoert auf den Server -- `CLAUDE.md`) oder die
# WIRKUNG (es schreibt in Quellen). `pruefe-notation.py` ist ganz herausgefallen: 0,56 s, und
# es ruft kein `cargo` -- **es stand vier Wochen auf einer Liste, auf die es nie gehoerte.**
SCHWER = {
    "mutiere-pruefer.py":
        "es SCHREIBT in Quellen -- zwei Laeufe zerstoeren einander (2 min 20 s, 2026-08-19)",
    "pruefe-beweise.sh":
        "1,45 GB Spitze -- ueber der lokalen 1-GB-Grenze; 8,1 s auf `fisch` (2026-08-20)",
    "pruefe-emission.sh":
        "`cargo run` je Einheit -- gehoert auf den Server; 13,7 s dort (2026-08-20)",
    "pruefe-luecken.py":
        "baut dreizehnmal neu -- gehoert auf den Server; 10,7 s / 27,8 s CPU dort (2026-08-20)",
    # **And this one is in here for a reason none of the others has: it would run THIS RUN.**
    # It drives every instrument under a line trace, and the acceptance is one of them --
    # which drives it again. Measured 2026-09-01: three nested levels were standing after
    # eleven minutes before the register said no. *A guardian whose object contains its own
    # caller has no fixed point, and `SCHWER` is where that is written down.*
    "zaehle-probenzweige.py":
        "faehrt 43 Instrumente unter `sys.settrace` -- darunter diese Abnahme, die ihn "
        "wieder faehrt; 2 min 11 s ohne sie (2026-09-01)",
    # **Not expensive -- 10,2 s wall over 5889 cases on `fisch` -- but it needs THREE things
    # the machine may not have**: a debug binary, a RELEASE binary, and `cc`. Missing any of
    # them it leaves with 2 and has measured nothing, and the quick run above would book that
    # `RUECKLAUFWERT-2` as a finding about the tree. *The same case as `zaehle-c-formen.py`
    # and `pruefe-umwandlungen.py`: "ran" and "measured" come apart at a precondition.*
    #
    # > `fuzze-grenzen.py` carries the same precondition (two profiles) and is NOT booked
    # > here. That is left as it stands rather than corrected in passing -- it is another
    # > lane's line, and a booking added from the side is a booking nobody measured.
    "fuzze-erzeuger.py":
        "braucht BEIDE Bauprofile und `cc`, sonst Ruecklaufwert 2 und NICHTS gemessen; "
        "5889 Faelle, 10,2 s Wanduhr / 85 s CPU auf `fisch` (2026-09-02)",
}
# **WHAT AN OMITTED GUARDIAN TAKES WITH IT -- in its OWN unit** (2026-08-31).
#
# `SCHWER` above says why a guardian is expensive. It does not say what stays UNMEASURED when
# the quick run leaves it out, and for two weeks the collective run's closing line therefore
# reported 45 guardians out of 49 over a tree of which it had seen less than half. *A count of
# guardians is not a count of the object* -- `pruefe-emission.sh` is one line in that
# denominator and 101 translation units behind it.
#
# > **W25: a number vouches for its DENOMINATOR, not for its label.** Here the denominator was
# > the wrong one, and it read like a verdict on the tree.
#
# Measured 2026-08-31 from the guardians' own sources and their last logged full run, with no
# build: `beweise/ROOT` (15 theories), `mutiere-pruefer.MUTATIONEN` (372), `pruefe-luecken
# .LUECKEN` (15 twists, 13 of them with a build of their own), and stage 9 of the last green
# `pruefe-emission.sh` run (101 out of 101, behind ten stages and 25 through-cuts).
#
# **The sum of these is NOT printed as a fraction.** 101 units, 372 mutations, 15 twists and
# 15 theories add up to 503 items only if one ignores that they are four different things,
# and there is no counted total for the other 45 guardians to divide it by. The number that
# HAS a denominator is the other one -- the dangerous places, counted by `teilmessungen()`
# over every guardian alike. This register exists to be NAMED beside it, never summed into it.
def mutationskatalog(wurzel=None):
    """**Wie viele Mutationen traegt der Katalog HEUTE?** Gelesen, nicht erinnert (W7).

    Bis zum 2026-09-02 stand hier `372`, gemessen am 2026-08-31 und danach nie wieder. Der
    Katalog stand an dem Tag bei **383** -- elf mehr, und der Eintrag daneben las sich
    unveraendert wie eine Messung. *Eine Zahl, die neben einem wachsenden Katalog steht,
    liest sich nicht als veraltet, sondern als Stand* -- genau der Satz, mit dem
    `mutiere-pruefer.py:FLAECHEN` seine eigene `code`-Zeile zum Leser gemacht hat.

    `-1`, wenn der Katalog nicht lesbar ist. **Eine Null waere hier falsch**: sie ist ein
    gueltiger Stand ("kein Gegenstand mehr"), und die Unterscheidung zwischen *leer* und
    *ungemessen* ist die, um die es in diesem ganzen Register geht.
    """
    try:
        spec = importlib.util.spec_from_file_location(
            "mp_katalog", (wurzel or W) / "instrumente" / "mutiere-pruefer.py")
        mp = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mp)
        return len(mp.MUTATIONEN)
    except Exception:
        return -1


def sprechprobe_katalog():
    """`[(what, ok)]` -- **liest der Leser, oder erinnert er sich?**

    Die zweite Richtung ist die, die eine feste Zahl nicht bestehen kann: ueber einem
    UNTERGESCHOBENEN Katalog mit drei Eintraegen muss `3` herauskommen. Ein Waechter, der
    seine Zahl behaelt, wenn der Gegenstand sich bewegt, misst sich selbst.
    """
    echt = mutationskatalog()
    with tempfile.TemporaryDirectory() as d:
        ort = pathlib.Path(d)
        (ort / "instrumente").mkdir()
        (ort / "instrumente" / "mutiere-pruefer.py").write_text(
            "class M:\n    pass\nMUTATIONEN = [M(), M(), M()]\n", encoding="utf-8")
        untergeschoben = mutationskatalog(ort)
    return [
        (f"der Katalog wird GELESEN: {echt} Mutationen", echt > 0),
        ("ein untergeschobener Katalog mit 3 Eintraegen ergibt 3", untergeschoben == 3),
    ]


GEGENSTAND = {
    "mutiere-pruefer.py":
        f"{mutationskatalog()} Mutationen, je ein `cargo build` und ein `cargo test`",
    "pruefe-beweise.sh":
        "15 Isabelle-Theorien (`beweise/ROOT`)",
    "pruefe-emission.sh":
        "101 von 101 Uebersetzungseinheiten in Stufe 9, hinter zehn Stufen und 25 Durchstichen",
    "pruefe-luecken.py":
        "15 Verdrehungen, 13 davon mit eigenem Bau, dazu der Nullauf",
    # **Not expensive -- ABSENT, and it belongs here for exactly that reason.** Its object is
    # the Caprock measuring base, and it carries ZERO dangerous places: in the unit the
    # fraction is counted in, losing it costs nothing, and it would drop out of the report
    # without a word. *A guardian whose object is a foreign tree is the case where the two
    # units come apart* -- so it is named here and stays out of the fraction.
    "zaehle-b3.py":
        "105 Dateien / 2536 Ruempfe der Caprock-Messbasis -- ein FREMDER Baum",
    # **Not expensive either -- but it is the only guardian whose object is the EMITTED C,
    # and it needs a built binary to have one at all.** Without `target/debug/gabbro` it
    # leaves with 2 and has measured nothing; then this line says what was lost. *A tool
    # whose object only exists after a build is the case where "ran" and "measured" come
    # apart.*
    "zaehle-c-formen.py":
        "102 emittierende Uebersetzungseinheiten / 8001 Zeilen erzeugtes C, "
        "gegen 101 Formen aus `BEWEIS.md` Item 2 §1",
    "zaehle-probenzweige.py":
        "43 von 52 Instrumenten unter einer geteilten Zeilenspur -- die Zweige, "
        "die nur die Sprechprobe je erreicht hat",
    # **Nicht teuer -- 3,6 s kalt auf `fisch`, 5,5 s lokal -- aber sein Gegenstand haengt an
    # einem Bauteil, das der Rechner nicht haben muss.** `cargo-clippy` stand am 2026-09-01
    # auf `ki-pc-fisch-101` NICHT zur Verfuegung, und der erste Lauf dieses Auftrags meldete
    # darueber `Ruecklaufwert 0` bei null Warnungen: ein fehlendes Werkzeug liest sich genau
    # wie ein sauberer Baum. *Derselbe Fall wie `zaehle-c-formen.py`* -- „gelaufen" und
    # „gemessen" gehen auseinander, und darum steht er hier mit seiner Vorbedingung.
    "pruefe-umwandlungen.py":
        "33 abschneidende Umwandlungen in 50 Quellen von `crates/*/src/` -- "
        "braucht `cargo-clippy`, sonst Ruecklaufwert 2 und NICHTS gemessen",
}
# **Waechter, deren Gegenstand ein FREMDER BAUM ist** -- einer, der nicht in diesem
# Verzeichnis liegt und den `git` nicht mitbringt. Je Eintrag: der Pfad und was dort steht.
#
# **Fehlt er, hat das Werkzeug NICHTS gemessen** -- und dann ist sein Ruecklaufwert ein
# Fehlaufruf und kein Befund. Bis zum 2026-08-20 wurde daraus ein rotes `--lauf`, und zwar
# genau auf `ki-pc-fisch-101`: dorthin gehoert die Rechenlast, und dort liegen weder die
# Caprock-Messbasis noch SEL4Lake. *Ein Waechter, dessen Urteil davon abhaengt, auf welchem
# Rechner er laeuft, ohne es zu sagen, misst den Rechner.*
#
# **Und `../caprock-messbasis` ist zusaetzlich relativ**: bis zum 2026-08-31 zeigte der Pfad
# aus einem `git worktree` heraus neben den Arbeitsbaum statt neben die Hauptauscheckung --
# geheilt durch `korpus_ort()` unten, das ihn und sein ARGUMENT an EINER Stelle aufloest.
#
# *Das ist kein Freibrief.* Was hier steht, wird NICHT gruen gebucht, sondern als **nicht
# gemessen** gezaehlt und in der Schlusszeile mit seiner Zahl genannt (W17).
FREMDER_KORPUS = {
    "zaehle-b3.py": ("../caprock-messbasis", "die Caprock-Messbasis (Zweig arch/x86_64)"),
    "zaehle-narrow.py": ("~/Dokumente/SEL4Lake/SEL4Lake", "der zweite Korpus, SEL4Lake"),
}
# Waechter, die ein Argument brauchen.
ARGUMENTE = {
    "pruefe-wortschatz.py": ["dokumente/SYNTAX.md"],
    # **Ohne Argument endet es mit 2 und hat nichts gemessen** -- und ein Ruecklaufwert 2 in
    # einer Kette sieht aus wie ein Befund. Gefunden 2026-08-20 beim ersten `--lauf`.
    "zaehle-b3.py": ["../caprock-messbasis"],
    # **`zaehle-narrow.py` nahm bis zum 2026-08-20 den Standardbaum stillschweigend an** und
    # endete mit 2, wo er fehlt. Jetzt steht der Pfad hier, sichtbar neben dem von `b3`.
    "zaehle-narrow.py": ["~/Dokumente/SEL4Lake/SEL4Lake"],
    # **`--uebersetzer` belongs in the collective run because the mark was taken with it.**
    # Without the switch three entries of the never list (implicit conversion, `const`
    # discarding, VLA) stay unmeasured -- and a guardian that cannot recompute its own mark
    # guards half of it. It costs 5 s over 102 units.
    "zaehle-c-formen.py": ["--uebersetzer"],
}


def hauptauscheckung(w=None):
    """The main checkout `w` belongs to -- `w` itself when it is not a worktree.

    **A guardian that is `NICHT FAHRBAR` here and runnable three directories up measures the
    checkout, not the tree** (2026-08-31). `../caprock-messbasis` sits beside the main
    checkout; from inside `.claude/worktrees/<name>/` the same two dots point somewhere else
    entirely, and `zaehle-b3.py` was booked as *"the measuring base is missing"* while it lay
    there and ran green against it (`rc=0`, 105 files, 2536 bodies). The acceptance said
    `48 von 49` and meant *48 of 49 in this worktree*.

    > *Same class as the guardian whose verdict hung on the MACHINE -- one level smaller.*

    **Read from the `.git` marker, not from `git`.** A worktree's `.git` is a FILE holding
    `gitdir: <main>/.git/worktrees/<name>`; a plain checkout has a DIRECTORY there. So this
    needs no subprocess, no return code and no `git` on the PATH -- and it cannot fall foul
    of the bolt three requirements below (*whoever reads `git` reads the return code*), which
    is the reason the healing waited a day. Anything unexpected returns `w`: the old
    behaviour, which errs towards `NICHT FAHRBAR` and never towards a false green.
    """
    w = W if w is None else w
    marke = w / ".git"
    try:
        if not marke.is_file():
            return w
        text = marke.read_text(encoding="utf-8", errors="replace").strip()
    except OSError:
        return w
    if not text.startswith("gitdir:"):
        return w
    ort = pathlib.Path(text.split(":", 1)[1].strip())
    if not ort.is_absolute():
        ort = (w / ort).resolve()
    if ort.parent.name == "worktrees" and ort.parent.parent.name == ".git":
        return ort.parent.parent.parent
    return w


def korpus_ort(pfad, w=None):
    """One declared corpus path: `~` expanded, relative resolved against the MAIN checkout.

    **The one place where such a path is turned into a location** (W7). It is read from two
    sides -- `korpus_fehlt()` below asks whether the corpus is there, and `abnahme.py` hands
    the very same path to the guardian as its argument. *Two resolutions of one path is how a
    run reports a corpus as present and then measures a different directory.*
    """
    ort = pathlib.Path(pfad).expanduser()
    return ort if ort.is_absolute() else (hauptauscheckung(w) / pfad).resolve()


def korpus_fehlt(name):
    """Der fremde Baum dieses Waechters -- oder `None`, wenn er keinen braucht/hat.

    Gibt `(pfad, was)` zurueck, wenn der Baum DEKLARIERT ist und FEHLT.
    """
    eintrag = FREMDER_KORPUS.get(name)
    if not eintrag:
        return None
    pfad, was = eintrag
    ort = korpus_ort(pfad)
    return None if ort.is_dir() else (str(ort), was)


# Werkzeuge, die messen statt zu bewachen: sie duerfen ohne Sprechprobe stehen, brauchen aber
# Frist und roten Abbruch wie jedes andere.
ZAEHLER = {"zaehle-b3.py", "zaehle-bereichspflichten.py", "zaehle-narrow.py", "zaehle-fallen.sh"}

FUEHRT_AUS = re.compile(r"subprocess\.|os\.system|check_output|\bcargo\b|\bcc\b|\bisabelle\b")
# **Eine DEKLARIERTE Frist** -- `timeout`, `timeout=`, `TimeoutExpired` oder eine benannte
# Konstante (`FRIST`, `ZEIT`). Dass sie dasteht, heisst nicht, dass sie greift; `--lauf` ist
# die Haelfte, die das misst. *Die statische Haelfte verpflichtet, sie spricht nicht frei.*
HAT_FRIST = re.compile(r"timeout=|\btimeout\b|TimeoutExpired|\bFRIST\b|\bZEIT\b")
HAT_PROBE = re.compile(r"[Ss]prechprobe|speech test|Gegenprobe|[Ss]elbsttest")

# **THE SIXTH REQUIREMENT: A REFUSAL ENDS WITH 2, NOT WITH 1** (2026-08-31)
# ------------------------------------------------------------------------
# Requirement three says *"an abort leaves with a return code other than zero"*, and that is
# not enough: `1` is other than zero, and `1` is also what a FINDING looks like. On the night
# of 2026-08-31 twelve guardians printed the abort word and returned `1`, among them
# `pruefe-grammatiktafel.py`, whose refusal states that no run happened at all -- and in the
# collective run that was indistinguishable from the four uncovered cells it reports on a
# good day. **Twice that cost an hour.**
#
# > **A tool that measured nothing must not look like one that found something.**
#
# The rule the whole workshop now follows, and it answers ONE question -- *who has to
# change?*
#
#     1  the TREE has to change    -- a finding: a gap, a broken ratchet, a stale booking
#     2  the SETUP has to change   -- a missing tool, an empty population, a fallen speech
#                                     test, a deadline, an unreadable subject
#
# The detection reads a line that PRINTS a refusal and then the NEXT exit within six lines.
# It looks at the call site, not at the word alone -- prose about an abort is not an abort,
# the same lesson requirement five had to learn about `cc`.
ABSAGEWORT = re.compile(
    r"ABBRUCH|ABORT:|KEIN LAUF|NICHTS gemessen|NICHTS geprueft|NICHTS an ihnen|"
    r"NOTHING measured|nothing measured|measures nothing|misst NICHTS|misst nicht\b|"
    r"SPRECHPROBE GESCHEITERT|[Ss]prechprobe.*GESCHEITERT|OHNE NACHWEIS|"
    # **Any PROBE that falls, not just the one spelled `SPRECHPROBE`** (2026-08-31).
    # The list named the forward direction by name, and `zaehle-pflichten.py` prints
    # `RUECKWAERTSPROBE UNTAUGLICH` and `RUECKWAERTSPROBE GESCHEITERT` and ends both with
    # `1`. **Two fallen probes reading as findings, inside the very requirement built
    # against that** -- found by the cut sieve, not by this pattern. *A rule that lists the
    # words it has already seen measures the words it has already seen.*
    r"PROBE\b[^\n]*\b(?:GESCHEITERT|UNTAUGLICH)\b|"
    r"KEIN CC|KEIN GABBRO|NO GABBRO|NO LEAN|KEIN ISABELLE|Zaehlung misst|UEBERSEHEN")
# **The CALL SITE, not the word** -- `print(` has to BEGIN the statement. The first version
# searched for it anywhere in the line, and this guardian promptly reported itself: the
# explanation further down quotes a printed refusal inside a sentence, and that was enough.
# **Prose about a refusal is not a refusal** -- the very lesson requirement five had to learn
# about `cc`.
DRUCKT = re.compile(r"^\s*print\(|^\s*echo\b|;\s*echo\b|\{\s*echo\b")
AUSGANG = re.compile(r"sys\.exit\(\s*(\d+)\s*\)|SystemExit\(\s*(\d+)\s*\)|"
                     r"^\s*return\s+(\d+)\b|(?:^|;|\|\||\{)\s*exit\s+(\d+)\b")
# **THE OTHER HALF OF THE SIXTH, AND IT IS THE HALF THAT DOES NOT SHOUT** (2026-08-31)
# ------------------------------------------------------------------------------------
# The detection above needs a PRINTED refusal. A fallen speech test does not have to print
# anything:
#
#     if not sprechprobe():
#         return 1
#
# No abort word on the printing line -- because there is no printing line. **The rule was
# never about the word**, it is about the question *who has to change?*, and a guardian
# that cannot prove it measures says the SETUP has to change. Measured over `99e2145`, the
# stand this requirement was written against: the printed half found **44 places in 15
# files** and MISSED **nine** of exactly this form -- among them `pruefe-todo.py` and
# `pruefe-vergabe.py` **whole**, two files in which the printed half found nothing at all.
# The nine were then healed by hand, one at a time; *the tenth would not have come up.*
#
# What counts as a speech test is not decided a second time here (W7): it is the word set
# of `HAT_PROBE`, one line up, read in a CONDITION instead of anywhere in the file. Beside
# it stands the form that carries the result in a variable -- `if not tief_ok:` -- and only
# under a negation, because `if ok:` is the good path. **The looser pattern was measured
# and thrown out**: a bare `\bproben?\b` reports `$name-probe` and `abi-proben/` in
# `pruefe-emission.sh` -- four stage findings that are RIGHTLY a `1`. *A rule with false
# alarms gets ignored, and then it protects nothing.*
PROBENZWEIG = re.compile(
    r"^\s*(?:if|elif)\b(?:"
    r".*(?:[Ss]prechprobe|[Ss]elbsttest|Gegenprobe|[Ss]peech[_ ]test)"
    r"|.*\bnot\b.*\b\w+_ok\b"
    r"|.*\bnot\b.*\ball\(.*\bok\b)")


def _fixtur(z):
    """Eine Zeile, die mit einem Anfuehrungszeichen BEGINNT, ist Text und kein Code.

    **Und sie wurde an genau EINER Datei gebraucht: dieser hier.** Die Sprechprobe unten
    schreibt ihre erfundene Quelle als Zeichenkette, Zeile fuer Zeile -- darunter eine mit
    dem Ausgang 1. Ohne diesen Riegel liest der Waechter seine eigene Probe als Verstoss.
    *Ein Waechter, der seinen eigenen Text mitzaehlt, misst sich selbst* -- dieselbe Klasse
    wie das `pgrep -f`, das sich in `CLAUDE.md` selbst gefunden hat.
    """
    return z.strip()[:1] in ("'", '"')


def _mit_eins(text, trifft):
    """Die Zeilen, auf die `trifft` passt und deren NAECHSTER Ausgang eine `1` ist."""
    zeilen = text.splitlines()
    aus = []
    for i, z in enumerate(zeilen):
        if _fixtur(z) or not trifft(z):
            continue
        for j in range(i, min(i + 7, len(zeilen))):
            if _fixtur(zeilen[j]):
                continue
            m = AUSGANG.search(zeilen[j])
            if not m:
                continue
            if next(g for g in m.groups() if g is not None) == "1":
                aus.append(i + 1)
            break
    return aus


def absage_mit_eins(text):
    """Die Zeilen, die eine Absage DRUCKEN und deren naechster Ausgang eine `1` ist."""
    return _mit_eins(text, lambda z: bool(ABSAGEWORT.search(z) and DRUCKT.search(z)))


def stumme_probe_mit_eins(text):
    """Die Zweige, die eine SPRECHPROBE pruefen und mit `1` verlassen -- ohne ein Wort."""
    return _mit_eins(text, lambda z: bool(PROBENZWEIG.search(z)))


# **THE CUT IN THE MIDDLE OF THE RUN -- the class that the empty tree cannot reach**
# ---------------------------------------------------------------------------------
# `messung/RUECKLAUFWERTE.md` measured every guard over an EMPTY tree and closes with the
# sentence it could not measure: *"a guard whose precondition breaks MID-RUN is not covered
# here. The empty tree is the cheapest refusal, not the only one."*
#
# **On 2026-08-31 that sentence got a specimen with a date.** `pruefe-emission.sh` died at
# `F06`'s `N043` in its fourth stage with `exit 1`; **stages 9 and 10 never ran**, and not
# one line said so. The return code `1` read as a stage finding and was at the same time an
# abort for everything behind it. Two findings sat there unseen for two weeks -- six files
# whose emitted C does not compile, and a mark that was seven too low.
#
# > *An empty population is a green judgement over nothing (W17). A TRUNCATED population is
# > worse: it looks like a judgement over everything.*
#
# What is measured here, and it is a COARSE upper bound: everything after a guard's FIRST
# non-zero exit is behind a cut. A guard counts as affected when at least one further exit
# AND at least one printing site lie behind that first one -- **then a run exists that ends
# before the last measurement.** The per-guard figure is how many printing sites lie behind
# the first exit: *the output a truncated run can swallow.*
#
# **And what this does NOT say** (W10): it does not say that any of those exits is wrong. A
# speech test at the top of the file SHOULD end everything behind it -- that is the point of
# a speech test. The number is the SURFACE, not a defect list; it names where to look, and
# it verpflichtet, it does not absolve.
AUSGANG_STELLE = re.compile(r"^\s*sys\.exit\(\s*[12]\s*\)|^\s*return\s+[12]\b"
                            r"|(?:^|;|\|\||&&|\{)\s*exit\s+[12]\b")
DRUCK_STELLE = re.compile(r"^\s*print\(|^\s*echo\b")


def schnitt(text):
    """`(Ausgaenge hinter dem ersten, Druckstellen hinter dem ersten)` -- Zeilennummern."""
    aus, druck = [], []
    for nr, z in enumerate(text.splitlines(), 1):
        s = z.rstrip()
        if _fixtur(s) or s.lstrip().startswith("#"):
            continue
        if AUSGANG_STELLE.search(s):
            aus.append(nr)
        if DRUCK_STELLE.search(s):
            druck.append(nr)
    if not aus:
        return [], []
    erster = aus[0]
    return [a for a in aus if a > erster], [d for d in druck if d > erster]


# **Who carries this requirement: whoever's return code is read as a VERDICT.**
#
# **The boundary MOVED on 2026-08-31, and it moved because it was printed.** Until that day
# it ran `pruefe-*` and `mutiere-*` only; the 18 `zaehle-*` stood outside with the sentence
# *"they measure, they do not guard"* -- and with their count beside it, so that somebody
# could move it. Somebody did, and the measurement decided it:
#
# * Over an EMPTY tree not one of the 18 returned a green verdict. Six died of a
#   `FileNotFoundError` with return code 1; nine printed a refusal and returned 1. **They all
#   carry a verdict -- none of them had been GIVEN one.**
# * `zaehle-karten.py` had been arriving at `master` RED, over a broken ratchet (36/32
#   measured 40/36), and no collective run read it.
#
# What is left outside stands in `OHNE_URTEIL` below, by name and with its reason.
TRAEGT_URTEIL = ("pruefe-", "mutiere-", "zaehle-", "abnahme.py")

# **Counters deliberately left OUT of `abnahme.py`, each with its reason.**
# It stands empty today, and that is a measurement: every one of the 18 ends with 0, 1 or 2,
# and every one of them says something by it. *An empty exclusion is the only honest starting
# state -- what goes in has to be argued for.* `abnahme.py` reads this register and PRINTS
# its count, so the boundary stays visible the way the old one was.
OHNE_URTEIL = {}

# **Booked instead of healed** -- with the reason beside it, as everywhere in this workshop.
# **It stands EMPTY since 2026-08-31, and that is a measurement and not an oversight.**
# Its one entry was `pruefe-zahlen.py`, booked because a second track was translating that
# file the same night -- two runs on one source destroy each other (`CLAUDE.md`). Both its
# places are healed now: the printed refusal at the dynamic self-reference guard, and the
# silent `if not tief_ok: return 1` that only the other half of the sixth requirement can
# see. *An empty booking is the only honest starting state -- what goes in has to be argued
# for.*
ABBRUCH_GEBUCHT = {}
# **`[1-9]` and not `1` -- and this guardian reported the flaw on itself** (2026-08-31).
# Requirement three reads *"an abort leaves with a return code other than zero"*, and the
# pattern recognised exactly one digit of that. The moment three guardians moved their fallen
# speech test from `return 1` to `return 2` -- from *"finding"* to *"ABORT"*, which is what
# this requirement means -- this tool reported all three of them as violating it. **A
# rule that punishes the right answer measures a habit, not the rule.** Same class as W16,
# one level up: inside the guardian over the guardians.
HAT_ROT = re.compile(
    r"sys\.exit\(\s*[1-9]|SystemExit\(\s*[1-9]|exit\s+[1-9]\b|return\s+[1-9]\b|returncode")
# **Eine ARBEITSMENGE in der Ausgabe**: `N von M`, `N Dateien`, `N Stellen`. Statisch ist das
# nur ein Hinweis; `--lauf` liest die wirkliche Ausgabe, und das ist die Haelfte, die zaehlt.
ARBEIT = re.compile(r"\b\d+\s+(?:von|of)\s+\d+\b|\b\d+\s+[A-Za-zÄÖÜäöüß][A-Za-zÄÖÜäöüß-]{3,}")
# **Fifth requirement: the LOCALE.** These tools report translated -- whoever calls them
# must set `LC_ALL=C`, or they measure the user's language.
#
# **The name alone is NOT enough as detection.** `mutiere-pruefer.py` mentions `cc` nine
# times in mutation descriptions and runs only `cargo test` -- a word pattern reports it red,
# and a guardian with false alarms gets ignored. So what is searched for is the CALL SITE:
# in Python the tool name as a string in an argument list, in the shell at the start of a
# command and without comment lines.
UEBERSETZTE = "cc|gcc|clang|ld|nm|objdump|readelf"
RUFT_UEBERSETZT_PY = re.compile(rf"""["'](?:{UEBERSETZTE})["']""")
# `sort` orders and `date` formats by locale -- but only in the SHELL. Python's `sorted`
# orders by code point and is untouched by it; the requirement does not apply there.
RUFT_UEBERSETZT_SH = re.compile(rf"(?m)^\s*(?:[!(]\s*)*(?:{UEBERSETZTE}|sort|date)\b")
KOMMENTARZEILE = re.compile(r"(?m)^\s*#.*$")
HAT_GEBIETSSCHEMA = re.compile(r"\bLC_ALL\b")


def waechter(wurzel=None):
    aus = []
    w = wurzel or W
    # **`abnahme.py` joined on 2026-08-30, and it very nearly did not.** The collective run is
    # not called `pruefe-*` and would have slipped through every mesh above -- a tool that
    # establishes the reach of acceptance while standing outside acceptance itself. *Exactly
    # what it was built against, one level up.*
    #
    # **`fuzze-*` joined on 2026-09-02, and for the same reason a second time.** The boundary
    # sweep is not called `pruefe-*` either, and it carries a judgement about the checker --
    # *a tool that hunts for a third answer while standing outside every mesh that asks
    # whether a tool can speak.* The class the line above names is not a one-off: **every new
    # verb invents a new prefix**, and each one silently leaves this net. The glob is widened
    # rather than the file renamed, so the next `fuzze-*` is inside it on the day it is
    # written.
    for p in sorted(w.glob("instrumente/pruefe-*.py")) + sorted(w.glob("instrumente/pruefe-*.sh")) \
            + sorted(w.glob("instrumente/zaehle-*.py")) + sorted(w.glob("instrumente/zaehle-*.sh")) \
            + sorted(w.glob("instrumente/fuzze-*.py")) \
            + sorted(w.glob("instrumente/mutiere-*.py")) + sorted(w.glob("instrumente/abnahme.py")):
        aus.append(p)
    return aus


# **DIE BESETZUNG IST EIN NAMENSMUSTER, UND JEDES NEUE VERB VERLAESST SIE STILL**
# --------------------------------------------------------------------------------
# (2026-09-02, und der Befund ist gemessen und nicht vermutet.)
#
# `waechter()` darueber sagt es selbst -- *„every new verb invents a new prefix, and each one
# silently leaves this net"* -- und heilt es durch Weiten. Am 2026-09-02 standen sechs
# Werkzeuge in `instrumente/` ausserhalb, und das Verhaeltnis war:
#
#     INNERHALB   0 von 57 tragen eine Verletzung
#     AUSSERHALB  3 von  6:  vergleiche-binaerprogramme.py  SPRECHPROBE
#                            miss-c-signaturen.py           FRIST, SPRECHPROBE
#                            abschnitt.sh                   SPRECHPROBE
#
# > **Der Waechter war gruen ueber 57 Werkzeugen, weil die drei, die ihn haetten roetten
# > koennen, ausserhalb seines Globs hiessen.** Genau die Klasse, gegen die er gebaut ist,
# > eine Ebene ueber seinem Urteil: *ein Werkzeug, das keine Liste erreicht, ist von einem
# > fehlerfreien nicht zu unterscheiden -- es fehlt einfach.*
#
# Der Glob wird hier NICHT geweitet. Das Weiten hat den Fehler dreimal nicht verhindert, und
# es zieht `--lauf` mit: eine Bibliothek und ein Werkzeug mit 1200 `cc`-Rufen zu FAHREN ist
# eine Entscheidung ueber den Sammellauf. Stattdessen wird die Luecke GEZAEHLT und benannt --
# und sie ist ROT, sobald ein Werkzeug ausserhalb eine Verletzung traegt und keinen Grund.
# *Ein Loch mit einem Namen ist kein Haken und kein Kreuz.*
AUSSERHALB_GEBUCHT = {
    "abschnitt.sh":
        "eine EINGEBUNDENE Schalenbibliothek, kein Waechter -- sie hat kein eigenes `main`, "
        "und ihre Sprechprobe wird in DIESER Datei gefahren (`sprechprobe_schale()`), "
        "in beide Richtungen, bei jedem Lauf",
}


def ausserhalb_der_besetzung(wurzel=None):
    """Jedes Werkzeug in `instrumente/`, das `waechter()` NICHT erreicht."""
    w = wurzel or W
    drin = {p.name for p in waechter(w)}
    return sorted(p for p in w.glob("instrumente/*")
                  if p.suffix in (".py", ".sh") and p.name not in drin)


def sprechprobe_besetzung():
    """`[(was, ok)]` -- **wird ein Werkzeug ausserhalb des Musters wirklich GESEHEN?**

    In beide Richtungen, an einem Gegenstand, den dieser Lauf mitbringt: ein `instrumente/`
    mit drei Dateien, deren Namen die Besetzung verschieden trifft. *Eine Zaehlung, die den
    Ausserhalbstehenden nicht findet, meldet null und liest sich wie null.*
    """
    ganz = ("import subprocess\n"
            "# Sprechprobe: eine kaputte Eingabe MUSS fallen\n"
            "subprocess.run(['x'], timeout=5)\n"
            "raise SystemExit(2)\n")
    nackt = "print('nichts')\n"
    with tempfile.TemporaryDirectory() as d:
        ort = pathlib.Path(d)
        (ort / "instrumente").mkdir()
        (ort / "instrumente" / "vergleiche-heil.py").write_text(ganz, encoding="utf-8")
        (ort / "instrumente" / "schnuppere-kaputt.py").write_text(nackt, encoding="utf-8")
        (ort / "instrumente" / "pruefe-drin.py").write_text(ganz, encoding="utf-8")
        namen = [q.name for q in ausserhalb_der_besetzung(ort)]
        kaputt = statisch(ort / "instrumente" / "schnuppere-kaputt.py")
        heil = statisch(ort / "instrumente" / "vergleiche-heil.py")
    return [
        ("ein Werkzeug mit unbekanntem Verb steht AUSSERHALB",
         namen == ["schnuppere-kaputt.py", "vergleiche-heil.py"]),
        ("und eines mit bekanntem Verb NICHT", "pruefe-drin.py" not in namen),
        (f"das nackte faellt dort auf: {', '.join(kaputt) or 'NICHTS'}",
         set(kaputt) == {"SPRECHPROBE", "ROT-BEI-ABBRUCH"}),
        ("das vollstaendige bleibt still", heil == []),
    ]


def statisch(p):
    """Die Forderungen am Quelltext. Gibt die Liste der VERLETZUNGEN."""
    t = p.read_text(encoding="utf-8", errors="replace")
    fehlt = []
    if p.name.startswith(TRAEGT_URTEIL) and p.name not in ABBRUCH_GEBUCHT:
        if stellen := absage_mit_eins(t):
            fehlt.append("ABSAGE-MIT-1 (Zeile " + ", ".join(map(str, stellen)) + ")")
        if stellen := stumme_probe_mit_eins(t):
            fehlt.append("STUMME-PROBE-MIT-1 (Zeile " + ", ".join(map(str, stellen)) + ")")
    if FUEHRT_AUS.search(t) and not HAT_FRIST.search(t):
        fehlt.append("FRIST")
    if p.name not in ZAEHLER and not HAT_PROBE.search(t):
        fehlt.append("SPRECHPROBE")
    if not HAT_ROT.search(t):
        fehlt.append("ROT-BEI-ABBRUCH")
    if p.suffix == ".sh":
        ruft_uebersetzt = RUFT_UEBERSETZT_SH.search(KOMMENTARZEILE.sub("", t))
    else:
        ruft_uebersetzt = RUFT_UEBERSETZT_PY.search(t)
    if ruft_uebersetzt and not HAT_GEBIETSSCHEMA.search(t):
        fehlt.append("GEBIETSSCHEMA")
    return fehlt


def sprechprobe():
    """**In beide Richtungen, an erfundenen Quellen.** Ein Waechter, der nur die eigenen
    Dateien liest, misst, wie gut sie zu ihm passen."""
    import tempfile
    gut = ('import subprocess, sys\n'
           '# Sprechprobe: eine kaputte Eingabe MUSS fallen\n'
           'subprocess.run(["true"], timeout=5)\n'
           'sys.exit(1)\n')
    # **`cc` instead of `cargo`** -- so the broken source violates the FIFTH one too: it
    # calls a tool that reports translated and does not pin the locale.
    schlecht = 'import subprocess\nsubprocess.run(["cc", "-o", "a", "a.c"])\nprint("ok")\n'
    # **And the counter-direction of the fifth:** the same source WITH `LC_ALL` must not
    # violate it. Without this half the requirement would be a ban on `cc`, not a
    # requirement.
    gut_lc = ('import subprocess, sys\n'
              '# Sprechprobe: eine kaputte Eingabe MUSS fallen\n'
              'subprocess.run(["cc", "-o", "a", "a.c"], timeout=5,\n'
              '               env={"LC_ALL": "C"})\n'
              'sys.exit(1)\n')
    with tempfile.TemporaryDirectory() as d:
        a = pathlib.Path(d) / "pruefe-gut.py"
        b = pathlib.Path(d) / "pruefe-schlecht.py"
        c = pathlib.Path(d) / "pruefe-gut-lc.py"
        a.write_text(gut, encoding="utf-8")
        b.write_text(schlecht, encoding="utf-8")
        c.write_text(gut_lc, encoding="utf-8")
        # **Third direction: prose about `cc` is not a call.** Exactly the false alarm
        # `mutiere-pruefer.py` triggered before the detection looked for the call site.
        e = pathlib.Path(d) / "pruefe-prosa.py"
        e.write_text('import subprocess, sys\n'
                     '# Sprechprobe: `cc` und `ld` stehen hier nur im Text.\n'
                     'subprocess.run(["cargo", "test"], timeout=5)\n'
                     'sys.exit(1)\n', encoding="utf-8")
        # **Fourth direction: an abort with `2` is RED.** The requirement says "other than
        # zero", not "equal to one" -- and until 2026-08-31 the pattern held the digit 1.
        # This source has NO exit with 1 and must come back clean all the same.
        g = pathlib.Path(d) / "pruefe-zwei.py"
        g.write_text('import subprocess, sys\n'
                     '# Sprechprobe: eine kaputte Eingabe MUSS fallen\n'
                     'subprocess.run(["cargo", "test"], timeout=5)\n'
                     'print("== 3 von 3 Stellen ==")\n'
                     'sys.exit(2)\n', encoding="utf-8")
        # **The sixth requirement, in BOTH directions** -- and the second one matters more:
        # without it the rule would be a ban on the abort word rather than a rule.
        h = pathlib.Path(d) / "pruefe-absage-eins.py"
        h.write_text('import subprocess, sys\n'
                     '# Sprechprobe: eine kaputte Eingabe MUSS fallen\n'
                     'subprocess.run(["cargo", "test"], timeout=5)\n'
                     'print("== 3 von 3 Stellen ==")\n'
                     'if not subprocess.run(["true"]).returncode:\n'
                     '    print("ABBRUCH: der Korpus fehlt -- es wurde NICHTS gemessen.")\n'
                     '    sys.exit(1)\n', encoding="utf-8")
        i = pathlib.Path(d) / "pruefe-absage-zwei.py"
        i.write_text(h.read_text(encoding="utf-8").replace("sys.exit(1)", "sys.exit(2)"),
                     encoding="utf-8")
        # **The OTHER half of the sixth, in both directions too** -- a fallen speech test
        # that prints NOTHING. This source carries no abort word anywhere; the printed half
        # comes back clean over it, and that is exactly the gap this probe is here for.
        j = pathlib.Path(d) / "pruefe-stumm-eins.py"
        j.write_text('import subprocess, sys\n'
                     'subprocess.run(["cargo", "test"], timeout=5)\n'
                     'print("== 3 von 3 Stellen ==")\n'
                     'def sprechprobe():\n'
                     '    return False\n'
                     'if not sprechprobe():\n'
                     '    sys.exit(1)\n', encoding="utf-8")
        k = pathlib.Path(d) / "pruefe-stumm-zwei.py"
        k.write_text(j.read_text(encoding="utf-8").replace("sys.exit(1)", "sys.exit(2)"),
                     encoding="utf-8")
        f_gut, f_schlecht, f_gut_lc = statisch(a), statisch(b), statisch(c)
        f_prosa = statisch(e)
        f_zwei = statisch(g)
        f_a1, f_a2 = statisch(h), statisch(i)
        f_s1, f_s2 = statisch(j), statisch(k)
        # **And the printed half must NOT see it** -- otherwise the new half would be
        # measuring something the old one already caught, and the nine missed places would
        # have no explanation.
        stumm_ist_stumm = not absage_mit_eins(j.read_text(encoding="utf-8"))
    # **Und die vierte Forderung, an ihrer eigenen Regex.** Ein gruener Lauf ohne Zahl
    # daneben MUSS auffallen; einer mit Zahl NICHT.
    leer_faellt = not ARBEIT.search("== ALL PASS ==\nok\n")
    voll_faellt = bool(ARBEIT.search("== 23 von 23 tragen alle drei ==\n"))
    a1 = len(f_a1) == 1 and f_a1[0].startswith("ABSAGE-MIT-1")
    s1 = len(f_s1) == 1 and f_s1[0].startswith("STUMME-PROBE-MIT-1")
    ok = (not f_gut and not f_gut_lc and not f_prosa and not f_zwei and a1 and not f_a2
          and s1 and not f_s2 and stumm_ist_stumm
          and set(f_schlecht) == {"FRIST", "SPRECHPROBE", "ROT-BEI-ABBRUCH", "GEBIETSSCHEMA"}
          and leer_faellt and voll_faellt)
    return (ok, f_gut, f_schlecht, f_gut_lc, f_prosa, f_zwei, a1, f_a2,
            s1, f_s2, stumm_ist_stumm, leer_faellt, voll_faellt)


# **The speech test of the cut, BOTH ways.** A guardian with ONE exit at the very end must
# not read as cut; one that still prints and still leaves again behind its first exit must.
# *A measure that answers in one direction only is an ornament* (R14).
SCHNITT_HEIL = "\n".join([
    "import sys",
    "print('a')",
    "print('b')",
    "sys.exit(1)",
])
SCHNITT_KAPUTT = "\n".join([
    "import sys",
    "print('a')",
    "sys.exit(2)",
    "print('b')",
    "sys.exit(1)",
])


def sprechprobe_schnitt():
    """`(heil_ist_frei, kaputt_faellt)` -- und beide muessen stimmen."""
    a_heil, d_heil = schnitt(SCHNITT_HEIL)
    a_kap, d_kap = schnitt(SCHNITT_KAPUTT)
    return (not (a_heil and d_heil), bool(a_kap and d_kap))


# **THE DANGEROUS SUBSET OF THE SURFACE -- and it is the SMALL one, not the big one**
# ------------------------------------------------------------------------------------
# `schnitt()` above counts the SURFACE: 249 exit sites behind a first one. That figure is an
# upper bound and says so. **This is the sieve underneath it**, and it exists because a
# surface nobody can shrink stops being read.
#
# Three cuts, each of which removes places that are NOT the hazard:
#
# 1. **Does it end the run at all?** A `return 1` inside a helper function is a VALUE, not an
#    exit -- the caller reads it and carries on. Only `sys.exit(...)`, a `return` out of
#    `main()`, and every `exit` in a shell script actually end the run.
# 2. **Which return code?** `2` means ABORT: the guard says *nothing measured*, and
#    `abnahme.py` prints it as `ABBRUCH` with its own word and its own colour. Reaching it
#    takes a BROKEN precondition -- a missing tool, a fallen speech test, an empty
#    population. `1` means FINDING, and a finding is reachable **with everything intact**:
#    the tree merely has a flaw. *That is the half that needs nothing to be broken.*
# 3. **Is there output on BOTH sides?** Output before the exit means a partial measurement
#    exists on screen; output behind it means something was skipped. Only both together make
#    the shape this class is named for: **a half-run that reads like a whole one.**
#
# What survives all three is the working list. And what takes a place OFF it is the form
# `pruefe-emission.sh` grew on 2026-08-31: a run that stops early **says where it stopped**.
# A file that carries that announcement is counted as covered -- its truncated runs are
# still truncated, but they no longer look complete.
#
# > *An abort names its reason (that is the third class of the table). A cut has to name its
# > PLACE -- the reason is already printed, and it is a finding.*
# Three shapes counted as covered, and each one was the WIRING, never the mere presence of
# the helper: the word itself (a guard carrying its own `trap`, as `pruefe-emission.sh`
# does), `abschnitt.fahre(` (Python, the wrapper around `main`), or an `EXIT` trap that
# calls `abschnitt_ende` (shell). **`import abschnitt` or `. abschnitt.sh` alone was NOT
# enough** -- a tool that loads the helper and never hands its run to it announces nothing.
# *A rule that counts the import counts the intention.*
#
# **AND SINCE 2026-08-31 THIS IS NO LONGER THE COUNTER. IT IS THE COUNTER'S FOIL.**
# `teilmessungen()` asks `stelle_gedeckt()` below, per PLACE. `SAGT_WO` reads the whole file
# and therefore cannot tell one exit from another -- which is exactly the property the last
# direction of `sprechprobe_deckung()` uses: the two fixtures that the per-place count
# rejects both match this pattern. *It is kept because a sharper rule that never gets
# compared to the blunt one is a claim, not a measurement* -- and it is kept OUT of the
# verdict, so that nothing depends on it twice (W7).
SAGT_WO = re.compile(r"ABGESCHNITTEN|abschnitt\.fahre\(|trap [^\n]*abschnitt_ende")

# **AND COVERAGE IS COUNTED PER PLACE, NOT PER FILE** -- measured 2026-08-31.
# --------------------------------------------------------------------------
# `SAGT_WO` above reads the FILE. It answers *does this guardian announce a cut at all?* and
# it was never able to answer the question underneath: *does it announce THIS one?* A trap
# that arms halfway down the file does not cover the exits above it, and a file counted as
# covered because one of its places is covered hides all the others -- the same shape this
# whole section is built against, one level up.
#
# The previous lane found two such places BY HAND (`pruefe-syntax.sh`, `pruefe-sonden.sh`,
# one exit each above their trap) and wrote down that the class stayed unmeasured. It is
# measured now, and the answer is zero -- *the class was not empty, it had been emptied.*
#
# **What "per place" means is not the same in both languages, and that is the whole point:**
#
# | | a place is covered when | why |
# |---|---|---|
# | shell | its line is BEHIND the `EXIT` trap -- or it sits inside a function body | a trap arms at its line. An `exit` above it walks straight past. |
# | Python | it lies lexically inside a `def` | `fahre()` wraps the CALL of `main`. Whatever runs at module level runs BEFORE `fahre` -- the subject bolt, for one. |
#
# **And it asks for the WIRING, never for the word.** `SAGT_WO` matches on file text, so two
# guardians carry `ABGESCHNITTEN` in their own prose and count as covered without a single
# line being wired: `pruefe-waechter.py` (this rule itself stands in it) and `abnahme.py`
# (it prints the mark). Both have zero dangerous places today, so it costs nothing today --
# *a trap laid, not a loss taken*, and it lies under exactly the two tools that print this
# number. **A yardstick that acquits itself does it silently.**
TRAP_STELLE = re.compile(r"trap\s+(.+?)\s+EXIT")
SH_FUNKTION = re.compile(r"^\s*(?:function\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*\(\s*\)\s*\{")
PY_DEF = re.compile(r"^(\s*)def\s+\w+")


def deckung_ab(text, ist_shell):
    """From which line on is the cut notice WIRED? `None` means: nowhere."""
    zeilen = text.splitlines()
    if ist_shell:
        # A guardian may carry its own notice instead of sourcing `abschnitt.sh`
        # (`pruefe-emission.sh` does). Then the trap names ITS function.
        eigen, akt = set(), None
        for z in zeilen:
            m = SH_FUNKTION.match(z)
            if m:
                akt = m.group(1)
            if akt and "ABGESCHNITTEN" in z:
                eigen.add(akt)
        for nr, z in enumerate(zeilen, 1):
            if _fixtur(z) or z.lstrip().startswith("#"):
                continue
            m = TRAP_STELLE.search(z)
            if m and ("abschnitt_ende" in m.group(1)
                      or any(f in m.group(1) for f in eigen)):
                return nr
        return None
    for nr, z in enumerate(zeilen, 1):
        if _fixtur(z) or z.lstrip().startswith("#"):
            continue
        if "abschnitt.fahre(" in z:
            return nr
    return None


def _in_funktion(zeilen, nr, ist_shell):
    """Does line `nr` (1-based) sit inside a function body?"""
    if ist_shell:
        offen = 0
        for z in zeilen[:nr - 1]:
            if SH_FUNKTION.match(z):
                offen += 1
            elif offen and z[:1] == "}":
                offen -= 1
        return offen > 0
    s = zeilen[nr - 1]
    tiefe = len(s) - len(s.lstrip())
    if tiefe == 0:
        return False
    return any(m and len(m.group(1)) < tiefe
               for m in (PY_DEF.match(zeilen[j]) for j in range(nr - 2, -1, -1)))


def stelle_gedeckt(zeilen, nr, ist_shell, ab):
    """Is the exit on line `nr` covered by the wiring that starts on line `ab`?"""
    if ab is None:
        return False
    if ist_shell:
        return nr > ab or _in_funktion(zeilen, nr, True)
    return _in_funktion(zeilen, nr, False)

# **WHO READS `git` -- AND WHAT DOES HE DO WITHOUT A REPOSITORY?**
# ------------------------------------------------------------------
# (2026-08-31. Same class as `FREMDER_KORPUS`, one level down.)
#
# `mutiere-pruefer.py --anker` was green here and red on `ki-pc-fisch-101` on byte-identical
# sources. The tree there arrives by `rsync` and is **no repository**, so `git status` exits
# 128 with an empty stdout. Three tools asked that one question, in three own copies:
#
# | | without a repository | |
# |---|---|---|
# | `mutiere-pruefer.py` | speech test FELL over its own tree reporting `unbekannt` | a working tool calling itself broken |
# | `pruefe-luecken.py` | read `stdout` only -- empty means CLEAN, and it **writes into sources** | the guard against a mixture was inert on the server it is sent to |
# | `erzeuge-mutationen.py` | `git diff --quiet` returns 128, read as *dirty tree* | a false reason: it sends the reader to fix a clean tree |
#
# > *A guardian whose verdict depends on which machine it runs on, without saying so,
# > measures the machine.*
#
# The register is now ONE (`mutiere-pruefer.py:baumstand()`, three states, speech test on a
# subject the run brings along). What this check keeps out is the FOURTH copy: whoever calls
# `git` himself has to look at the return code, because *an empty output from a command that
# failed is not an answer.*
# **The CALL SITE, not the name in a message.** `git status` appears in half a dozen
# refusal texts in this directory; a rule with false alarms gets ignored, and then it
# protects nothing (the same lesson the sixth requirement learned over `$name-probe`).
GIT_AUFRUF = re.compile(r"""\[\s*["']git["']|(?:^|;|\||&&|\()\s*git\s+[a-z-]+""")
GIT_GEPRUEFT = re.compile(r"returncode|baumstand|\$\?|&&|\|\||if\s+git\b|check=True")


def git_ohne_riegel(text):
    """Call sites that read `git` and do NOT look at its return code within ten lines."""
    zeilen = text.splitlines()
    aus = []
    for i, z in enumerate(zeilen):
        if (_fixtur(z) or z.lstrip().startswith("#") or DRUCK_STELLE.search(z)
                or not GIT_AUFRUF.search(z)):
            continue
        fenster = "\n".join(zeilen[max(0, i - 2):i + 11])
        if not GIT_GEPRUEFT.search(fenster):
            aus.append(i + 1)
    return aus
_DEF = re.compile(r"^(\s*)def\s+(\w+)")
_WERT = re.compile(r"sys\.exit\(\s*([12])\s*\)|return\s+([12])\b|exit\s+([12])\b")


def _beendet_den_lauf(zeilen, nr, s, ist_shell):
    """Does the exit on line `nr` end the RUN -- or merely a function?"""
    if ist_shell:
        return True
    if not re.match(r"^\s*return\b", s):
        return True          # `sys.exit(...)` -- always.
    tiefe = len(s) - len(s.lstrip())
    for j in range(nr - 2, -1, -1):
        m = _DEF.match(zeilen[j])
        if m and len(m.group(1)) < tiefe:
            return m.group(2) == "main"
    return False


def schnitt_stellen(text, ist_shell):
    """Per exit behind the first: `(line, code, ends_the_run, partial_measurement)`."""
    zeilen = text.splitlines()
    aus, druck = [], []
    for nr, z in enumerate(zeilen, 1):
        s = z.rstrip()
        if _fixtur(s) or s.lstrip().startswith("#"):
            continue
        if AUSGANG_STELLE.search(s):
            m = _WERT.search(s)
            wert = next((g for g in m.groups() if g), "?") if m else "?"
            aus.append((nr, wert, s))
        if DRUCK_STELLE.search(s):
            druck.append(nr)
    if not aus or not druck:
        return []
    erster = aus[0][0]
    if not any(d > erster for d in druck):
        return []
    stellen = []
    for nr, wert, s in aus:
        if nr <= erster:
            continue
        stellen.append((nr, wert, _beendet_den_lauf(zeilen, nr, s, ist_shell),
                        any(d < nr for d in druck) and any(d > nr for d in druck)))
    return stellen


def teilmessungen(pfade):
    """`(total, ending, finding, partial, covered, open_per_file)` over all guardians."""
    gesamt = beendend = befund = teil = gedeckt = 0
    offen = {}
    for p in pfade:
        t = p.read_text(encoding="utf-8", errors="replace")
        ist_shell = p.suffix == ".sh"
        zeilen = t.splitlines()
        ab = deckung_ab(t, ist_shell)
        n_offen = 0
        for nr, wert, beendet, ist_teil in schnitt_stellen(t, ist_shell):
            gesamt += 1
            if not beendet:
                continue
            beendend += 1
            if wert != "1":
                continue
            befund += 1
            if not ist_teil:
                continue
            teil += 1
            if stelle_gedeckt(zeilen, nr, ist_shell, ab):
                gedeckt += 1
            else:
                n_offen += 1
        if n_offen:
            offen[p.name] = n_offen
    return gesamt, beendend, befund, teil, gedeckt, offen


# **The ratchet over the working list -- it may only FALL.**
# Measured 2026-08-31 over `283cb26`: 249 sites, of which 246 end the run, 106 leave with
# code 1 (reachable with nothing broken), 94 carry output on both sides -- and 45 of those
# sat in `pruefe-emission.sh`, which prints `ABGESCHNITTEN in:` since that same day.
# **49 stayed open, in 25 files.**
#
# **Same evening: 49 -> 19 -> 0.** `abschnitt.py` gave the 19 Python guards the same form,
# `abschnitt.sh` gave it to the five shell guards, and the last two places -- two fallen
# BACKWARD probes in `zaehle-pflichten.py` that ended with `1` -- turned out not to need the
# form at all: *a fallen probe measured nothing, and its exit is a `2`.* Requirement six had
# listed the forward direction by name and never saw them; this sieve did.
#
# **The ratchet stands at 0, and that is not a finish line.** A covered site still cuts the
# run -- it merely SAYS so, and `abnahme.py` prints it as `TEILMESSUNG` instead of as a
# finding. What is measured here is whether the cut is announced, never whether it is right.
#
# **2026-08-31, second reading: the count moved from PER FILE to PER PLACE, and the mark did
# not move.** That is a measurement, not luck: all 92 dangerous places in 25 files sit behind
# their own wiring, the two tightest being `pruefe-beweise.sh` (trap on line 21, first exit
# on 72) and `pruefe-syntax.sh` (11 / 70) -- both pulled up the evening before. *Had the mark
# risen here, it would have been a CORRECTION and not a regression*, because the coarser
# count could only ever have been too kind. It did not rise.
MARKE_TEILMESSUNG = 0


# **The speech test of the sieve, in FOUR directions.** Three cuts, and each has to bite on
# its own -- otherwise the sieve measures a habit instead of a rule.
SIEB_HELFER = "\n".join([
    "import sys", "print('a')", "sys.exit(2)", "print('b')",
    "def hilf():", "    return 1", "print('c')",
])
SIEB_ZWEI = "\n".join([
    "import sys", "print('a')", "sys.exit(2)", "print('b')", "sys.exit(2)", "print('c')",
])
SIEB_RAND = "\n".join([
    "import sys", "print('a')", "sys.exit(2)", "print('b')", "sys.exit(1)",
])
SIEB_ECHT = "\n".join([
    "import sys", "print('a')", "sys.exit(2)", "print('b')", "sys.exit(1)", "print('c')",
])


# **The speech test of the git check, in three directions.** A call site WITHOUT a look at
# the return code must fall; one WITH it must not; and the tool name inside a printed
# refusal must not count as a call. *A rule with false alarms gets ignored, and then it
# protects nothing.*
GIT_OFFEN = "\n".join([
    "import subprocess",
    "r = subprocess.run(['git', 'status', '--porcelain'], capture_output=True, text=True)",
    "if r.stdout.strip():",
    "    print('schmutzig')",
])
GIT_ZU = "\n".join([
    "import subprocess",
    "r = subprocess.run(['git', 'status', '--porcelain'], capture_output=True, text=True)",
    "if r.returncode != 0:",
    "    print('unbekannt')",
])
GIT_PROSA = "\n".join([
    "print('  `git status` auf einer uebertragenen Kopie (128, leere Ausgabe).')",
    "print('  erst committen')",
])


def sprechprobe_auscheckung():
    """`[(what, ok)]` -- **four directions, on invented checkouts, never on the real one.**

    A probe that reads the tree it runs in passes or fails by where somebody put the
    repository -- the very fault this function exists against. So all four cases are built in
    a throwaway directory: a plain checkout, a worktree, a `.git` file with nonsense in it,
    and no `.git` at all. **The last two must fall back to the directory itself**, because
    the wrong answer there is a corpus reported present at a place nobody measured.
    """
    with tempfile.TemporaryDirectory() as d:
        dp = pathlib.Path(d).resolve()
        haupt = dp / "haupt"
        (haupt / ".git" / "worktrees" / "zweig").mkdir(parents=True)
        baum = dp / "haupt" / ".claude" / "worktrees" / "zweig"
        baum.mkdir(parents=True)
        (baum / ".git").write_text(f"gitdir: {haupt}/.git/worktrees/zweig\n")
        wirr = dp / "wirr"
        wirr.mkdir()
        (wirr / ".git").write_text("nicht der Rede wert\n")
        nackt = dp / "nackt"
        nackt.mkdir()
        return [
            ("eine gewoehnliche Auscheckung ist ihre eigene Hauptauscheckung",
             hauptauscheckung(haupt) == haupt),
            ("ein `git worktree` findet die Hauptauscheckung darueber",
             hauptauscheckung(baum) == haupt),
            ("eine `.git`-Datei ohne `gitdir:` faellt auf den Baum selbst zurueck",
             hauptauscheckung(wirr) == wirr),
            ("und ohne `.git` ebenso -- nie auf einen erratenen Ort",
             hauptauscheckung(nackt) == nackt),
            ("und ein ABSOLUTER Korpuspfad bleibt, wie er ist",
             korpus_ort("/nirgends/korpus", baum) == pathlib.Path("/nirgends/korpus")),
            ("ein relativer wird gegen die HAUPTauscheckung aufgeloest, nicht gegen den Baum",
             korpus_ort("../korpus", baum) == (dp / "korpus")),
        ]


def sprechprobe_git():
    """`[(what, ok)]` -- the bolt has to be able to fall, and must not fall everywhere."""
    return [
        ("ein `git`-Aufruf ohne Blick auf den Ruecklaufwert FAELLT",
         git_ohne_riegel(GIT_OFFEN) == [2]),
        ("derselbe Aufruf mit `returncode` kommt durch",
         git_ohne_riegel(GIT_ZU) == []),
        ("`git status` in einem ABSAGETEXT ist keine Aufrufstelle",
         git_ohne_riegel(GIT_PROSA) == []),
    ]


# **And the SHELL half gets driven too** -- `abschnitt.sh` is sourced by five guardians and
# reached by no collective run of its own. *A tool nobody drives is indistinguishable from
# one that does not exist*, and here it would be worse than absent: a silent `abschnitt_ende`
# would let five guardians read as covered while announcing nothing.
#
# **Built line by line, every line BEGINNING with a quote** -- and that is not style. A
# fixture written as a block string puts a bare `exit 1` at the start of a line, and the cut
# measurement above then counts this guardian's own probe text as a real exit site. It did:
# the surface read 253 instead of 251 the moment these two were added. *A guardian that
# counts its own fixture measures itself* -- exactly what `_fixtur` is for.
SCHALE_AB = "\n".join([
    '. "%s/abschnitt.sh"',
    "trap 'abschnitt_ende' EXIT",
    'stufe "Stufe 4: der Differenztest"',
    "exit 1",
])
SCHALE_GANZ = "\n".join([
    '. "%s/abschnitt.sh"',
    "trap 'abschnitt_ende' EXIT",
    'stufe "Stufe 9: jede Datei uebersetzt"',
    "abschnitt_fertig",
    "exit 1",
])


def sprechprobe_schale():
    """`[(what, ok)]` -- the shell notice must fire on a cut and stay quiet on a full run."""
    ort = str(W / "instrumente")

    def lauf(vorlage):
        r = subprocess.run(["bash", "-c", vorlage % ort], capture_output=True, text=True,
                           timeout=FRIST, cwd=W)
        return r.returncode, r.stdout
    rc_ab, aus_ab = lauf(SCHALE_AB)
    rc_ganz, aus_ganz = lauf(SCHALE_GANZ)
    return [
        ("die Schale sagt einen Schnitt an und behaelt den Ruecklaufwert",
         rc_ab == 1 and "ABGESCHNITTEN in: Stufe 4: der Differenztest" in aus_ab),
        ("nach `abschnitt_fertig` schweigt sie -- auch bei 1",
         rc_ganz == 1 and "ABGESCHNITTEN" not in aus_ganz),
    ]


# **The speech test of the PER-PLACE count, in both directions** -- and the first one is the
# one that matters: an uncovered place in an otherwise covered file HAS to stand out.
# *A coverage rule that cannot fail anywhere covers everything.*
DECKUNG_SPAET = "\n".join([          # shell: one `exit 1` above the trap, one below
    '"echo a"',
    '"exit 2"',
    '"echo b"',
    '"exit 1"',
    '"echo c"',
    '"trap \'abschnitt_ende\' EXIT"',
    '"echo d"',
    '"exit 1"',
    '"echo e"',
])
DECKUNG_MODUL = "\n".join([          # python: an exit at MODULE level, before `fahre`
    '"import sys"',
    '"print(2)"',
    '"sys.exit(2)"',
    '"print(3)"',
    '"sys.exit(1)"',
    '"print(4)"',
    '"def main():"',
    '"    print(5)"',
    '"    return 1"',
    '"print(6)"',
    '"sys.exit(abschnitt.fahre(main))"',
])


def sprechprobe_deckung():
    """`[(what, ok)]` -- the per-place count must bite above a trap and hold below it."""
    def messe(vorlage, ist_shell):
        text = "\n".join(z.strip().strip('"').replace("\\'", "'")
                          for z in vorlage.splitlines())
        zeilen = text.splitlines()
        ab = deckung_ab(text, ist_shell)
        aus = [(nr, stelle_gedeckt(zeilen, nr, ist_shell, ab))
               for nr, wert, beendet, teil in schnitt_stellen(text, ist_shell)
               if beendet and wert == "1" and teil]
        return ab, aus
    ab_sh, sh = messe(DECKUNG_SPAET, True)
    ab_py, py = messe(DECKUNG_MODUL, False)
    return [
        ("die Falle wird an ihrer ZEILE gefunden, nicht irgendwo", ab_sh == 6),
        ("Schale: ein `exit 1` UEBER der Falle faellt auf -- und der darunter nicht",
         sh == [(4, False), (8, True)]),
        ("Python: ein Ausgang auf MODULEBENE ist ungedeckt, einer in `main` gedeckt",
         py == [(5, False), (9, True)]),
        ("das blosse WORT deckt nicht -- ohne Verdrahtung gibt es keine Zeile",
         deckung_ab("# ABGESCHNITTEN in: nirgends\nimport abschnitt\n", False) is None),
        ("und je DATEI gezaehlt saehe genau diese Probe GRUEN aus",
         all(bool(SAGT_WO.search("\n".join(z.strip().strip('\"')
                                           for z in v.splitlines())))
             for v in (DECKUNG_SPAET, DECKUNG_MODUL))),
    ]


def sprechprobe_sieb():
    """`[(what, ok)]` -- four directions, and only the last one gets through the sieve."""
    def zaehle(text):
        return [(w, b, t) for _, w, b, t in schnitt_stellen(text, False)]
    helfer = zaehle(SIEB_HELFER)
    zwei = zaehle(SIEB_ZWEI)
    rand = zaehle(SIEB_RAND)
    echt = zaehle(SIEB_ECHT)
    return [
        # It sits in the middle of the output and would therefore read as a partial
        # measurement -- the FIRST cut removes it, and only that one. Hence the `True`.
        ("ein `return 1` im HELFER beendet den Lauf nicht",
         helfer == [("1", False, True)]),
        ("ein Ausgang mit 2 ist ein ABBRUCH, kein halbes Urteil",
         zwei == [("2", True, True)]),
        ("ein Befund OHNE Ausgabe dahinter ist keine Teilmessung",
         rand == [("1", True, False)]),
        ("ein Befund mit Ausgabe auf BEIDEN Seiten ist eine",
         echt == [("1", True, True)]),
    ]


def main():
    (ok, f_gut, f_schlecht, f_gut_lc, f_prosa, f_zwei, a1, f_a2,
     s1, f_s2, stumm_ist_stumm, leer_faellt, voll_faellt) = sprechprobe()
    print("== Sprechprobe des Waechters ==")
    print(f"  saubere Quelle: {len(f_gut)} Verletzungen -- "
          + ("ok" if not f_gut else f"GESCHEITERT (falsches Rot: {f_gut})"))
    print(f"  kaputte Quelle: {len(f_schlecht)} Verletzungen -- "
          + ("ok" if len(f_schlecht) == 4 else f"GESCHEITERT (der Waechter ist stumm: {f_schlecht})"))
    print(f"  cc mit LC_ALL:  {len(f_gut_lc)} Verletzungen -- "
          + ("ok (die fuenfte verbietet nicht `cc`, sie fordert das Gebietsschema)"
             if not f_gut_lc else f"GESCHEITERT (falsches Rot: {f_gut_lc})"))
    print(f"  cc nur als Prosa: {len(f_prosa)} Verletzungen -- "
          + ("ok (der Name im Text ist keine Aufrufstelle)"
             if not f_prosa else f"GESCHEITERT (Fehlalarm: {f_prosa})"))
    print(f"  Abbruch mit 2:  {len(f_zwei)} Verletzungen -- "
          + ("ok (ein Ausgang mit 2 ist ROT -- die Forderung heisst `ungleich null`)"
             if not f_zwei else f"GESCHEITERT (falsches Rot: {f_zwei})"))
    print("  Absage mit 1:   " + ("ok (eine gedruckte Absage, die mit 1 endet, FAELLT)"
                                  if a1 else "GESCHEITERT -- sie kommt durch"))
    print(f"  Absage mit 2:   {len(f_a2)} Verletzungen -- "
          + ("ok (dieselbe Absage mit 2 kommt durch -- die Regel verbietet nicht das Wort)"
             if not f_a2 else f"GESCHEITERT (falsches Rot: {f_a2})"))
    print("  stumme Probe 1: " + ("ok (`if not sprechprobe(): exit 1` FAELLT, ohne ein Wort)"
                                  if s1 else "GESCHEITERT -- sie kommt durch"))
    print(f"  stumme Probe 2: {len(f_s2)} Verletzungen -- "
          + ("ok (dieselbe Stelle mit 2 kommt durch)"
             if not f_s2 else f"GESCHEITERT (falsches Rot: {f_s2})"))
    print("  und sie ist wirklich stumm: "
          + ("ok (die GEDRUCKTE Haelfte sieht sie nicht -- darum die zweite)"
             if stumm_ist_stumm else "GESCHEITERT -- die alte Haelfte faengt sie schon"))
    print("  Arbeitsmenge:   " + ("ok (eine Ausgabe ohne Zahl faellt, eine mit Zahl nicht)"
                                  if leer_faellt and voll_faellt else "GESCHEITERT"))
    schnitt_heil, schnitt_kaputt = sprechprobe_schnitt()
    print("  Schnitt:        " + ("ok (ein Ausgang am Ende ist kein Schnitt, einer mit "
                                  "Ausgabe dahinter schon)"
                                  if schnitt_heil and schnitt_kaputt else "GESCHEITERT"))
    ok = ok and schnitt_heil and schnitt_kaputt
    for was, sieb_ok in sprechprobe_sieb():
        print(f"  Sieb:           {'ok' if sieb_ok else 'GESCHEITERT'} -- {was}")
        ok = ok and sieb_ok
    for was, dk_ok in sprechprobe_deckung():
        print(f"  Deckung/Stelle: {'ok' if dk_ok else 'GESCHEITERT'} -- {was}")
        ok = ok and dk_ok
    for was, git_ok in sprechprobe_git():
        print(f"  git-Riegel:     {'ok' if git_ok else 'GESCHEITERT'} -- {was}")
        ok = ok and git_ok
    for was, au_ok in sprechprobe_auscheckung():
        print(f"  Auscheckung:    {'ok' if au_ok else 'GESCHEITERT'} -- {was}")
        ok = ok and au_ok
    # **`abschnitt.py` is not a guardian, so no collective run reaches it** -- and a tool
    # nobody drives is indistinguishable from one that does not exist. It is driven here,
    # because the honesty of every guarded cut rests on it.
    for was, ab_ok in _abschnitt.sprechprobe():
        print(f"  Abschnitt:      {'ok' if ab_ok else 'GESCHEITERT'} -- {was}")
        ok = ok and ab_ok
    for was, sch_ok in sprechprobe_schale():
        print(f"  Abschnitt (sh): {'ok' if sch_ok else 'GESCHEITERT'} -- {was}")
        ok = ok and sch_ok
    # **R14 fuer die EINZIGE Zeile in `GEGENSTAND`, die eine Zahl liest** (2026-09-02). Bis
    # heute stand die Zahl fest da, und der Katalog war um elf gewachsen. *Ein Leser ohne
    # Probe ist von einer festen Zahl nicht zu unterscheiden.*
    for was, kat_ok in sprechprobe_katalog():
        print(f"  Katalog:        {'ok' if kat_ok else 'GESCHEITERT'} -- {was}")
        ok = ok and kat_ok
    # **R14 fuer die Zaehlung der Ausserhalbstehenden** (2026-09-02). Sie ist die einzige
    # Stelle, an der dieser Waechter ueber seine EIGENE Besetzung urteilt -- und eine
    # Zaehlung, die niemanden findet, sieht aus wie eine, bei der es niemanden gibt.
    for was, bs_ok in sprechprobe_besetzung():
        print(f"  Besetzung:      {'ok' if bs_ok else 'GESCHEITERT'} -- {was}")
        ok = ok and bs_ok
    if not ok:
        # **2, not 1 -- and in this file the sentence carries twice.** The guardian over the
        # guardians demands a working speech test from all of them; one that fails its own
        # has measured nothing, and everything it prints below is about itself.
        print("\n! Der Waechter ueber den Waechtern misst nicht, was er behauptet. ABBRUCH.")
        return 2

    print()
    print("== Die STATISCHEN Forderungen, am Quelltext ==")
    befunde = []
    alle = waechter()
    for p in alle:
        fehlt = statisch(p)
        marke = "ok      " if not fehlt else "FEHLT   "
        zusatz = "" if not fehlt else "  " + ", ".join(fehlt)
        print(f"  {marke}{p.name:<28}{zusatz}")
        if fehlt:
            befunde.append((p.name, fehlt))

    print()
    # **The wording of this line is an INTERFACE PROMISE, not prose.**
    # `pruefe-zahlen.py` recomputes two figures in README and TODO against exactly this
    # pattern. The first draft of the sixth requirement dropped one word from it, and both
    # entries went SILENT -- not wrong, unrecomputable, which is worse. *A tool whose output
    # somebody reads has an interface, whether or not anyone calls it one.*
    print(f"== {len(alle) - len(befunde)} von {len(alle)} tragen die vier STATISCHEN ==")
    print("   Es sind seit dem 2026-08-31 FUENF: die sechste Forderung (eine Absage endet")
    print("   mit 2) steht in derselben Zahl. **Der Wortlaut `vier` bleibt, weil")
    print("   `pruefe-zahlen.py` diese Zeile woertlich nachrechnet** -- wer ihn aendert,")
    print("   macht zwei Kennzahlen stumm, statt sie falsch zu machen.")
    print("   Die ARBEITSMENGE neben dem Urteil (W17) -- steht in der Ausgabe")
    print("   und nicht im Quelltext. Sie wird in `--lauf` gemessen, sonst gar nicht.")

    # **The boundary of the sixth requirement, printed with its count instead of kept quiet.**
    # It holds for those whose return code `abnahme.py` reads as a VERDICT -- and since
    # 2026-08-31 that is everyone but the named exceptions. The number below is what is STILL
    # outside; on 2026-08-30 it was 18 tools and 46 places. *A tool nobody names is a tool
    # nobody moves*, and this one moved because it was named.
    ausserhalb = [(p.name, absage_mit_eins(p.read_text(encoding="utf-8", errors="replace")),
                   stumme_probe_mit_eins(p.read_text(encoding="utf-8", errors="replace")))
                  for p in alle if not p.name.startswith(TRAEGT_URTEIL)]
    n_gedruckt = sum(len(s) for _, s, _ in ausserhalb)
    n_stumm = sum(len(s) for _, _, s in ausserhalb)
    n_stellen = n_gedruckt + n_stumm
    print()
    print(f"== Die sechste Forderung gilt fuer {sum(1 for p in alle if p.name.startswith(TRAEGT_URTEIL))} "
          f"von {len(alle)}: die mit einem gelesenen URTEIL ==")
    print(f"   Ausserhalb stehen {len(ausserhalb)} Werkzeuge mit {n_stellen} Stellen "
          f"({n_gedruckt} gedruckt, {n_stumm} stumm).")
    print("   **Am 2026-08-30 waren es 18 Werkzeuge und 46 Stellen** -- die 18 `zaehle-*`,")
    print("   mit dem Satz *sie messen, sie bewachen nicht*. Die Grenze stand mit ihrer Zahl")
    print("   da, damit jemand sie verschieben KANN; am 2026-08-31 hat es jemand getan.")
    if OHNE_URTEIL:
        print(f"   Und {len(OHNE_URTEIL)} AUSGENOMMEN, mit Grund:")
        for name, grund in sorted(OHNE_URTEIL.items()):
            print(f"     {name}: {grund}")
    else:
        print("   `OHNE_URTEIL` steht LEER: keiner der 18 blieb mit Grund draussen.")
    if ABBRUCH_GEBUCHT:
        print(f"   Und {len(ABBRUCH_GEBUCHT)} GEBUCHT, mit Grund:")
        for name, grund in sorted(ABBRUCH_GEBUCHT.items()):
            print(f"     {name}: {grund}")

    # **UND WEN DAS MUSTER NICHT ERREICHT -- gezaehlt, nicht erraten** (2026-09-02).
    draussen = ausserhalb_der_besetzung()
    print()
    print(f"== Ausserhalb der Besetzung: {len(draussen)} von "
          f"{len(alle) + len(draussen)} Werkzeugen in `instrumente/` ==")
    print("   Die Besetzung oben ist ein NAMENSMUSTER, und jedes neue Verb erfindet ein")
    print("   neues Vorsilbenwort. Diese Zeile nennt, wen es kostet -- gemessen am")
    print("   2026-09-02: 0 von 57 INNERHALB trugen eine Verletzung, 3 von 6 ausserhalb.")
    offen_draussen = []
    for q in draussen:
        fehlt = statisch(q)
        grund = AUSSERHALB_GEBUCHT.get(q.name)
        if fehlt and not grund:
            offen_draussen.append((q.name, fehlt))
            print(f"     !! {q.name:<30} {', '.join(fehlt)}")
        elif fehlt:
            print(f"        {q.name:<30} {', '.join(fehlt)} -- GEBUCHT: {grund}")
        else:
            print(f"        {q.name:<30} traegt die vier ohnehin")
    if offen_draussen:
        befunde.append(("ausserhalb der Besetzung", offen_draussen))
        print("   Ein Werkzeug, das keine Liste erreicht, ist von einem fehlerfreien nicht")
        print("   zu unterscheiden -- es fehlt einfach. *Dieselbe Klasse wie ein toter")
        print("   Anker, eine Ebene ueber dem Urteil.*")
    print("   **`abnahme.py:besetzung()` traegt DIESELBE Form** -- auch dort ist die")
    print("   Besetzung ein Glob ueber `pruefe-*`, `mutiere-*`, `zaehle-*`. Hier steht sie")
    print("   nur benannt; sie zu weiten heisst, diese Werkzeuge auch zu FAHREN, und das")
    print("   ist eine Entscheidung ueber den Sammellauf und nicht ueber diesen Waechter.")

    # **The cut in the middle of the run -- the item the empty tree leaves open.**
    geschnitten = []
    for q in alle:
        a, d = schnitt(q.read_text(encoding="utf-8", errors="replace"))
        if a and d:
            geschnitten.append((q.name, len(a), len(d)))
    geschnitten.sort(key=lambda r: -r[1])
    n_aus = sum(a for _, a, _ in geschnitten)
    print()
    print(f"== Ein Abbruch MITTEN im Lauf: {len(geschnitten)} von {len(alle)} koennen ihn haben ==")
    print(f"   {n_aus} Ausgangsstellen liegen hinter dem jeweils ersten -- jede davon ist ein")
    print("   Lauf, der VOR der letzten Messung endet, mit einem Ruecklaufwert, der wie ein")
    print("   Befund aussieht. **Der leere Baum misst den ANFANG; das hier misst die Mitte.**")
    for name, a, d in geschnitten[:5]:
        print(f"     {name:<28} {a:>3} Ausgaenge, {d:>4} Druckstellen dahinter")
    print("   *Gemessen am 2026-08-31 an einem Fall mit Datum:* `pruefe-emission.sh` starb an")
    print("   `F06`s `N043` in der vierten Stufe, die Stufen 9 und 10 liefen nie, und dahinter")
    print("   standen zwei Befunde, die zwei Wochen niemand sah. **Kein `2`, kein Wort --")
    print("   ein `1`, das wie ein Stufenbefund aussah.**")
    print("   Und was diese Zahl NICHT sagt: dass einer dieser Ausgaenge falsch ist. Eine")
    print("   Sprechprobe am Dateianfang SOLL alles dahinter beenden. Sie ist die FLAECHE,")
    print("   keine Mangelliste -- sie verpflichtet, sie spricht nicht frei (W10).")

    # **And underneath it the sieve: the surface turns into a working list.**
    ges, beendend, befund, teil, gedeckt, offen = teilmessungen(alle)
    n_offen = sum(offen.values())
    print()
    print(f"== Davon eine TEILMESSUNG, die wie eine ganze aussieht: {teil} von {ges} ==")
    print(f"   {ges - beendend} beenden den Lauf gar nicht erst -- ein `return 1` im Helfer")
    print("   ist ein WERT, den der Aufrufer liest, und kein Ausgang.")
    print(f"   {beendend - befund} der uebrigen enden mit 2. Das ist ein ABBRUCH: der Waechter")
    print("   sagt *nichts gemessen*, und die Abnahme druckt ihn mit eigenem Wort. Dorthin")
    print("   kommt nur, wer etwas KAPUTT hat -- ein fehlendes Werkzeug, eine gefallene")
    print("   Probe, eine leere Grundgesamtheit.")
    print(f"   **{befund} enden mit 1, und die sind erreichbar, ohne dass etwas kaputt ist**:")
    print("   ein Befund ist eine Aussage ueber den BAUM, und der Baum darf einen Fehler")
    print(f"   haben. Von ihnen tragen {teil} Ausgabe auf BEIDEN Seiten -- davor eine halbe")
    print("   Messung, dahinter das, was nie lief. *Das ist die gefaehrliche Menge, und sie")
    print("   ist die kleine.*")
    print(f"   {gedeckt} davon sind gedeckt -- **je STELLE gezaehlt, nicht je Datei**: die")
    print("   Zeile liegt hinter der `EXIT`-Falle (Schale) oder in einem `def`, das `fahre()`")
    print("   umschliesst (Python). *Eine Falle auf halber Hoehe deckt nichts darueber, und")
    print("   das Wort `ABGESCHNITTEN` in der eigenen Beschreibung deckt gar nichts.*")
    print(f"   **{n_offen} bleiben offen, in {len(offen)} Dateien** (Ratsche "
          f"{MARKE_TEILMESSUNG}):")
    for name, n in sorted(offen.items(), key=lambda r: (-r[1], r[0]))[:8]:
        print(f"     {name:<28} {n:>3}")
    if len(offen) > 8:
        print(f"     ... und {len(offen) - 8} weitere mit je einer")
    # **And the family beside it: whoever reads `git` looks at the return code.**
    # Measured over EVERY tool in the directory, not merely over the cast --
    # `erzeuge-mutationen.py` writes into sources and stands in no collective run.
    werkzeuge = sorted(p for p in (W / "instrumente").iterdir()
                       if p.is_file() and p.suffix in (".py", ".sh") and p.name != "__init__.py")
    liest_git, ohne = [], {}
    for p in werkzeuge:
        t = p.read_text(encoding="utf-8", errors="replace")
        stellen = [nr for nr, z in enumerate(t.splitlines(), 1)
                   if GIT_AUFRUF.search(z) and not _fixtur(z)
                   and not z.lstrip().startswith("#") and not DRUCK_STELLE.search(z)]
        if not stellen:
            continue
        liest_git.append(p.name)
        offene = git_ohne_riegel(t)
        if offene:
            ohne[p.name] = offene
    print()
    print(f"== {len(liest_git)} von {len(werkzeuge)} Werkzeugen lesen `git` -- "
          f"{len(ohne)} ohne Blick auf den Ruecklaufwert ==")
    print("   Ohne Repository endet `git status` mit **128 und LEERER Ausgabe**. Wer nur")
    print("   `stdout` liest, liest das als *sauber* -- und `pruefe-luecken.py` hat danach")
    print("   IN QUELLEN GESCHRIEBEN, auf genau dem Rechner, auf den `SCHWER` ihn schickt.")
    print(f"   Es lesen: {', '.join(liest_git) if liest_git else '(keiner)'}")
    for name, nrs in sorted(ohne.items()):
        print(f"     !! {name:<28} Zeilen {nrs}")
        befunde.append((name, [f"GIT-OHNE-RIEGEL:{nrs}"]))
    if not ohne:
        print("   Die drei Zustaende stehen an EINER Stelle (`mutiere-pruefer.py:baumstand()`)")
        print("   und werden von dort GELESEN -- eine vierte Kopie faellt hier auf (W7).")

    if n_offen > MARKE_TEILMESSUNG:
        print(f"   !! RATSCHE: {n_offen} offene Teilmessungen, erlaubt {MARKE_TEILMESSUNG}.")
        befunde.append(("TEILMESSUNG", [f"{n_offen} > {MARKE_TEILMESSUNG}"]))
    elif n_offen < MARKE_TEILMESSUNG:
        print(f"   Die Ratsche steht auf {MARKE_TEILMESSUNG} und ist auf {n_offen} gefallen"
              " -- nachziehen.")

    if "--lauf" in sys.argv:
        print()
        print("== Und die leichten laufen wirklich, mit Frist -- und mit der vierten Forderung ==")
        nicht_gemessen = []
        gesamtzeit = [0.0]
        for p in alle:
            if p.name in SCHWER:
                print(f"  schwer  {p.name:<28}  {SCHWER[p.name]}")
                continue
            fehlt_korpus = korpus_fehlt(p.name)
            if fehlt_korpus:
                ort, was = fehlt_korpus
                print(f"  KORPUS FEHLT  {p.name:<22}  {was}")
                print(f"                {'':<22}  {ort}")
                nicht_gemessen.append(p.name)
                continue
            befehl = [str(p)] + [str(pathlib.Path(a).expanduser())
                                 if a.startswith("~") else a
                                 for a in ARGUMENTE.get(p.name, [])]
            try:
                t0 = time.monotonic()
                r = subprocess.run(befehl, cwd=W, capture_output=True, text=True, timeout=FRIST)
                dauer = time.monotonic() - t0
                arbeit = ARBEIT.search(r.stdout)
                marke = "Ende" if r.returncode in (0, 1) else "USAGE?"
                zusatz = "" if arbeit else "   !! OHNE ARBEITSMENGE"
                # **Die Zeit gehoert neben das Urteil, wie die Arbeitsmenge.** Wer eine
                # Ausnahme mit Kosten begruendet, muss die Kosten irgendwo ablesen koennen --
                # sonst wird die Begruendung so alt wie die „~25 min" oben.
                print(f"  {marke} {r.returncode:<2} {p.name:<28}{dauer:6.2f} s{zusatz}")
                gesamtzeit[0] += dauer
                # **Erfolg ohne Arbeit.** Ein gruener Lauf ohne eine Zahl daneben ist von
                # einem leeren nicht zu unterscheiden -- `isabelle build` waehlte nichts und
                # endete gruen, dasselbe Muster.
                if not arbeit:
                    befunde.append((p.name, ["OHNE-ARBEITSMENGE"]))
                # **Ein Ruecklaufwert ausserhalb {0,1} ist kein Befund, sondern ein
                # FEHLAUFRUF** -- das Werkzeug hat nichts gemessen und sieht doch rot aus.
                if r.returncode not in (0, 1):
                    befunde.append((p.name, [f"RUECKLAUFWERT-{r.returncode}"]))
            except subprocess.TimeoutExpired:
                print(f"  HAENGT  {p.name:<28}  Frist {FRIST} s ueberschritten")
                befunde.append((p.name, ["LAEUFT-NICHT-DURCH"]))
            except PermissionError:
                print(f"  NICHT AUSFUEHRBAR  {p.name} -- ein Waechter, den niemand starten kann")
                befunde.append((p.name, ["NICHT-AUSFUEHRBAR"]))

    if "--lauf" in sys.argv:
        ohne = [n for n, f in befunde if "OHNE-ARBEITSMENGE" in f]
        gelaufen = len(alle) - len(SCHWER) - len(nicht_gemessen)
        print()
        print(f"== {gelaufen - len(ohne)} von {gelaufen} gelaufenen nennen ihre ARBEITSMENGE ==")
        print("   Ein gruener Lauf ohne Zahl daneben ist von einem leeren nicht zu")
        print(f"   unterscheiden (W17). Die {len(SCHWER)} schweren sind hier NICHT gemessen,")
        print(f"   und {len(nicht_gemessen)} weitere nicht, weil ihr fremder Korpus fehlt:")
        print(f"   {', '.join(nicht_gemessen) if nicht_gemessen else '(keiner)'}")
        print("   **Das ist ein Loch mit einer Zahl, kein gruener Haken.** Ein Waechter,")
        print("   dessen Gegenstand nicht da ist, hat nichts gemessen -- und das steht hier,")
        print("   statt sich als roter Ruecklaufwert zu tarnen, den keiner lesen kann.")
        print()
        print(f"== {gesamtzeit[0]:.1f} s fuer {gelaufen} Waechter ==")
        print("   Die Zeit steht hier, weil die AUSNAHMEN mit Kosten begruendet werden. Eine")
        print("   Ausnahme, deren Grund niemand nachrechnet, ist dieselbe Klasse wie eine Zahl,")
        print("   die niemand nachrechnet -- nur teurer: sie schaltet eine ganze Messung ab.")
        print("   *Am 2026-08-20 stand `pruefe-emission.sh` mit ~25 min auf dieser Liste und")
        print("   braucht 13,7 s; die Schaetzung stammte von dem Vormittag, an dem er HING.*")

    print()
    print("== Und was das NICHT heisst ==")
    print("  Die statische Haelfte liest QUELLTEXT. Dass ein `timeout` im Text steht, heisst")
    print("  nicht, dass es an der richtigen Stelle steht -- `pruefe-emission.sh` hatte am")
    print("  2026-08-20 eine Frist und beendete sich damit STILL, weil `set -e` auf den")
    print("  Ruecklaufwert 124 traf. **Die Frist war da, die Forderung nicht erfuellt.**")
    print(f"  {len(SCHWER)} Waechter sind zu schwer fuer den Lauf hier und stehen mit Grund")
    print("  daneben; ihre Frist ist damit nur statisch geprueft.")
    # **From here on nothing more is measured** -- everything above has run, and both the
    # green end and the red one are complete.
    _abschnitt.fertig()
    return 1 if befunde else 0


# **AND THE GUARD OVER THE GUARDS ANNOUNCES ITS OWN CUT** -- since 2026-08-31.
# It counted 92 covered places and was not among them, because its own dangerous set is
# empty today. *That is a reason to be exempt from the FINDING, never from the FORM* -- a
# crash halfway through this file would have cut every measurement below it and said
# nothing, and the reader would have had the sections above and no hint that the rest was
# missing. Same class, applied to the tool that names the class.
if __name__ == "__main__":
    sys.exit(_abschnitt.fahre(main))
