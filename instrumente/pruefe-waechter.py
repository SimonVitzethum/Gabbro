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
import pathlib
import re
import subprocess
import sys
import time

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
# **Und `../caprock-messbasis` ist zusaetzlich relativ**: in einem `git worktree` zeigt der
# Pfad neben den Arbeitsbaum statt neben die Hauptauscheckung. Auch dort fehlt er also --
# lautlos, bis dieser Eintrag es sagt.
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
}


def korpus_fehlt(name):
    """Der fremde Baum dieses Waechters -- oder `None`, wenn er keinen braucht/hat.

    Gibt `(pfad, was)` zurueck, wenn der Baum DEKLARIERT ist und FEHLT.
    """
    eintrag = FREMDER_KORPUS.get(name)
    if not eintrag:
        return None
    pfad, was = eintrag
    ort = pathlib.Path(pfad).expanduser()
    if not ort.is_absolute():
        ort = (W / pfad).resolve()
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


def waechter():
    aus = []
    # **`abnahme.py` joined on 2026-08-30, and it very nearly did not.** The collective run is
    # not called `pruefe-*` and would have slipped through every mesh above -- a tool that
    # establishes the reach of acceptance while standing outside acceptance itself. *Exactly
    # what it was built against, one level up.*
    for p in sorted(W.glob("instrumente/pruefe-*.py")) + sorted(W.glob("instrumente/pruefe-*.sh")) \
            + sorted(W.glob("instrumente/zaehle-*.py")) + sorted(W.glob("instrumente/zaehle-*.sh")) \
            + sorted(W.glob("instrumente/mutiere-*.py")) + sorted(W.glob("instrumente/abnahme.py")):
        aus.append(p)
    return aus


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
    return 1 if befunde else 0


if __name__ == "__main__":
    sys.exit(main())
