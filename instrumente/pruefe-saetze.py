#!/usr/bin/env python3
"""**Der zweite Zahn des Passregisters: kein neuer Absagecode ohne seinen Satz.**

    ./instrumente/pruefe-saetze.py [--je-satz] [--ohne-satz]

WARUM DIESER ZAHN SOFORT KOMMT UND NICHT NACH DEN SAETZEN
---------------------------------------------------------
**Jede Kennung, die zwischen heute und dem Beweisprojekt dazukommt, ist ein Satz mehr, den
spaeter jemand RUECKWAERTS rekonstruieren muss** -- aus einem Absagetext auf die Aussage
zurueckschliessen, die der Pass eigentlich haelt. *An einem einzigen Arbeitstag sind drei
Kennungen dazugekommen.* Eine Ratsche kostet nichts, solange sie frueh steht.

Dieselbe Bauart wie `pruefe-schablonen.py`, an einem anderen Gegenstand: dort die Praemissen
bewiesener Schablonen ohne Pass, hier die Kennungen ohne Satz.

DIE ZWEI RICHTUNGEN, UND DIE ZWEITE IST DIE SCHAERFERE
-------------------------------------------------------
    (a) Kennung im Pruefer, kein Satz     die RATSCHE -- sie darf fallen, nicht steigen
    (b) Kennung im Satz, nicht im Pruefer ein Satz ueber einer Regel, die es nicht gibt

**(b) ist immer rot, ohne Marke.** Bei (a) weiss man wenigstens, dass die Regel existiert;
bei (b) steht ein Satz da und beschreibt nichts. *Das ist woertlich die Klasse, gegen die
`pruefe-schablonen.py` steht -- ein Beweis, dessen Voraussetzung niemand herstellt.*

WAS DIE ZAHL NICHT SAGT
-----------------------
**Ein aufgeschriebener Satz ist kein bewiesener.** Dieser Waechter zaehlt, ob eine Kennung
einem Satz ZUGEORDNET ist -- er liest den Satz nicht und prueft ihn nicht. Ein Satz, der
falsch ist, zaehlt hier genauso wie ein richtiger. *Derselbe Vorbehalt wie bei den Adressen
in `pruefe-schablonen.py`: das Werkzeug zaehlt Zuordnungen, es prueft sie nicht* (W10).

**Und `gabbro paesse` fuehrt den Stand daneben:** `CONJECTURED` gegen `measured` gegen
`PROVED`. Heute ist die dritte Spalte leer, und das ist die Zahl, um die es in PL.2 geht.
"""
import collections
import pathlib
import re
import subprocess
import sys

W = pathlib.Path(__file__).resolve().parent.parent
BIN = W / "target" / "debug" / "gabbro"
FRIST = 60

# **Die gebuchte Marke.** Eine Ratsche, keine Zielzahl: sie darf fallen, nicht steigen.
#
# 2026-08-21, beim Anlegen des Registers: **45**. Das sind genau die Kennungen, die zu keinem
# Pass der `passliste()` gehoeren -- `parse.rs` (37), `lex.rs` (7), `emit.rs` (1). Sie sind
# nicht vergessen, sondern **strukturell ausserhalb**: der Parser ist kein Pruefpass, und der
# Erzeuger auch nicht.
#
# *Trotzdem stehen sie als offen und nicht als wegdefiniert.* Ein Absagetext des Parsers
# behauptet genauso etwas ueber ein Programm wie einer des Kostenpasses, und wer die Zahl auf
# null bringen will, schreibt die 45 Saetze -- oder das Register bekommt eine zweite Spalte
# fuer „kein Pass". **Was NICHT geht, ist die Zahl kleiner zu machen, indem man die Frage
# aendert.**
MARKE = 45

KENNUNG = re.compile(r'"([A-Z][0-9]{3})"')
CODES_ZEILE = re.compile(r"^--\s+codes: (.+)$")


def erhebe_kennungen(wurzel=None):
    """Kennung -> Menge der Dateien, die sie vergeben. Wie `pruefe-kennungen.py`."""
    wurzel = wurzel or W
    karte = collections.defaultdict(set)
    for q in sorted((wurzel / "crates").rglob("*.rs")):
        if "/tests/" in str(q):
            continue          # Tests NENNEN Kennungen, sie vergeben keine
        # **`saetze.rs` NENNT jede Kennung, es vergibt keine** -- dieselbe Klasse wie
        # `tests/`, und ohne diese Zeile misst der Waechter sich selbst: eine erfundene
        # Kennung in einem Satz faende sich in `saetze.rs` wieder und gaelte als vorhanden.
        # *Genau daran ist die Sprechprobe (3) beim ersten Lauf von aussen gescheitert.*
        if q.name == "saetze.rs":
            continue
        for m in KENNUNG.finditer(q.read_text(encoding="utf-8", errors="replace")):
            karte[m.group(1)].add(q.name)
    return karte


def lies_register(text):
    """Die Kennungen, die das Register beansprucht, und die gemeldete Satzzahl."""
    beansprucht = set()
    for z in text.splitlines():
        m = CODES_ZEILE.match(z)
        if not m:
            continue
        roh = m.group(1).strip()
        if roh.startswith("NONE"):
            continue
        beansprucht.update(re.findall(r"[A-Z][0-9]{3}", roh))
    gemeldet = None
    g = re.search(r"SENTENCES: (\d+) over", text)
    if g:
        gemeldet = int(g.group(1))
    return beansprucht, gemeldet


def urteile(vorhanden, beansprucht):
    """(ohne Satz, erfunden) -- die beiden Richtungen."""
    ohne = sorted(set(vorhanden) - beansprucht)
    erfunden = sorted(beansprucht - set(vorhanden))
    return ohne, erfunden


def lauf(*args):
    if not BIN.is_file():
        print(f"ABBRUCH: {BIN} fehlt -- gebaut wird auf ki-pc-fisch-101 (CLAUDE.md).",
              file=sys.stderr)
        sys.exit(2)
    try:
        return subprocess.run([str(BIN), *args], cwd=W, capture_output=True,
                              text=True, timeout=FRIST)
    except subprocess.TimeoutExpired:
        print(f"ABBRUCH: `gabbro {' '.join(args)}` ueberschritt {FRIST} s -- "
              "es wurde NICHTS gemessen.", file=sys.stderr)
        sys.exit(2)


# **Die Sprechprobe, in beide Richtungen -- an der LOGIK dieses Waechters.** Das Register ist
# statische Rust-Tafel; eine Probe von aussen kann nichts hineinschieben. Also wird die
# Auswertung selbst gefuettert. *Ein Waechter, der nur die eigenen Dateien liest, misst, wie
# gut sie zu ihm passen.*
GIFT_REGISTER = """-- Namen
--   [measured] probe.eins
--     codes: X001 X002
--   [CONJECTURED] probe.zwei
--     codes: NONE -- this rule widens what passes, or is not built
--   SENTENCES: 2 over 1 passes -- 1 measured, 1 CONJECTURED, 0 proved.
"""


def sprechprobe():
    beansprucht, gemeldet = lies_register(GIFT_REGISTER)
    if beansprucht != {"X001", "X002"} or gemeldet != 2:
        return False, "die Auswertung liest das Registerformat nicht mehr"

    # (1) Eine ERFUNDENE Kennung ohne Satz MUSS auffallen.
    ohne, erfunden = urteile(["X001", "X002", "X999"], beansprucht)
    if ohne != ["X999"] or erfunden:
        return False, "eine Kennung ohne Satz faellt NICHT auf"

    # (2) Der saubere Stand darf NICHT auffallen.
    ohne, erfunden = urteile(["X001", "X002"], beansprucht)
    if ohne or erfunden:
        return False, "ein vollstaendig belegter Stand wird beanstandet"

    # (3) Die zweite Richtung: ein Satz ueber einer Regel, die es nicht gibt.
    ohne, erfunden = urteile(["X001"], beansprucht)
    if erfunden != ["X002"]:
        return False, "eine erfundene Kennung im Satz faellt NICHT auf"

    # (4) `NONE` ist keine Kennung -- sonst zaehlte das Wort als Regel.
    if "NONE" in beansprucht:
        return False, "`NONE` wird als Kennung gelesen"
    return True, None


def main():
    ok, warum = sprechprobe()
    print("== Sprechprobe: ", end="")
    if not ok:
        print("GESCHEITERT ==")
        print(f"SPRECHPROBE GESCHEITERT: {warum}.", file=sys.stderr)
        print("  Ein Waechter, der seine eigene Logik nicht besteht, misst NICHTS.",
              file=sys.stderr)
        return 2
    print("ok (ohne Satz faellt auf, belegt geht durch, erfunden faellt auf) ==\n")

    r = lauf("paesse", "--je-satz")
    if r.returncode != 0 or "THE PASS REGISTER" not in r.stdout:
        print("ABBRUCH: `gabbro paesse` lief nicht -- das ist KEINE Zaehlung von null.",
              file=sys.stderr)
        return 2
    beansprucht, saetze = lies_register(r.stdout)
    if saetze is None:
        print("ABBRUCH: das Register meldet keine Satzzahl -- die Auswertung dieses "
              "Waechters passt nicht mehr zur Ausgabe.", file=sys.stderr)
        return 2

    karte = erhebe_kennungen()
    vorhanden = sorted(karte)
    ohne, erfunden = urteile(vorhanden, beansprucht)

    print(f"== Zahn 2: {len(ohne)} von {len(vorhanden)} Kennungen ohne Satz ==")
    print(f"   {saetze} Saetze beanspruchen {len(beansprucht)} Kennungen.")
    print(f"   Marke {MARKE} -- eine Ratsche, keine Zielzahl: sie darf fallen, nicht steigen.")
    print()

    if "--je-satz" in sys.argv:
        print(r.stdout)
    if "--ohne-satz" in sys.argv or "--je-satz" in sys.argv:
        je_datei = collections.defaultdict(list)
        for k in ohne:
            for d in karte[k]:
                je_datei[d].append(k)
        for d in sorted(je_datei):
            print(f"   {d}: {' '.join(sorted(je_datei[d]))}")
        print()

    schlecht = 0
    if len(ohne) > MARKE:
        print(f"FUND: {len(ohne)} Kennungen ohne Satz, gebucht sind {MARKE} -- "
              "die Ratsche laeuft nur nach unten.", file=sys.stderr)
        schlecht += 1
    elif len(ohne) < MARKE:
        print(f"FUND: nur noch {len(ohne)} statt {MARKE} -- die Marke gehoert nachgezogen "
              "(das ist der gute Fall, und er ist trotzdem ein Befund).", file=sys.stderr)
        schlecht += 1
    for k in erfunden:
        print(f"FUND: `{k}` steht in einem Satz und wird von KEINER Datei vergeben -- "
              "ein Satz ueber einer Regel, die es nicht gibt.", file=sys.stderr)
        schlecht += 1

    print("== Und was das NICHT heisst ==")
    print("  Dieser Waechter zaehlt ZUORDNUNGEN, er prueft sie nicht. Ein falscher Satz")
    print("  zaehlt hier wie ein richtiger, und ein Satz, der weniger sagt als sein Pass")
    print("  leistet, faellt gar nicht auf. **Ein aufgeschriebener Satz ist kein")
    print("  bewiesener** -- `gabbro paesse` fuehrt den Stand daneben, und die Spalte")
    print("  `PROVED` ist heute leer (W10).")
    print()
    print(f"== Arbeitsmenge: {len(vorhanden)} Kennungen, {saetze} Saetze, {len(ohne)} ohne "
          f"Satz, {len(erfunden)} erfunden, 1 Werkzeuglauf, 4 Proben ==")
    return 1 if schlecht else 0


if __name__ == "__main__":
    sys.exit(main())
