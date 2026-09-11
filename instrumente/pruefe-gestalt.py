#!/usr/bin/env python3
"""**Der Gestaltwaechter -- Saetze gegen Definitionen, je Datei.**

Am 2026-09-10 mass der Ordner `grammatik/Grammatik`: 23 Dateien, 372
`theorem`, 569 `def`-Formen -- und stellte fest, dass mehrere Dateien
ausdruecklich Gestalt sind und es auch sagen, die Dokumente darueber aber
Zahlen zitieren, die niemand nachrechnet (`ABSENKUNG-ZAEHLUNG.md` fuehrte
noch ` proPrimitiv <= 8` waehrend `Ziel.lean` laengst `<= 18` traegt).
*Zwei Register ueber einer Zahl, die aelteste Fehlerklasse des Ordners.*

Dieser Waechter zaehlt je Datei die Saetze (`theorem`/`lemma`) und Beispiele
(`example`) gegen die Definitionen (`def`/`abbrev`/`structure`/`inductive`/
`class`) und ratscht beide: jede Bewegung braucht einen Commit, der die
Tabelle unten mitbewegt. Was die Tabelle nicht erklaert, ist keine Messung.

**Zaehlt, was der Befehl zaehlt:** ein Konstrukt gilt, wenn es in Spalte 0
beginnt (`^theorem `, nicht eingerueckt); Kommentare (`--`, `/- -/`
geschachtelt) zaehlen nicht mit. Dieselbe Methode, mit der die 372/569
gemessen wurden -- ein Muster, das anders zaehlt als seine Quelle, misst
seine eigene Lesart (W16).
"""

import os
import re
import signal
import sys
import tempfile
from pathlib import Path

# **Vier statische Forderungen, wie jedes Instrument.** Pinned locale first:
# Fremdwerkzeuge melden in der Sprache des Benutzers, und ein `grep` auf den
# englischen Wortlaut trifft dann nichts.
os.environ.setdefault("LC_ALL", "C")

# **Frist, deklariert.** Reines Textzaehlen braucht sie nicht -- sie steht,
# damit ein Haenger, den es nicht geben kann, trotzdem keinen Zustand wuerde.
FRIST = 300

W = Path(__file__).resolve().parent.parent
GEGENSTAND = W / "grammatik" / "Grammatik"

# **Die Ratsche: je Datei (Saetze, Beispiele, Definitionen), gemessen am
# 2026-09-11 auf dem vereinten Baum (Bahn 100 eingeschlossen).** Eine Zeile
# bewegt sich nur mit einem Commit, der sie hier mitbewegt und den Grund
# daneben schreibt -- eine Marke, die man hochzieht, weil sie klemmt, ist
# keine (Rattenfaenger 2026-08-28: MARKE_EINGEFROREN blieb bei 31).
ERWARTET = {
    "Adressraum.lean": (11, 0, 36),
    "Budget.lean": (19, 0, 18),
    "Erhaltung.lean": (23, 15, 48),
    "Extraktion.lean": (51, 6, 68),
    "Fehler.lean": (48, 0, 25),
    "Fristlauf.lean": (12, 7, 9),  # p16: +1 theorem (hardware-exhaustive expiry link) +1 example (eval pin)
    "Geraet.lean": (10, 0, 20),
    "Geteilt.lean": (19, 2, 26),
    "InterferenzAllgemein.lean": (13, 0, 25),
    "Interferenz.lean": (9, 0, 4),
    "Koernung.lean": (10, 0, 4),
    "Komposition.lean": (0, 0, 37),
    "Marken.lean": (8, 0, 18),
    "Satz.lean": (105, 7, 25),
    "Semantik.lean": (2, 0, 65),
    "Syntax.lean": (0, 0, 45),
    "Terminierung.lean": (14, 2, 2),
    "Typen.lean": (12, 0, 27),
    "Unterbrechung.lean": (5, 0, 3),
    "Wettlauf.lean": (22, 0, 16),
    "Zeugnis.lean": (6, 41, 24),
    "Ziel.lean": (9, 0, 4),
    "Zucker.lean": (1, 2, 37),
}

ZEILEN_SATZ = re.compile(r"^(theorem|lemma) ")
ZEILEN_BEISPIEL = re.compile(r"^example ")
ZEILEN_DEF = re.compile(r"^(def|abbrev|structure|inductive|class) ")


def ohne_kommentare(text):
    """Zeilen- (`--`) und geschachtelte Blockkommentare (`/- -/`) entfernen.

    Was in einem Kommentar steht, ist kein Konstrukt: `-- theorem spaet`
    und ein `theorem` im Blockkommentar duerfen nicht mitzaehlen -- sonst
    zaehlt eine auskommentierte Zeile als Satz (W16: das Werkzeug misst
    seine eigene Lesart).
    """
    out = []
    i, n, tiefe = 0, len(text), 0
    while i < n:
        if tiefe == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
        elif text.startswith("/-", i):
            tiefe += 1
            i += 2
        elif tiefe > 0 and text.startswith("-/", i):
            tiefe -= 1
            i += 2
        elif tiefe == 0:
            out.append(text[i])
            i += 1
        else:
            i += 1
    return "".join(out)


def zaehle(pfad):
    """(Saetze, Beispiele, Definitionen) einer Datei, nach obiger Methode."""
    code = ohne_kommentare(pfad.read_text(encoding="utf-8"))
    saetze = beispiele = definitionen = 0
    for zeile in code.split("\n"):
        if ZEILEN_SATZ.match(zeile):
            saetze += 1
        elif ZEILEN_BEISPIEL.match(zeile):
            beispiele += 1
        elif ZEILEN_DEF.match(zeile):
            definitionen += 1
    return saetze, beispiele, definitionen


def pruefe(gegenstand):
    """Liste der Befunde; leer heisst: jede Datei steht auf ihrer Zeile."""
    befunde = []
    dateien = sorted(gegenstand.glob("*.lean"))
    for pfad in dateien:
        name = pfad.name
        if name not in ERWARTET:
            befunde.append(f"{name}: keine Zeile in der Ratsche -- neu, "
                           f"nicht gebucht")
            continue
        ist = zaehle(pfad)
        soll = ERWARTET[name]
        if ist != soll:
            befunde.append(f"{name}: steht als {soll}, gemessen {ist}")
    for name in ERWARTET:
        if not (gegenstand / name).is_file():
            befunde.append(f"{name}: Zeile ohne Datei -- entfernt, nicht Ausfall")
    return befunde, len(dateien)


def sprechprobe():
    """Sprechprobe in BEIDE Richtungen: was stimmt, besteht; was verstellt
    ist, faellt. Laeuft auf Wegwerf-Dateien im eigenen Kratzverzeichnis --
    nie im Baum (`CLAUDE.md`: fremde Dateien im Messverzeichnis verderben
    den Lauf, der sie liest)."""
    with tempfile.TemporaryDirectory(prefix="gestaltprobe-") as d:
        ort = Path(d)
        sauber = (
            "-- theorem spaet -- zaehlt nicht, Kommentar\n"
            "/- theorem tief -/\n"
            "/- aussen /- theorem tief2 -/ noch aussen -/\n"
            "theorem echt_a : True := trivial\n"
            "  theorem eingerueckt : True := trivial\n"
            "def d_a : Nat := 1\n"
            "abbrev A := Nat\n"
            "structure S where\n"
            "  x : Nat\n"
            "inductive I | a | b\n"
            "example e_a : True := trivial\n"
        )
        (ort / "sauber.lean").write_text(sauber, encoding="utf-8")
        if zaehle(ort / "sauber.lean") != (1, 1, 4):
            return False, "saubere Vorlage falsch gelesen"
        (ort / "verstellt.lean").write_text(sauber + "theorem spaet : True := trivial\n",
                                            encoding="utf-8")
        # Die verstellte Datei MUSS von der Ratsche abweichen: ein Eintrag
        # mit (1, 1, 4) daneben faellt auf (1, 1, 4) gegen (2, 1, 4).
        if zaehle(ort / "verstellt.lean") == (1, 1, 4):
            return False, "verstellte Datei kam durch"
    return True, ""


def main():
    signal.alarm(FRIST)
    ok, grund = sprechprobe()
    if not ok:
        print(f"ABBRUCH: Sprechprobe versagt ({grund}) -- NICHTS gemessen.")
        print("  Ein Waechter, der seine eigene Probe nicht besteht, misst")
        print("  einen Defekt an sich selbst, keinen am Gegenstand (R14).")
        return 2
    print("== Sprechprobe des Waechters ==")
    print("  saubere Vorlage gelesen, verstellte erkannt -- ok")
    if not GEGENSTAND.is_dir():
        print(f"ABBRUCH: {GEGENSTAND} fehlt -- NICHTS gemessen.")
        print("  Ueber einem fehlenden Gegenstand ist jede Zahl null, und null")
        print("  saehe aus wie ein sauberer Baum (W17).")
        return 2
    befunde, n = pruefe(GEGENSTAND)
    t = e = d = 0
    for name in sorted(ERWARTET):
        p = GEGENSTAND / name
        if p.is_file():
            st, be, de = zaehle(p)
            t, e, d = t + st, e + be, d + de
    # **Die Arbeitsmenge neben dem Urteil** (W17): ein Lauf, der null faehrt,
    # ist rot statt gruen.
    print(f"== Gestalt: {n} Dateien, {t} Saetze, {e} Beispiele, {d} Definitionen ==")
    if n == 0:
        print("ABBRUCH: keine Datei gezaehlt -- das ist kein sauberer Baum.")
        return 2
    if befunde:
        for b in befunde:
            print(f"  BEFUND  {b}")
        print("== GESTALT: ROT -- der Baum ist neben seiner Ratsche ==")
        return 1
    print("== GESTALT: GRUEN -- jede Datei steht auf ihrer Zeile ==")
    return 0


if __name__ == "__main__":
    sys.exit(main())
