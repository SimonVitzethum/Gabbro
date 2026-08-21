#!/usr/bin/env python3
"""**Eine Kennung, eine REGEL -- und `pruefe-kennungen.py` misst nur „eine Kennung, eine
Datei".**

Am 2026-08-21 wurde `M120` zweimal vergeben: fuer `Self` im `ensures` (Stufe 6) und fuer einen
Grundwert (Stufe 7). **Beide in `m1.rs`** -- und damit war der Kennungswaechter blind, denn
seine Regel lautet *„eine Kennung darf in beliebig vielen ZEILEN stehen, aber nur in EINER
Datei"*.

    Die Datei war eine NAEHERUNG an die Regel, und sie war richtig, solange Dateien und
    Regeln eins zu eins standen.

**Das ist dieselbe Vergroeberung wie bei W16 -- nur nicht in der Tiefe, sondern in der
AUFLOESUNG.** Ein Werkzeug, das auf Dateiebene aufloest, kann zwei Regeln in einer Datei nicht
unterscheiden; es meldet nichts und sieht aus, als haette es nachgesehen.

## Warum die naheliegende Verschaerfung nicht geht

*„Zaehle, wie oft ein Literal als Kennung emittiert wird, und alles ueber eins ist ein
Befund."* Gemessen am selben Tag: **227 Vergabestellen auf 193 Kennungen; 32 Kennungen haben
mehr als eine.** Achtzehn davon geben dieselbe Regel aus mehreren Zweigen aus
(`erwarte_z`/`erwarte_kw` melden beide `P001`). **Die Regel waere in die andere Richtung zu
grob und haette 32 Befunde gemeldet, von denen die meisten keine sind.**

## Was stattdessen aufloest: der MELDUNGSTEXT

Eine Regel ist, was sie SAGT. Zwei Vergabestellen derselben Regel teilen ihr Textgeruest
(*„`{}` leaves the range"* / *„`{}` leaves the width"*); zwei verschiedene Regeln teilen
nichts (*„`{}` is not a declared `reason`"* gegen *„`Self` in `ensures` names no carrier"*).

**Dieses Werkzeug faellt kein Urteil, es stellt eine Kandidatenliste auf** -- und die Richtung
seines Fehlers steht daneben:

  * **falsch positiv:** eine Regel, die an zwei Stellen verschieden formuliert ist, sieht aus
    wie zwei Regeln;
  * **falsch negativ (W10):** zwei Regeln, die aehnlich klingen, kommen durch. *Nicht
    abgewiesen ist nicht bestaetigt.*

## Und die teurere Haelfte: was eine Doppelvergabe RUECKWIRKEND kostet

Die Giftproben pruefen auf **Kennungen** (`-- erwartet: CODE`). Eine doppelt vergebene Kennung
macht jede Probe darauf **mehrdeutig**: sie faellt gruen, waehrend die gemeinte Regel
ausgefallen sein kann. *Ein Duplikat entwertet damit rueckwirkend die Deckungsaussage aller
Proben, die darauf zeigen* -- und deshalb zaehlt dieses Werkzeug sie mit.

    ./instrumente/pruefe-vergabe.py            prueft
    ./instrumente/pruefe-vergabe.py --liste    die Kandidaten einzeln, mit ihren Texten
"""
import collections
import difflib
import pathlib
import re
import sys

W = pathlib.Path(__file__).resolve().parent.parent
FRIST = 120  # Sekunden. Dieses Werkzeug fuehrt nichts aus, die Frist gilt dem Gesamtlauf.

# **Die Vergabestelle ist die Kennung im ABSAGEKONSTRUKTOR**, nicht jede Erwaehnung. Eine
# Notiz, ein Kommentar oder ein Register NENNT eine Kennung; vergeben wird sie hier.
VERGABE = re.compile(
    r'Absage::(?:fehler|hinweis|warnung)\s*\(\s*"([A-Z][0-9]{3})"\s*,(.{0,600})', re.S)

# **`saetze.rs` NENNT jede Kennung, die ein Pass ausgibt** -- es vergibt keine. Dieselbe Zeile
# steht in `pruefe-kennungen.py` und in `pruefe-gruende.py`, und in beiden hat ihr Fehlen an
# einem Tag eine Zahl verschoben. *Wer Quellen nach `"XNNN"` durchsucht, misst Nennungen.*
NICHT = {"saetze.rs"}

# **Die Marke ist eine Ratsche, keine Zielzahl.** Sie darf fallen, nicht steigen -- und sie
# steht auf dem gemessenen Stand vom 2026-08-21, nicht auf einer Wunschzahl.
MARKE = 14
# Ebenso fuer die Proben, deren Kennung heute mehrdeutig ist.
MARKE_PROBEN = 39

SCHWELLE = 0.45  # Textaehnlichkeit, unter der zwei Vergabestellen als verschieden gelten.


def botschaft(roh):
    """Der Meldungstext einer Vergabestelle -- Formatzeichenketten ohne Platzhalter."""
    teile = re.findall(r'"((?:[^"\\]|\\.)*)"', roh)
    txt = re.sub(r"\{[^}]*\}", " ", " ".join(teile))
    return " ".join(re.sub(r"\\\s*", " ", txt).split()).lower()[:120]


def erhebe(zusatz=None):
    """Kennung -> Liste von (Datei, Zeile, Meldungstext)."""
    stellen = collections.defaultdict(list)
    for q in sorted(W.glob("crates/*/src/*.rs")):
        if q.name in NICHT:
            continue
        t = q.read_text(encoding="utf-8", errors="replace")
        if zusatz and q.name == zusatz[0]:
            t += zusatz[1]
        for m in VERGABE.finditer(t):
            stellen[m.group(1)].append(
                (q.name, t[: m.start()].count("\n") + 1, botschaft(m.group(2))))
    return stellen


def kandidaten(stellen):
    """Kennungen, deren Vergabestellen UNAEHNLICH melden -- Kandidaten, kein Urteil."""
    aus = {}
    for k, v in stellen.items():
        if len(v) < 2:
            continue
        texte = [b for _, _, b in v]
        mn = min(difflib.SequenceMatcher(None, a, b).ratio()
                 for i, a in enumerate(texte) for b in texte[i + 1:])
        if mn < SCHWELLE:
            aus[k] = (mn, v)
    return aus


def proben():
    """Giftprobe -> erwartete Kennung."""
    aus = {}
    for g in sorted(W.glob("beispiele/gift/*.gab")):
        m = re.search(r"--\s*erwartet:\s*([A-Z][0-9]{3})", g.read_text(encoding="utf-8"))
        if m:
            aus[g.name] = m.group(1)
    return aus


def sprechprobe():
    """In BEIDE Richtungen -- und die Giftrichtung REKONSTRUIERT den echten Fall.

    *Eine Probe, die sich einen Fall ausdenkt, misst ihre eigene Phantasie.* Diese hier
    stellt `M120` wieder her, wie es am 2026-08-21 wirklich dastand: zwei Vergabestellen in
    EINER Datei, mit unverwandten Meldungen.
    """
    echt = kandidaten(erhebe())
    gift = kandidaten(erhebe(zusatz=(
        "m1.rs",
        '\nAbsage::fehler("M126", s, format!("`{}` is not a declared `reason`", x));\n')))
    a = "M126" not in echt
    b = "M126" in gift
    print("== Sprechprobe, in beide Richtungen ==")
    print(f"  rekonstruiert: {'ok (die alte M120-Doppelvergabe faellt auf)' if b else 'GESCHEITERT -- der Waechter sieht sie nicht'}")
    print(f"  heutiger Stand: {'ok (M126 gilt nicht als doppelt)' if a else 'GESCHEITERT -- falsches Rot'}")
    return a and b


def main():
    if not sprechprobe():
        return 1
    stellen = erhebe()
    n_stellen = sum(len(v) for v in stellen.values())
    mehrfach = {k: v for k, v in stellen.items() if len(v) > 1}
    kand = kandidaten(stellen)

    print(f"\n== Vergabestellen: {n_stellen} auf {len(stellen)} Kennungen ==")
    print(f"   {len(mehrfach)} Kennungen haben mehr als eine Vergabestelle.")
    print(f"   Davon melden {len(kand)} UNAEHNLICH -- Kandidaten fuer zwei Regeln")
    print(f"   unter einer Kennung.  Marke {MARKE}: sie darf fallen, nicht steigen.")

    p = proben()
    betroffen = {g: c for g, c in p.items() if c in kand}
    print(f"\n== Was das RUECKWIRKEND kostet: {len(betroffen)} von {len(p)} Giftproben ==")
    print("   Eine Probe auf eine mehrdeutige Kennung faellt gruen, auch wenn die GEMEINTE")
    print("   Regel ausgefallen ist. *Ihre Deckungsaussage ist damit keine.*")
    print(f"   Marke {MARKE_PROBEN}.")

    if "--liste" in sys.argv:
        print("\n== Die Kandidaten einzeln ==")
        for k, (mn, v) in sorted(kand.items(), key=lambda x: x[1][0]):
            pr = [g for g, c in p.items() if c == k]
            print(f"\n  {k}  Aehnlichkeit {mn:.2f}   {len(pr)} Probe(n)")
            for d, z, b in v:
                print(f"       {d}:{z}  {b[:82]}")

    # **Die dritte Fehlerrichtung, und sie ist die groesste:** dieses Werkzeug sieht nur
    # Kennungen, die WOERTLICH im Absagekonstruktor stehen. Wer ueber eine Hilfsfunktion
    # absagt, kommt gar nicht erst vor -- und das ist keine kleine Restmenge.
    alle = set()
    for q in sorted(W.glob("crates/*/src/*.rs")):
        if q.name in NICHT:
            continue
        alle |= set(re.findall(r'"([A-Z][0-9]{3})"', q.read_text(encoding="utf-8")))
    unsichtbar = sorted(alle - set(stellen))

    print("\n== Und was das NICHT heisst ==")
    print(f"  {len(unsichtbar)} Kennungen stehen in den Quellen und NICHT in einem")
    print("  Absagekonstruktor -- ueber eine Hilfsfunktion vergeben oder nur genannt.")
    print("  **Ueber sie sagt dieses Werkzeug gar nichts**, und das ist die groesste")
    print("  seiner drei Fehlerrichtungen.")
    print("  Dies ist eine KANDIDATENLISTE, kein Urteil. Eine Regel, die an zwei Stellen")
    print("  verschieden formuliert ist, sieht hier aus wie zwei; und zwei Regeln, die")
    print("  aehnlich klingen, kommen durch -- *nicht abgewiesen ist nicht bestaetigt* (W10).")
    print("  Die Entscheidung, ob zwei Vergabestellen dieselbe Regel sind, ist ein Urteil")
    print("  und faellt von Hand.")

    schlecht = 0
    if len(kand) > MARKE:
        print(f"\n  RATSCHE GEBROCHEN: {len(kand)} Kandidaten, gebucht sind {MARKE}.")
        schlecht = 1
    if len(betroffen) > MARKE_PROBEN:
        print(f"\n  RATSCHE GEBROCHEN: {len(betroffen)} betroffene Proben, gebucht sind {MARKE_PROBEN}.")
        schlecht = 1

    print(f"\n== Arbeitsmenge: {n_stellen} Vergabestellen, {len(stellen)} Kennungen, "
          f"{len(kand)} Kandidaten, {len(betroffen)} von {len(p)} Proben, 2 Proben ==")
    return schlecht


if __name__ == "__main__":
    sys.exit(main())
