#!/usr/bin/env python3
"""**`MARKE_ALLEIN`, mit einem eigenen Ruecklaufwert -- und ohne die Sprachfrage zu beruehren.**

`pruefe-grammatiktafel.py` misst seit dem 2026-08-31, an wie vielen Dateien ein Wort der
Grammatik haengt (`MARKE_ALLEIN = 0`). Es DRUCKT die Zahl und laesst den Ruecklaufwert in
Ruhe, und der Grund steht dort: die vier `UNGEDECKT`-Zellen faerben jeden Lauf rot, und

    ein Anstieg waere unsichtbar in einem Rot, das eine andere Ursache hat.

Der Vorschlag daneben lautete: *sobald die vier Zellen entschieden sind und jener Waechter
gruen werden kann, soll `MARKE_ALLEIN` den Ruecklaufwert mitentscheiden.* **Das ist eine
Wartestellung, und sie kostet.** Die vier Zellen sind eine Entscheidung des Ordners und keine
Messfrage -- sie koennen Monate offen bleiben, und solange steigt die Zahl unbemerkt.

**WAS DIESES WERKZEUG STATTDESSEN TUT**

Es stellt **dieselbe Zahl** unter eine **eigene Frage** mit einem **eigenen Ruecklaufwert**:

    pruefe-grammatiktafel.py   Sind alle Terminale gedeckt?     -> heute ROT (vier Zellen)
    zaehle-empfindlichkeit.py  Haengt ein Wort an EINER Datei?  -> heute GRUEN

Zwei Fragen, zwei Farben, **eine Messung**. `abnahme.py` liest seine Besetzung aus dem
VERZEICHNIS, nicht aus einer Liste -- damit bekommt diese Frage von selbst ihre eigene Zeile
im Abnahmelauf, und ein Anstieg steht dort in seiner eigenen Farbe.

**UND WARUM DAS KEIN ZWEITES REGISTER IST (W7)**

**Hier steht keine Zahl und keine Messvorschrift.** Marke, Korpus, Uebersetzungstor,
Traegerkarte und der Auszaehler kommen alle aus `pruefe-grammatiktafel.py`, als Modul
geladen. Aendert sich dort die Definition von `gesenkt`, aendert sich hier die Antwort mit.
*Ein zweites Register ueber derselben Sache laeuft davon; ein zweiter EINGANG in dasselbe
Register tut es nicht.*

Was es kostet, ist ein zweiter Durchgang durch Korpus und Uebersetzer -- die Zahl haengt am
`cc`-Tor und laesst sich ohne es nicht bilden. Gemessen steht der Preis unten in der Ausgabe,
damit er nicht behauptet werden muss.

**DIE RICHTUNG, UND DASS BEIDE SEITEN EIN BEFUND SIND**

* **Steigt sie**, haengt ein Wort neu an einer einzigen Datei. Das ist nicht immer ein
  Schaden -- ein neues Terminal, das genau ein Programm schreibt, hebt sie auch. Darum
  druckt der Lauf jedes Wort mit seiner Adresse: *die Zahl ist die Frage, die Adresse die
  Antwort.* Ein Steigen braucht seinen Grund an der Marke.
* **Faellt sie**, ist die Marke ueberholt und gehoert nachgezogen. Der gute Fall, und
  trotzdem ein Befund -- eine Marke, die unter dem Gegenstand liegt, misst nichts mehr.

**Was hier NICHT entschieden wird:** nichts ueber die vier `UNGEDECKT`-Zellen. Sie faerben
`pruefe-grammatiktafel.py` weiter rot, und dieses Werkzeug sagt kein Wort ueber sie -- es
nimmt der Sprachentscheidung nichts vorweg, es nimmt ihr nur die Geiselhaft an dieser Zahl.
"""
import importlib.util
import os
import pathlib
import shutil
import sys

# **Whoever leaves mid-run says WHERE** -- the shared form, out of `abschnitt.py`.
# `sys.path` gets the tool's own directory because this file is also LOADED by
# `abnahme.py` (via `importlib`), and then `sys.path[0]` is the working directory.
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import abschnitt  # noqa: E402

# **Fifth requirement: the LOCALE.** The compiler gate below reports through `cc`, and under
# `de_DE.UTF-8` it says `Neudefinition` where this run expects `redefinition` -- a tool that
# measures its own locale looks plausible while doing it (W16).
os.environ["LC_ALL"] = "C"

W = pathlib.Path(__file__).resolve().parent.parent

# The whole measurement is READ from the table, never restated here (W7).
_spec = importlib.util.spec_from_file_location(
    "gt", W / "instrumente" / "pruefe-grammatiktafel.py")
_gt = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_gt)


def main():
    # **Tooth 0 -- the subject has to be there**, and the table already says what it needs.
    # A crash inside a loaded module returns 1 with a traceback and reads like a finding;
    # a NAMED refusal says the setup has to change and leaves with 2 (W1, W17).
    fehlend = [str(d.relative_to(W)) for d in (_gt.SYNTAX, _gt.KW) if not d.is_file()]
    if not _gt.CHECK.is_dir():
        fehlend.append(str(_gt.CHECK.relative_to(W)))
    if shutil.which("cc") is None:
        fehlend.append("`cc`")
    if fehlend:
        print("ABBRUCH: es fehlen: %s -- es wurde NICHTS gemessen." % ", ".join(fehlend),
              file=sys.stderr)
        print("  Die Empfindlichkeit haengt am Uebersetzungstor: `gesenkt` heisst\n"
              "  *emittiert UND uebersetzt*. Ohne Gegenstand waere `0 einsam` ein Urteil\n"
              "  ueber nichts (W1).", file=sys.stderr)
        return 2

    term = _gt.terminale()
    pruefer, _ = _gt.prueferworte()
    # The deadline sits with whoever executes -- `zaehle-absagen.korpuslauf` aborts per file
    # after its own `FRIST`. A second deadline beside it would be a second register (W7).
    za = _gt._lade("zaehle-absagen.py", ["x"])
    print(f"   (Frist je Datei: {za.FRIST} s, aus `zaehle-absagen.py` -- ein Ablauf bricht ab)",
          file=sys.stderr)
    korpus = za.korpuslauf()
    if not korpus:
        print("== EMPFINDLICHKEIT: KEIN LAUF -- es wurde NICHTS gemessen ==")
        print("   Ohne `gabbro emit` ueber dem Korpus gibt es den Zustand `gesenkt` nicht,")
        print("   und ohne ihn keine Traegerkarte. W1: der Ausfall senkt die Zahl, er")
        print("   laesst sie nicht unberuehrt.")
        return 2

    uebersetzt, faellt_durch = _gt.uebersetzende(korpus)
    karte = _gt.traeger(korpus, term, pruefer, dateien=uebersetzt)
    n1, n2, eins = _gt.empfindlichkeit(karte)

    print(f"== EMPFINDLICHKEIT: {n1} von {len(karte)} Woertern haengen an je EINER Datei "
          f"(Marke {_gt.MARKE_ALLEIN}) ==")
    print(f"   {len(karte)} der {len(term)} Terminale sind NUR durch Absenkung gedeckt --")
    print("   fuer sie ist die Uebersetzungsprobe die einzige Gegenprobe. Faellt die eine")
    print("   Datei aus der Uebersetzung, faellt das Wort mit.")
    print(f"   an je ZWEI Dateien: {n2} (Marke {_gt.MARKE_ZU_ZWEIT}, ohne Riegel -- diese")
    print("   Zahl STEIGT, wenn Woerter aus der Einserspalte herunterwandern.)")
    print(f"   {len(uebersetzt)} Dateien tragen die Karte; {len(faellt_durch)} emittieren und")
    print("   fallen am Uebersetzer -- deren Woerter zaehlen hier NICHT als gedeckt.")

    abschnitt.fertig()
    if n1 > _gt.MARKE_ALLEIN:
        print()
        print(f"! EMPFINDLICHKEIT GESTIEGEN: {n1} statt {_gt.MARKE_ALLEIN}. Jedes dieser")
        print("  Woerter haengt an einer einzigen Datei, und die Adresse steht daneben:")
        for t in sorted(eins):
            print(f"    {t:<16} {eins[t]}")
        print("  Ein Steigen ist nicht immer ein Schaden -- ein neues Terminal, das genau")
        print("  ein Programm schreibt, hebt die Zahl auch. Es braucht aber seinen GRUND")
        print("  an der Marke, und den kann nur ein Mensch hinschreiben.")
        print("  Die Einteilung der Woerter steht in `messung/EINSAME-WOERTER.md`.")
        return 1
    if n1 < _gt.MARKE_ALLEIN:
        print()
        print(f"! MARKE UEBERHOLT: {n1} < {_gt.MARKE_ALLEIN}. Sie gehoert nachgezogen --")
        print("  der gute Fall, und trotzdem ein Befund: eine Marke unter ihrem Gegenstand")
        print("  misst nichts mehr.")
        return 1

    print()
    print(f"== EMPFINDLICHKEIT GRUEN: {n1} Woerter an je EINER Datei, Marke {_gt.MARKE_ALLEIN} ==")
    print("   Und was das NICHT heisst: die vier `UNGEDECKT`-Zellen stehen unveraendert.")
    print("   Sie sind eine Entscheidung des Ordners und faerben `pruefe-grammatiktafel.py`")
    print("   weiter rot. Dieser Lauf sagt kein Wort ueber sie -- er sagt nur, dass die")
    print("   Deckung, die es GIBT, nicht an einzelnen Dateien haengt.")
    return 0


if __name__ == "__main__":
    sys.exit(abschnitt.fahre(main))
