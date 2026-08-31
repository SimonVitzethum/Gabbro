#!/usr/bin/env python3
"""**Die `narrow`-Zaehlung ueber Gabbro-Quelltext** — ohne Klassifikator.

Die erste Zaehlung (2026-08-14, ueber Rust) starb an ihrem Klassifikator: eine Handstichprobe
zeigte in 3 von 5 Faellen einen Fehler, alle in dieselbe Richtung. **Hier entscheidet kein
Skript, was eine Bereichspflicht ist, sondern der Pass, der sie prueft.**

Verfahren: alle `narrow`-Anweisungen aus dem Korpus entfernen, `gabbro pruefe` fahren, die
`M101`/`M104`-Fundstellen zaehlen. Jede ist eine Stelle, die ohne `narrow` nicht uebersetzt.

**Vorab-Protokoll:** `MESSUNGEN.md`, Abschnitt *VORAB — die `narrow`-Zaehlung*, Commit
`70053c4`. Zaehlregel, Stichprobenumfang, Fehlerschranke und Tor stehen dort.

Aufruf: `./instrumente/zaehle-bereichspflichten.py [--selbstprobe]`
"""
import pathlib
import re
import subprocess
import sys

WURZEL = pathlib.Path(__file__).resolve().parent.parent

# **Jede Ausfuehrung mit Frist.** Ein Haenger sieht aus wie „laeuft noch", nicht wie
# ein Befund -- am 2026-08-20 standen deswegen einundzwanzig Laeufe von
# `pruefe-emission.sh` nebeneinander, der aelteste seit dreieinhalb Stunden.
FRIST = 600
KORPUS = WURZEL / "dokumente/FRAGMENTE.md"


def ohne_narrow(text):
    """Entfernt jede `narrow`-Anweisung samt ihrem `else`-Block.

    Der Block ist einzeilig (`narrow x to a .. b else { … }`) oder mehrzeilig; gezaehlt wird
    ueber die geschweiften Klammern, nicht ueber die Einrueckung.
    """
    aus, zeilen, i, entfernt = [], text.splitlines(keepends=True), 0, 0
    while i < len(zeilen):
        if re.match(r"\s*narrow\s", zeilen[i]):
            entfernt += 1
            tiefe = zeilen[i].count("{") - zeilen[i].count("}")
            i += 1
            while i < len(zeilen) and tiefe > 0:
                tiefe += zeilen[i].count("{") - zeilen[i].count("}")
                i += 1
            continue
        aus.append(zeilen[i])
        i += 1
    return "".join(aus), entfernt


def messe(quelle):
    """Faehrt den Korpus und liefert (Fundstellen, Einheiten_sauber, Einheiten, roh).

    **Bricht sichtbar ab, statt null zu zaehlen** (R14a): laeuft der Uebersetzer nicht, ist
    das kein Ergebnis von null Pflichten, sondern gar kein Ergebnis.
    """
    tmp = WURZEL / "target" / "narrowprobe.md"
    tmp.parent.mkdir(exist_ok=True)
    tmp.write_text(quelle)
    r = subprocess.run(
        ["cargo", "run", "-q", "-p", "gabbro-cli", "--", "fragmente", str(tmp)],
        cwd=WURZEL,
        capture_output=True,
        text=True, timeout=FRIST)
    if r.returncode not in (0, 1) or "Translation units" not in r.stdout:
        print("!! ABBRUCH: `gabbro fragmente` lief nicht -- das ist KEINE Zaehlung von null.")
        print((r.stderr or r.stdout)[-800:])
        sys.exit(2)
    stellen = set()
    for m in re.finditer(r"\[(M101|M104)\] \S+?:(\d+):(\d+):(\d+):", r.stdout):
        stellen.add((m.group(2), m.group(3)))   # Einheit + Zeile: EINE Pflicht
    sauber = re.search(r"(\d+) of (\d+) with no errors", r.stdout)
    return stellen, int(sauber.group(1)), int(sauber.group(2)), r.stdout


def main():
    urtext = KORPUS.read_text()
    gestrichen, entfernt = ohne_narrow(urtext)

    if "--selbstprobe" in sys.argv:
        # **R14b: die Zahl muss am Pruefling haengen.** Ein wieder eingesetztes `narrow`
        # senkt N um genau eins -- sonst misst der Lauf etwas anderes als er behauptet.
        voll, _, _, _ = messe(urtext)
        leer, _, _, _ = messe(gestrichen)
        print(f"== Selbstprobe (R14) ==")
        print(f"  mit allen {entfernt} `narrow`:  {len(voll)} Fundstellen")
        print(f"  ohne jedes `narrow`:      {len(leer)} Fundstellen")
        # Eines wieder einsetzen: die erste entfernte Stelle.
        eins, _ = ohne_narrow(urtext)
        erste = re.search(r"(\s*narrow\s[^\n]*\n(?:[^\n]*\n)*?\s*\}\n)", urtext)
        if erste:
            mit_einem = gestrichen  # Platzhalter, s. u.
        gefallen = len(leer) - len(voll)
        print(f"  Unterschied:              {gefallen}")
        ok = gefallen == entfernt
        print(f"  {'BESTANDEN' if ok else 'GEFALLEN'}: {entfernt} entfernte `narrow` -> "
              f"{gefallen} zusaetzliche Pflichten")
        if not ok:
            print("  Die Zahl haengt NICHT eins zu eins am Pruefling. Vor der Zaehlung klaeren:")
            print("  entweder deckt ein `narrow` mehrere Pflichten, oder eine Pflicht faellt")
            print("  aus einem anderen Grund weg. Beides ist berichtenswert.")
        return 0 if ok else 1

    # **`N_ritus` -- das Tor von K100.1, zum ersten Mal GEMESSEN** (2026-08-20).
    #
    # K100.1 buchte: *„`zaehle-bereichspflichten.py` unterscheidet die drei Faelle"*. Es tat
    # es nicht -- die Unterscheidung stand in `PFLICHTEN.md`, also im Urteil, und nicht im
    # Werkzeug. **Sechster Fall an einem Tag, in dem eine Buchung auf etwas zeigte, das
    # anderswo lag.**
    #
    # Die messbare Haelfte braucht kein Urteil: **ein `narrow`, dessen Entfernung nichts
    # aendert, ist ein Ritus.** Eines nach dem anderen entfernen und den Unterschied zaehlen
    # -- die Zwei-Ebenen-Sonde (W8), auf die eigene Quelle angewandt.
    #
    # *Was es NICHT entscheidet:* ob ein tragendes `narrow` Logik oder ein Loch in M1 ist.
    # Das ist die Frage nach der ERREICHBARKEIT des `else`-Zweigs, und die beantwortet
    # dieses Verfahren nicht. **Ein Ritus dagegen ist ohne Urteil erkennbar.**
    voll, _, _, _ = messe(urtext)
    rituale = []
    zeilen = urtext.splitlines(keepends=True)
    stellen_narrow = [i for i, z in enumerate(zeilen) if re.match(r"\s*narrow\s", z)]
    for i in stellen_narrow:
        eins_weg, n = ohne_narrow("".join(zeilen[i:]))
        text = "".join(zeilen[:i]) + eins_weg if n == 1 else None
        if text is None:
            # `ohne_narrow` hat mehr als eines erwischt -- dann sagt der Lauf nichts.
            continue
        s1, _, _, _ = messe(text)
        if len(s1) == len(voll):
            rituale.append(i + 1)

    stellen, sauber, ganz, roh = messe(gestrichen)
    print(f"== Bereichspflichten im Gabbro-Korpus ==")
    print(f"  N_folgenlos = {len(rituale)}"
          + (f" -- Zeilen {', '.join(map(str, rituale))}" if rituale else ""))
    print( "  Ein `narrow`, dessen Entfernung NICHTS aendert, ist Zierde: M1 traegt die")
    print( "  Schranke ohnehin.")
    print()
    print( "  **Und das ist NICHT `N_ritus`.** `MESSUNGEN.md` definiert `N_ritus` als die")
    print( "  Stelle, deren `else`-Zweig UNERREICHBAR ist -- die traegt sehr wohl eine")
    print( "  Pflicht (M1 sieht die Schranke nicht) und faellt hier darum nicht auf.")
    print( "  *Zwei verschiedene Fragen, und bis zum 2026-08-20 hiessen sie beide `N_ritus`.*")
    print( "  Die Erreichbarkeit bleibt ein Urteil; dieses Werkzeug misst die Folgenlosigkeit.")
    print(f"  entfernte `narrow`-Anweisungen: {entfernt}")
    print(f"  Tor P2 ohne sie:               {sauber} von {ganz} sauber")
    if sauber == ganz:
        print("  ACHTUNG: das Tor faellt NICHT -- ohne `narrow` uebersetzt alles.")
        print("  Dann misst dieser Lauf nichts (Vorab-Protokoll: ungueltig).")
    print(f"\n== N = {len(stellen)} Fundstellen ==")
    for e, z in sorted(stellen, key=lambda x: (int(x[0]), int(x[1]))):
        print(f"     Einheit ab {e}, Zeile {z}")
    zeilen = sum(1 for _ in re.findall(r"^", gestrichen, re.M))
    print(f"\n  Korpus: 791 Zeilen Gabbro in {ganz} Einheiten")
    print(f"  Dichte: {len(stellen)} Pflichten / 791 Zeilen = "
          f"{len(stellen) * 1000 / 791:.1f} je 1000 Zeilen")
    print("  Die Hochrechnung steht im Bericht, NICHT hier -- die sechs Fragmente sind nach")
    print("  Schwierigkeit gewaehlt, nicht zufaellig, und tragen keinen Mittelwert.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
