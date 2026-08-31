#!/usr/bin/env python3
"""**Keine Kennung zweimal.** Der Waechter gegen eine Fehlerklasse, die ich an einem Tag
dreimal begangen habe.

Am 2026-08-14 habe ich beim Bau von `locks shared` die Kennungen `K003` und `S001`/`S002`
vergeben, ohne nachzusehen, wer sie schon hat: `kosten.rs` fuehrt `K003` seit Pass 9 fuer
unbekannte Aufrufkosten, `schleifen.rs` fuehrt `S001`/`S002` seit Pass 6 fuer die
Schleifenmarke und den durchfallenden `else`-Zweig.

**Warum das mehr ist als Kosmetik:** die Giftproben pruefen auf **Kennungen**
(`-- erwartet: CODE`). Eine doppelt vergebene Kennung macht jede solche Probe mehrdeutig --
sie faellt gruen, waehrend die gemeinte Regel ausgefallen ist. *Genau die Bewegung, gegen die
der ganze Ordner gebaut ist.*

**Die Regel, mechanisch:** eine Kennung darf in beliebig vielen ZEILEN stehen (dieselbe Regel
an mehreren Stellen ist normal), aber nur in **einer Datei**. Die Datei ist die Regel.

Sprechprobe in beide Richtungen, und sie faehrt in JEDEM Lauf. `--sprechprobe`
faehrt nur sie und sonst nichts.
"""
import collections
import pathlib
import re
import sys

WURZEL = pathlib.Path(__file__).resolve().parent.parent
KENNUNG = re.compile(r'"([A-Z][0-9]{3})"')


def erhebe(zusatz=None):
    """Kennung -> Menge der Dateien, die sie vergeben."""
    karte = collections.defaultdict(set)
    for q in sorted((WURZEL / "crates").rglob("*.rs")):
        if "/tests/" in str(q):
            continue          # Tests NENNEN Kennungen, sie vergeben keine
        # **Dasselbe fuer das Passregister** (seit 2026-08-21): `saetze.rs` fuehrt je Satz
        # die Kennungen auf, mit denen er absagt -- es NENNT sie, es vergibt sie nicht.
        # *Ohne diese Zeile meldete dieser Waechter 146 Doppelbelegungen, und keine davon
        # war eine.*
        if q.name == "saetze.rs":
            continue
        text = q.read_text()
        if zusatz and q.name == zusatz[0]:
            text += zusatz[1]
        for m in KENNUNG.finditer(text):
            karte[m.group(1)].add(q.name)
    return karte


def befunde(karte):
    return sorted((k, sorted(v)) for k, v in karte.items() if len(v) > 1)


def sprechprobe():
    """**In beide Richtungen -- und die zweite nimmt ihren Massstab NICHT vom Gegenstand.**

    Der Waechter muss eine kuenstliche Doppelbelegung SEHEN und dieselbe Kennung ohne das
    Gift DURCHLASSEN.

    Bis zum 2026-08-31 lautete die Gegenrichtung *„die echte Lage meldet nichts"*, und das
    ist genau die Falle, die `pruefe-todo.py` schon einmal bezahlt hat: eine WIRKLICHE
    Doppelbelegung haette die Probe fallen lassen, der Waechter haette mit `2` abgebrochen
    -- **und den Befund dabei verschluckt.** *Eine Probe, die ihren Massstab aus ihrem
    Gegenstand nimmt, misst den Gegenstand nicht.* Gefragt wird darum nur nach `K001`: mit
    Gift eine Doppelbelegung, ohne Gift keine -- unabhaengig davon, was sonst im Baum steht.
    """
    gift = befunde(erhebe(("namen.rs", '\nlet _ = "K001";\n')))
    sauber = befunde(erhebe())
    gesehen = any(k == "K001" for k, _ in gift)
    frei = not any(k == "K001" for k, _ in sauber)
    print("== Sprechprobe ==")
    print(f"  kuenstliche Doppelbelegung K001: {'gesehen' if gesehen else 'UEBERSEHEN'}")
    print(f"  ohne das Gift ist K001 frei:     {'ja' if frei else 'FALSCHER ALARM'}")
    return gesehen and frei


def main():
    # **DIE SPRECHPROBE FAEHRT IMMER** (2026-08-31). Bis heute stand sie hinter
    # `--sprechprobe`, und `abnahme.py` ruft dieses Werkzeug ohne Argumente -- **der
    # Regellauf hat also nie geprueft, ob dieser Waechter ueberhaupt rot werden kann.**
    # Von allen 28 Waechtern war er der einzige mit einer Probe auf Bestellung; der Rest
    # faehrt sie im Regellauf. *Eine Sprechprobe, die man anfordern muss, ist von keiner
    # nicht zu unterscheiden* (R14).
    if not sprechprobe():
        # 2, nicht 1: ein Waechter, der seine eigene Probe nicht besteht, hat NICHTS
        # gemessen -- was er danach ueber die Kennungen sagt, ist keine Aussage ueber sie.
        print("\n! Der Waechter misst nicht, was er behauptet. ABBRUCH.")
        return 2
    if "--sprechprobe" in sys.argv:
        return 0

    karte = erhebe()
    # **`0 issued ... ALL PASS` was a GREEN run until 2026-08-31** (measured over an empty
    # tree). Every identifier belonged to exactly one file because there were none -- the
    # statement is true, empty, and it looks like a result. *That is W17, and this workshop
    # has already paid for the sentence once, with `zaehle-b3.py`.*
    if not karte:
        print("ABBRUCH: keine einzige Kennung erhoben -- es wurde NICHTS gemessen.")
        print("  `jede Kennung gehoert genau einer Datei` ist ueber der leeren Menge wahr")
        print("  und sagt nichts. Eine leere Grundgesamtheit ist eine Absage (W1, W17).")
        return 2
    b = befunde(karte)
    print(f"== Kennungen: {len(karte)} vergeben ==")
    if not b:
        letters = collections.Counter(k[0] for k in karte)
        print("  " + ", ".join(f"{c}: {n}" for c, n in sorted(letters.items())))
        print("== KENNUNGEN: ALL PASS -- jede Kennung gehoert genau einer Datei ==")
        return 0
    for k, dateien in b:
        print(f"  !! {k} wird in {len(dateien)} Dateien vergeben: {', '.join(dateien)}")
    print(f"\n== KENNUNGEN: {len(b)} DOPPELBELEGUNGEN ==")
    print("  Eine Giftprobe mit `-- erwartet: <Kennung>` ist damit mehrdeutig: sie faellt")
    print("  gruen, waehrend die gemeinte Regel ausgefallen sein kann.")
    return 1


if __name__ == "__main__":
    sys.exit(main())
