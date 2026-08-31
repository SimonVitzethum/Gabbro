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
    """**Both directions -- and the second one does NOT take its yardstick from the subject.**

    The guardian has to SEE an artificial double issue and to LET THROUGH the same
    identifier once the poison is gone.

    Until 2026-08-31 the counter-direction read *"the real state reports nothing"*, and that
    is exactly the trap `pruefe-todo.py` has already paid for once: a REAL double issue would
    have made the probe fall, the guardian would have aborted with `2` -- **and swallowed the
    finding while doing so.** *A probe that takes its yardstick from its subject does not
    measure the subject.* So the question is only about `K001`: a double issue with the
    poison, none without it -- whatever else stands in the tree.
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
    # **THE SPEECH TEST RUNS EVERY TIME** (2026-08-31). Until today it sat behind a flag,
    # and `abnahme.py` calls this tool with no arguments at all -- **so the regular run
    # never once checked whether this guardian can go red.** Of all 28 guardians it was the
    # only one whose probe had to be ordered; every other runs it unasked. *A speech test
    # you have to request is indistinguishable from none* (R14).
    if not sprechprobe():
        # 2, not 1: a guardian that fails its own probe has measured NOTHING -- what it
        # says about the identifiers afterwards is not a statement about them.
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
