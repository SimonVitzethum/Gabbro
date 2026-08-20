#!/usr/bin/env python3
"""**Systematisch erzeugte Mutationen gegen den Pruefer** — der Gegentest zu den 38 von Hand.

`mutiere-pruefer.py` beschaedigt 38 Regeln, die ich beim Schreiben im Kopf hatte. Der
Verdacht steht seit dem 2026-08-14 im TODO: *„Die 100 % sind eine Aussage ueber diese 38,
nicht ueber den Pruefer."* Dieses Werkzeug verdreht stattdessen **jede Stelle einer festen
Formklasse**, ohne zu wissen, welche Regel dort haengt.

**Vorab-Protokoll:** `MESSUNGEN.md`, Abschnitt *VORAB — systematisch erzeugte Mutationen*,
Commit `63fd2e0`. Zaehlregel, Kippregel und Tor stehen dort und werden hier nicht wiederholt,
damit es keine zweite Fassung gibt, die jemand parallel zur Wahrheit fuehrt.

Aufruf: `./instrumente/erzeuge-mutationen.py [--stichprobe N] [--klasse VERGL,BOOL,…]`
"""
import hashlib
import pathlib
import random
import re
import subprocess
import sys

WURZEL = pathlib.Path(__file__).resolve().parent.parent
CHECK = WURZEL / "crates/gabbro-check/src"
ZEIT = 180

# Jede Klasse ist ein Paar (Suchmuster, Ersetzung). Die Ersetzung darf den Text NICHT
# laenger machen als noetig -- eine Verdrehung, die nebenbei umformatiert, misst zwei Dinge.
KLASSEN = {
    "VERGL": [
        (r"(?<![<>=!])>=(?!=)", ">"),
        (r"(?<![<>=!])<=(?!=)", "<"),
        (r"(?<![<>=!])==(?!=)", "!="),
        (r"(?<![<>=!])!=(?!=)", "=="),
    ],
    "BOOL": [(r"&&", "||"), (r"\|\|", "&&")],
    "KONST": [(r"\b([0-9]+)\b", None)],  # None = Sonderbehandlung: +1
}

# Zeilen, an denen eine Verdrehung nichts ueber eine REGEL sagt.
BLIND = re.compile(
    r"^\s*(//|///|//!)"                       # Kommentare -- eine Verdrehung dort ist keine
    r"|format!|push_str|write!|\.mit_notiz|Absage::"
    r'|"[^"]{20,}"'                            # lange Zeichenketten: Meldungstext
    r'|^\s*"'                                  # FORTSETZUNG einer Meldung ueber Zeilen --
    r"|\\\s*$"                                 # zweite Filterluecke des ersten Laufs
)


def stellen(datei: pathlib.Path):
    """Alle mutierbaren Stellen einer Datei: (Zeilennr, Klasse, alt, neu).

    **Testkoerper zaehlen NICHT.** Eine Mutation in einem `#[cfg(test)]`-Bereich misst die
    Probe, nicht die Regel -- der Lauf vom 2026-08-15 hatte drei davon unter den
    "entkommenen" und meldete sie selbst als Filterluecke. Geschlossen 2026-08-15, und
    zwar VOR dem zweiten Lauf: sonst waere die Grundgesamtheit gewachsen (377 -> 557,
    weil die neuen Wertetabellen selbst mutierbar sind), die Ziehung eine andere, und
    der Vergleich zweier Quoten waere keiner.
    """
    zeilen = datei.read_text().splitlines()
    testab = next((i for i, l in enumerate(zeilen) if "#[cfg(test)]" in l), len(zeilen))
    aus = []
    for nr, zeile in enumerate(zeilen, 1):
        if nr > testab:
            break
        if BLIND.search(zeile):
            continue
        for klasse, regeln in KLASSEN.items():
            for muster, ersatz in regeln:
                for m in re.finditer(muster, zeile):
                    if ersatz is None:  # KONST: Literal um 1 verschieben
                        neu = zeile[: m.start()] + str(int(m.group(1)) + 1) + zeile[m.end() :]
                    else:
                        neu = zeile[: m.start()] + ersatz + zeile[m.end() :]
                    if neu != zeile:
                        aus.append((datei, nr, klasse, zeile, neu))
    return aus


def fahre(datei, nr, alt, neu):
    """Setzt die Mutation, faehrt die Proben, stellt wieder her.

    Rueckgabe: 'gefangen' | 'entkommen' | 'ungueltig (…)'.
    """
    urtext = datei.read_text()
    zeilen = urtext.splitlines(keepends=True)
    ende = "\n" if zeilen[nr - 1].endswith("\n") else ""
    zeilen[nr - 1] = neu + ende
    datei.write_text("".join(zeilen))
    try:
        b = subprocess.run(
            ["cargo", "build", "--quiet"], cwd=WURZEL, capture_output=True, timeout=ZEIT
        )
        if b.returncode != 0:
            return "ungueltig (uebersetzt nicht)"
        t = subprocess.run(
            ["cargo", "test", "--quiet"], cwd=WURZEL, capture_output=True, timeout=ZEIT
        )
        return "gefangen" if t.returncode != 0 else "entkommen"
    except subprocess.TimeoutExpired:
        # Kippregel: Grenzfaelle in die TEURERE Spalte -- nicht als gefangen buchen.
        return "ungueltig (Zeitschranke)"
    finally:
        datei.write_text(urtext)


def main():
    stichprobe = 40
    if "--stichprobe" in sys.argv:
        stichprobe = int(sys.argv[sys.argv.index("--stichprobe") + 1])

    if subprocess.run(
        ["git", "diff", "--quiet", "--", "crates/"], cwd=WURZEL
    ).returncode != 0:
        print("crates/ ist nicht sauber -- erst committen. Dieses Werkzeug schreibt in Quellen.")
        return 2

    alle = []
    for f in sorted(CHECK.glob("*.rs")):
        alle += stellen(f)
    print(f"== {len(alle)} mutierbare Stellen in {len(list(CHECK.glob('*.rs')))} Dateien ==")

    # **Deterministische Auswahl.** Ein Lauf, der bei jedem Aufruf andere Stellen zieht, ist
    # nicht nachfahrbar -- und eine Zahl, die niemand wiederholen kann, ist keine Messung.
    r = random.Random(int(hashlib.sha256(b"gabbro-mutgen-1").hexdigest()[:8], 16))
    ziehung = r.sample(alle, min(stichprobe, len(alle)))

    gefangen, entkommen, ungueltig = 0, [], []
    for i, (datei, nr, klasse, alt, neu) in enumerate(ziehung, 1):
        zustand = fahre(datei, nr, alt, neu)
        marke = {"gefangen": "  "}.get(zustand, "!!")
        print(f"  {marke} {i:>3}/{len(ziehung)} {zustand:<26} {datei.name}:{nr} [{klasse}]")
        if zustand == "gefangen":
            gefangen += 1
        elif zustand == "entkommen":
            entkommen.append((datei, nr, klasse, alt.strip(), neu.strip()))
        else:
            ungueltig.append((datei, nr, zustand))

    gueltig = gefangen + len(entkommen)
    print(f"\n== {gefangen} von {gueltig} gueltigen erzeugten Mutationen gefangen ==")
    print(f"   {len(ungueltig)} ungueltig (aus Zaehler UND Nenner -- W1: Belege, nicht Versuche)")
    if gueltig < 30:
        print("\n   UNGUELTIGER LAUF: weniger als 30 Mutanten uebersetzen.")
        print("   Dieser Lauf misst den Generator, nicht den Pruefer (Vorab-Protokoll).")
        return 1
    if entkommen:
        print(f"\n== {len(entkommen)} ENTKOMMEN -- jede ist ein Befund ==")
        for datei, nr, klasse, alt, neu in entkommen:
            print(f"     {datei.name}:{nr} [{klasse}]")
            print(f"       alt: {alt[:100]}")
            print(f"       neu: {neu[:100]}")
        print("\n   Eine entkommene Mutation heisst: diese Stelle koennte ausfallen, ohne dass")
        print("   eine einzige Probe faellt. Das TOR IST BESTANDEN -- `38 von 38` war eine")
        print("   Aussage ueber 38 gewaehlte Stellen, nicht ueber den Pruefer.")
    else:
        print("\n   KEINE entkommen. Das Tor ist GEFALLEN, und das ist ein Ergebnis:")
        print("   der Pruefer ist an den erzeugten Stellen so dicht wie an den gewaehlten.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
