#!/usr/bin/env python3
"""**Zahn 3: jede bewiesene Schablone bindet ihre Praemissen an einen Pass.**

    ./pruefe-schablonen.py [--je-praemisse]

DAS TOR UND DIE RATSCHE SIND ZWEI VERSCHIEDENE DINGE
----------------------------------------------------
    `gabbro schablonen --tor`   das ZIEL: faellt, solange EINE Praemisse haengt
    dieser Waechter             die taegliche Wache: faellt, wenn die Zahl STEIGT

*Ein Werkzeug, das jeden Tag rot ist, wird nicht gelesen.* Deshalb traegt das Tor die
Zielaussage und die Ratsche die Bewegung -- und die Ratsche faellt nur nach unten.

WARUM DAS SCHAERFER IST ALS EINE UNGELESENE KLAUSEL
---------------------------------------------------
Bei einer ungelesenen Klausel weiss niemand etwas. Hier steht ein **Isabelle-Beweis**, und
wer das Zeugnis liest, schliesst auf eine Eigenschaft, die nichts herstellt.

> **Ein Beweis, dessen Voraussetzung niemand herstellt, ist gefaehrlicher als eine
> ungepruefte Zusage -- weil ein Haekchen darueber steht.** Der Registerversatz war genau
> das: bewiesener Satz, keine Prueferzeile.

DIE ZWEITE FORDERUNG: JEDE HAENGENDE PRAEMISSE NENNT IHRE ADRESSE
-----------------------------------------------------------------
`durch: None` allein sagt *„niemand"*. Eine Liste von Loechern ohne die Angabe, womit man sie
fuellt, ist eine Klage und kein Arbeitsauftrag. **Eine haengende Praemisse ohne `braeuchte`
ist darum selbst ein Befund** -- unabhaengig von der Marke.

*Und `braeuchte` VERALTET.* Am 2026-08-20 waren zwei von neun falsch: `abstieg` hatte seit
dem 2026-08-19 einen Leser (`S005`), und die Wortmenge von `ops` war entschieden. **Dieser
Waechter kann das nicht sehen** -- er zaehlt Adressen, er prueft sie nicht. Das steht hier,
damit die Zahl nicht mehr verspricht, als sie misst (W10).
"""
import pathlib
import re
import subprocess
import sys

W = pathlib.Path(__file__).resolve().parent
BIN = W / "target" / "debug" / "gabbro"
FRIST = 60

# **Die gebuchte Marke.** Eine Ratsche, keine Zielzahl: sie darf fallen, nicht steigen.
# Das Ziel ist 0, und `gabbro schablonen --tor` sagt es jeden Tag.
MARKE = 9


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


def lies(text):
    """(haengende Praemissen als (Schablone, was, braeuchte), gemeldete Zahl)."""
    gemeldet = None
    m = re.search(r"PREMISES WITHOUT A PASS \(tooth 3\): (\d+)", text)
    if m:
        gemeldet = int(m.group(1))
    aus, offen = [], None
    for z in text.splitlines():
        t = re.match(r"^--     ([\w.]+): (.+)$", z)
        if t:
            if offen:
                aus.append(offen)
            offen = (t.group(1), t.group(2), None)
            continue
        b = re.match(r"^--       braeuchte: (.+)$", z)
        if b and offen:
            offen = (offen[0], offen[1], b.group(1))
    if offen:
        aus.append(offen)
    return aus, gemeldet


# **Die Sprechprobe, in beide Richtungen -- an der LOGIK dieses Waechters.** Das Register ist
# statische Rust-Tafel; eine Probe von aussen kann nichts hineinschieben. Also wird die
# Auswertung selbst gefuettert: ein Text mit einer adresslosen Praemisse MUSS auffallen.
GIFT = """--   of those PREMISES WITHOUT A PASS (tooth 3): 2 -- a proof nothing establishes.
--     probe.eins: eine Praemisse mit Adresse
--       braeuchte: irgendetwas
--     probe.zwei: eine Praemisse OHNE Adresse
"""
SAUBER = """--   of those PREMISES WITHOUT A PASS (tooth 3): 1 -- a proof nothing establishes.
--     probe.eins: eine Praemisse mit Adresse
--       braeuchte: irgendetwas
"""


def main():
    g, _ = lies(GIFT)
    s, _ = lies(SAUBER)
    if len(g) != 2 or g[1][2] is not None:
        print("SPRECHPROBE GESCHEITERT: eine adresslose Praemisse faellt nicht auf.",
              file=sys.stderr)
        return 1
    if len(s) != 1 or s[0][2] is None:
        print("SPRECHPROBE GESCHEITERT: eine Praemisse MIT Adresse wird beanstandet.",
              file=sys.stderr)
        return 1
    print("== Sprechprobe: ok (adresslos faellt auf, mit Adresse geht durch) ==\n")

    r = lauf("schablonen")
    if r.returncode != 0 or "tooth 3" not in r.stdout:
        print("ABBRUCH: `gabbro schablonen` lief nicht -- das ist KEINE Zaehlung von null.",
              file=sys.stderr)
        return 2
    luft, gemeldet = lies(r.stdout)
    if gemeldet is None or gemeldet != len(luft):
        print(f"ABBRUCH: das Werkzeug meldet {gemeldet}, gelesen wurden {len(luft)} -- "
              "die Auswertung dieses Waechters passt nicht mehr zur Ausgabe.", file=sys.stderr)
        return 2

    # Das Tor selbst -- der Ruecklaufwert des Werkzeugs, nicht ein zweites Urteil (W7).
    tor = lauf("schablonen", "--tor").returncode

    ohne_adresse = [(n, w) for n, w, b in luft if b is None]
    print(f"== Zahn 3: {len(luft)} Praemissen bewiesener Schablonen ohne Pass ==")
    print(f"   Marke {MARKE} -- eine Ratsche, keine Zielzahl: sie darf fallen, nicht steigen.")
    print(f"   Das TOR (`gabbro schablonen --tor`) gibt {tor} zurueck; es faellt, bis hier 0 steht.")
    print()
    if "--je-praemisse" in sys.argv:
        for n, was, b in luft:
            print(f"   {n}")
            print(f"     {was}")
            print(f"     -> {b if b else '!! KEINE ADRESSE'}")
        print()

    schlecht = 0
    if len(luft) > MARKE:
        print(f"FUND: {len(luft)} haengende Praemissen, gebucht sind {MARKE} -- "
              "die Ratsche laeuft nur nach unten.", file=sys.stderr)
        schlecht += 1
    elif len(luft) < MARKE:
        print(f"FUND: nur noch {len(luft)} statt {MARKE} -- die Marke gehoert nachgezogen "
              "(das ist der gute Fall, und er ist trotzdem ein Befund).", file=sys.stderr)
        schlecht += 1
    if ohne_adresse:
        for n, was in ohne_adresse:
            print(f"FUND: `{n}` -- Praemisse ohne `braeuchte`: {was[:70]}", file=sys.stderr)
        print("  Eine Liste von Loechern ohne die Angabe, womit man sie fuellt, ist eine "
              "Klage und kein Arbeitsauftrag.", file=sys.stderr)
        schlecht += len(ohne_adresse)

    print("== Und was das NICHT heisst ==")
    print("  Dieser Waechter zaehlt ADRESSEN, er prueft sie nicht. Am 2026-08-20 waren zwei")
    print("  von neun `braeuchte`-Texten VERALTET -- `abstieg` hatte seit dem Vortag einen")
    print("  Leser, und die Wortmenge von `ops` war entschieden. **Das sieht er nicht.**")
    print("  Die Adressen gehoeren von Hand am Gegenstand nachgeprueft (W10).")
    print()
    print(f"== Arbeitsmenge: {len(luft)} Praemissen, {len(ohne_adresse)} ohne Adresse, "
          f"1 Werkzeuglauf, 2 Proben ==")
    return 1 if schlecht else 0


if __name__ == "__main__":
    sys.exit(main())
