#!/usr/bin/env python3
"""**Der RUMPFKANAL -- wie viele der gezaehlten Pflichten kann ein Beweiser ueber dem RUMPF lesen?**

`gabbro pflichten --isabelle` schreibt das Register als Isabelle-Theorie und sagt siebzehn
Pflichten mit `body-effect` ab: *„redet ueber die Welt NACH einem Rumpf, und es gibt keine
Semantik eines Gabbro-Rumpfs."* `gabbro pflichten --lean` schreibt dasselbe Register gegen
`Passlogik.Rumpf` -- die Bedeutung, die dort fehlte.

**Dieses Werkzeug zaehlt beide Spalten ueber dem Korpus.** Und die zweite ist die, auf die es
ankommt: ein Erzeuger, der neunundfuenfzig Pflichten verschluckt und drei ausgibt, sieht in
der ersten Spalte genauso aus wie einer, der neunundfuenfzig ABSAGT und drei ausgibt -- *und
nur der zweite hat etwas gemessen.* Der Lauf FAELLT deshalb, wenn `Ziele + Absagen` nicht auf
die Gesamtzahl kommt, und er faellt noch einmal, wenn die Gruende nicht auf die Absagen kommen.

    ./instrumente/zaehle-lean.py                 ueber `beispiele/` und `messung/`
    ./instrumente/zaehle-lean.py --je-datei      mit der Tafel, Datei fuer Datei

Das Binaerprogramm wird auf `ki-pc-fisch-101` gebaut (CLAUDE.md); dieses Werkzeug ruft ein
vorhandenes `target/debug/gabbro` und baut nicht.
"""
import collections
import glob
import pathlib
import re
import subprocess
import sys

W = pathlib.Path(__file__).resolve().parent.parent
GABBRO = W / "target" / "debug" / "gabbro"

# **Every run under a deadline.** A hang looks like "still running", not like a finding --
# the same lesson `mutiere-pruefer.py` carries at the top of its file.
FRIST = 120

# The refusal reasons exactly as `lean.rs` writes them. **The list stands here in FULL** -- a
# reason the emitter knows and this tool does not shows up below as `UNBEKANNT` instead of
# quietly landing in no column at all.
GRUENDE = [
    ("foreign-body", "ein `ensures` an einem fremden Rumpf -- eine ANNAHME, kein Ziel"),
    ("table-invariant", "`maintains` nennt eine Tabelleninvariante: quantifiziert ueber jeden Slot"),
    ("call-site", "eine Vorbedingung am Rufort -- die traegt der Isabelle-Kanal"),
    ("device-promise", "eine Zusage an Hardware, die Gabbro nicht sieht"),
    ("statement-outside-core", "eine Anweisungsart ausserhalb des sequentiellen Kerns"),
    ("no-term", "eine Form, fuer die dieser Kanal keinen Lean-Term hat"),
    ("carrier-not-a-table", "der Traeger eines Ortes ist keine erklaerte `table`"),
    ("no-shape-for-field", "die erklaerte Art eines Slotfeldes hat hier keine Form"),
    ("spec-not-an-expression", "die genannte `spec fn` ist kein blosser Ausdrucksrumpf"),
]

KOPF = re.compile(r"@duty 1  (\S+)  total (\d+)  goals (\d+)  refused (\d+)")
ZEILE = re.compile(r"^  (\S+) \((\d+)\): ")


def lies_kopf(text):
    """`(gesamt, ziele, abgesagt)` aus dem Kopf, oder `None`, wenn keiner dasteht."""
    m = KOPF.search(text)
    return (int(m.group(2)), int(m.group(3)), int(m.group(4))) if m else None


def sprechprobe():
    """**In beide Richtungen: eine luegende Bilanz muss fallen, eine ehrliche nicht.**

    Das ganze Urteil dieses Werkzeugs haengt an einer Rechenprobe, und *eine Probe, die
    niemand hat fallen sehen, ist eine Verzierung* (R11).
    """
    gut = "        @duty 1  x.gab  total 4  goals 1  refused 3\n"
    gift = "        @duty 1  x.gab  total 4  goals 1  refused 1\n"
    stumm = "        nichts hier ueber sich selbst\n"
    a, b, c = lies_kopf(gut), lies_kopf(gift), lies_kopf(stumm)
    ok_gut = a is not None and a[1] + a[2] == a[0]
    ok_gift = b is not None and b[1] + b[2] != b[0]
    ok_stumm = c is None
    print("== Sprechprobe ==")
    print("  ehrliche Bilanz geht durch:  %s" % ("ja" if ok_gut else "NEIN"))
    print("  luegende Bilanz faellt:      %s" % ("ja" if ok_gift else "NEIN"))
    print("  fehlender Kopf faellt:       %s" % ("ja" if ok_stumm else "NEIN"))
    return ok_gut and ok_gift and ok_stumm


def main() -> int:
    je_datei = "--je-datei" in sys.argv
    if not sprechprobe():
        print("== RUMPFKANAL: der Waechter misst nicht ==")
        return 2
    if not GABBRO.exists():
        print(f"ABBRUCH: {GABBRO} fehlt -- gebaut wird auf ki-pc-fisch-101 (CLAUDE.md).")
        return 1
    dateien = sorted(glob.glob(str(W / "beispiele" / "*.gab"))) + sorted(
        glob.glob(str(W / "messung" / "*" / "*.gab"))
    )
    gesamt = ziele = abgesagt = 0
    ohne_register = 0
    je_grund: collections.Counter = collections.Counter()
    tafel = []
    for f in dateien:
        rel = str(pathlib.Path(f).relative_to(W))
        try:
            lauf = subprocess.run(
                [str(GABBRO), "pflichten", "--lean", rel],
                cwd=W,
                capture_output=True,
                text=True,
                timeout=FRIST,
            )
        except subprocess.TimeoutExpired:
            print(f"ABBRUCH: {rel} -- Frist {FRIST} s ueberschritten. Ein Haenger ist kein Befund.")
            return 1
        # **A unit with errors carries no register**, and that is the same rule
        # `gabbro pflichten` follows -- not a skipped file but one without an answer yet.
        if lauf.returncode != 0:
            ohne_register += 1
            continue
        kopf = lies_kopf(lauf.stdout)
        if kopf is None:
            print(f"ABBRUCH: {rel} -- kein `@duty`-Kopf. Der Erzeuger schweigt ueber sich selbst.")
            return 1
        g, z, a = kopf
        if z + a != g:
            print(f"ABBRUCH: {rel} -- {z} + {a} != {g}. Die Bilanz des Erzeugers geht nicht auf.")
            return 1
        gesamt += g
        ziele += z
        abgesagt += a
        hier: collections.Counter = collections.Counter()
        for zeile in lauf.stdout.splitlines():
            m = ZEILE.match(zeile)
            if m:
                hier[m.group(1)] += int(m.group(2))
        summe = sum(hier.values())
        if summe != a:
            print(f"ABBRUCH: {rel} -- die Gruende zaehlen {summe}, abgesagt sind {a}.")
            return 1
        je_grund.update(hier)
        if z or a:
            tafel.append((rel, g, z, a))

    bekannt = {t for t, _ in GRUENDE}
    for t in je_grund:
        if t not in bekannt:
            print(f"ABBRUCH: UNBEKANNTER Absagegrund `{t}` -- dieses Werkzeug ist veraltet.")
            return 1

    if je_datei:
        print()
        print("-- je Einheit --")
        print(f"   {'Einheit':<42} {'ges':>4} {'Ziel':>5} {'abges':>6}")
        for rel, g, z, a in tafel:
            print(f"   {rel:<42} {g:>4} {z:>5} {a:>6}")

    print()
    print("-- Der Bestand, wie der RUMPFKANAL ihn sieht --")
    print()
    for tag, satz in GRUENDE:
        print(f"   {tag:<24}{je_grund[tag]:>4}   {satz}")
    print()
    print(
        f"== RUMPFKANAL: {gesamt} Pflichten, {ziele} Ziele, {abgesagt} abgesagt "
        f"({ohne_register} Einheiten mit Fehlern, ohne Register) =="
    )
    print("   Und was das NICHT heisst: ein Ziel ist keine bewiesene Pflicht. Es heisst,")
    print("   dass die Pflicht GESCHLOSSEN dasteht. Ob sie durchgeht, sagt `lean`, und der")
    print("   Weg dorthin ist `./instrumente/pruefe-lean-beweis.sh`.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
