#!/usr/bin/env python3
"""**Der vervollstaendigte Fragmentkorpus, gemessen -- und die Ergaenzung mitgezaehlt.**

`dokumente/FRAGMENTE.md` traegt einen Einfriersatz: *„ein Bericht vom 2026-08-14, und er
bleibt unangetastet."* Die Absenkungspflicht aus K100 lautet aber *„das erzeugte C rechnet,
was das Fragment sagt"* -- **an der Ausfuehrung gemessen**. Ein Ausschnitt laesst sich nicht
ausfuehren.

Am 2026-08-20 wurde nachgezaehlt, was die zehn Ausschnitte daran hindert, und es war nicht
Gabbro: **41 Stellen nennen 20 Namen, die niemand deklariert**, neun `let … else` rufen
Ruempfe, die es nicht gibt, sechs Bitlagen sind unbenannt. **Jedes der sieben offenen
Fragmente trug mindestens einen korpusseitigen Riegel** -- F4, das reinste, brauchte genau
eine Zeile.

> Damit fiel die Absenkungsspalte um keinen Punkt, ohne in eine eingefrorene Datei zu
> schreiben. **Der Boden des Tores `H = 0` lag bei 7, nicht bei 0.**

`messung/fragmente/` ist der Ausweg, und es ist derselbe Zug wie «K2»: **nachgebildet, nicht
uebersetzt -- und ausdruecklich gesagt.** Je Datei steht im Kopf, was ergaenzt wurde und was
nicht, und dieser Zaehler haelt die Zahlen dagegen.

    ./instrumente/zaehle-fragmente.py [--je-datei]

**Und was das NICHT heisst:** eine Datei, die sauber prueft, ist nicht abgesenkt; eine, die
absenkt, ist nicht ausgefuehrt. Die drei Zahlen sind drei verschiedene Aussagen, und sie
stehen deshalb einzeln da (W11: jede Quote nennt ihr N).
"""
import pathlib
import re
import subprocess
import sys

W = pathlib.Path(__file__).resolve().parent.parent
KORPUS = W / "messung" / "fragmente"
FRIST = 300
BIN = W / "target" / "debug" / "gabbro"


def gabbro(*args):
    """Ein Lauf mit Frist. **Ohne sie meldet ein Haenger sich als „laeuft noch"** (W17)."""
    befehl = ([str(BIN)] if BIN.is_file() else
              ["cargo", "run", "-q", "--bin", "gabbro", "--"]) + list(args)
    try:
        return subprocess.run(befehl, cwd=W, capture_output=True, text=True, timeout=FRIST)
    except subprocess.TimeoutExpired:
        print(f"ABBRUCH: `{' '.join(args)}` ueberschritt {FRIST} s -- es wurde NICHTS gemessen.",
              file=sys.stderr)
        sys.exit(2)


def pflichtenzaehler():
    """`zaehle-pflichten.py` als Modul -- **ein Suchweg, nicht zwei Register** (W7)."""
    import importlib.util
    ort = W / "instrumente" / "zaehle-pflichten.py"
    if not ort.is_file():
        print(f"ABBRUCH: {ort} fehlt -- die Durchstichzahl wurde NICHT gemessen.",
              file=sys.stderr)
        sys.exit(2)
    spec = importlib.util.spec_from_file_location("zaehle_pflichten", ort)
    modul = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(modul)
    return modul


def messe(p):
    r = gabbro("pruefe", str(p))
    if "items," not in r.stdout:
        print(f"ABBRUCH: `gabbro pruefe {p.name}` lief nicht -- das ist KEINE Zaehlung von null.",
              file=sys.stderr)
        sys.exit(2)
    m = re.search(r"(\d+) errors", r.stdout)
    fehler = int(m.group(1)) if m else -1
    e = gabbro("emit", str(p))
    senkt = e.returncode == 0
    absagen = e.stdout.count("no lowering") + e.stderr.count("no lowering")
    # Wie viele Zeilen wurden ERGAENZT? Der Kopf sagt es, der Zaehler prueft es nach: alles
    # bis zur Trennlinie ist Kopf, und was danach neu ist, steht als `-- ERGAENZT`.
    text = p.read_text(encoding="utf-8")
    ergaenzt = len(re.findall(r"^-- ERGAENZT", text, re.M)) + text.count("-- ERGAENZT:")
    return fehler, senkt, absagen, ergaenzt


def main():
    if not KORPUS.is_dir():
        print(f"ABBRUCH: {KORPUS} fehlt -- es wird NICHT null gezaehlt.", file=sys.stderr)
        # **Every refusal in this file ends with 2, not 1** (2026-08-31). This counter joined
        # `abnahme.py` that day, so its return code is now read as a VERDICT -- and the sixth
        # requirement applies: `1` means the TREE has to change, `2` means the SETUP does.
        # Every site below says NOTHING WAS MEASURED, so every one of them is a `2`.
        return 2
    dateien = sorted(KORPUS.glob("F*.gab"))
    if len(dateien) != 10:
        print(f"ABBRUCH: {len(dateien)} Dateien statt 10 -- die Grundgesamtheit hat sich bewegt.",
              file=sys.stderr)
        return 2
    # **Sprechprobe, in beide Richtungen.** Eine erfundene Datei mit einem Fehler MUSS als
    # Fehler gezaehlt werden, eine leere nicht als null Dateien durchgehen.
    # speech_test: begin
    probe = KORPUS / "_sprechprobe.gab"
    probe.write_text("module p { impl fn f() -> u32 { return zzunbekannt; } }\n", encoding="utf-8")
    try:
        f_probe, _, _, _ = messe(probe)
    finally:
        probe.unlink()
    if f_probe <= 0:
        print("SPRECHPROBE GESCHEITERT: eine kaputte Datei zaehlt null Fehler -- "
              "dieser Zaehler misst nichts.", file=sys.stderr)
        return 2
    print(f"== Sprechprobe: ok (eine erfundene kaputte Datei zaehlt {f_probe} Fehler) ==\n")

    # speech_test: end
    sauber = senken = 0
    zeilen = []
    for p in dateien:
        fehler, senkt, absagen, ergaenzt = messe(p)
        sauber += fehler == 0
        senken += senkt
        zeilen.append((p.stem, fehler, senkt, absagen, ergaenzt))

    print(f"== Der vervollstaendigte Fragmentkorpus: {len(dateien)} Dateien ==")
    if "--je-datei" in sys.argv:
        print(f"  {'':<5} {'Fehler':>7} {'Absenkung':>12}")
        for n, f, s, a, _e in zeilen:
            print(f"  {n:<5} {f:>7} {'senkt ab' if s else f'{a} Absagen':>12}")
        print()
    # **The FOURTH number, and it is the one K100's first gate stands on** (2026-08-25).
    #
    # The paragraph below has always said *"one that lowers has not been run"* -- and then did
    # not count the ones that were. The lowering obligation reads *"the generated C computes
    # what the fragment says"*, **measured by execution**; stopping at `senkt ab` stops one
    # step short of the statement.
    #
    # **And it is read at the RUN, not at the line** (2026-08-31). Until today this stood
    # here:
    #
    #     waechter = (W / "instrumente" / "pruefe-emission.sh").read_text(...)
    #     gestochen = {... for m in re.findall(r'^lauf "fragment(\d+)"', waechter, re.M)}
    #
    # -- the SECOND member of the family that `zaehle-pflichten.py` was caught in on the same
    # day. Three lines above, this file runs `gabbro pruefe` and `gabbro emit` over every
    # fragment and counts what comes back; **for the one number that says AUSGEFUEHRT it read
    # a line of shell.** *A counter that runs for three of its four figures and reads text for
    # the fourth looks measured all the way through.*
    #
    # `zaehle-pflichten.absenkung()` is the one search path now (W7: not a second register),
    # and it answers out of `pruefe-emission.sh --absenkung` -- 1,7 s, a real run per fragment.
    zp = pflichtenzaehler()
    haelt, faellt, _ = zp.absenkung()
    gestochen = {f"F{int(f[1:]):02d}" for f in haelt}
    gefallen = {f"F{int(f[1:]):02d}" for f in faellt}
    print(f"  {sauber} von {len(dateien)} pruefen sauber")
    print(f"  {senken} von {len(dateien)} senken ab")
    print(f"  {len(gestochen)} von {len(dateien)} sind DURCHGESTOCHEN -- "
          f"{', '.join(sorted(gestochen)) or 'keines'}")
    print("     erzeugt, uebersetzt, AUSGEFUEHRT und gegen eine Handschrift verglichen.")
    if gefallen:
        print(f"  {len(gefallen)} traegt einen Differenztest, dessen Lauf FAELLT -- "
              f"{', '.join(sorted(gefallen))}")
        print("     **eine gebaute Einloesung, die weggefallen ist** -- ein anderer Zustand")
        print("     als „nie durchgestochen\", und bis zum 2026-08-31 nicht unterscheidbar.")
    print()
    print("  Vor der Vervollstaendigung (2026-08-20, ueber den Ausschnitten):")
    print("  5 von 10 sauber, 3 von 10 senkten ab -- und JEDES der sieben offenen trug")
    print("  mindestens einen korpusseitigen Riegel.")
    print()
    print("== Und was das NICHT heisst ==")
    print("  Eine Datei, die sauber prueft, ist nicht abgesenkt; eine, die absenkt, ist")
    print("  nicht ausgefuehrt. **Vier verschiedene Aussagen, vier Zahlen** (W11) -- die")
    print("  vierte kam am 2026-08-25 dazu, weil dieser Absatz sie seit jeher NANNTE und")
    print("  nicht zaehlte.")
    print("  Und dieser Korpus ist NACHGEBILDET: je Datei steht im Kopf, was ergaenzt wurde.")
    print("  `dokumente/FRAGMENTE.md` bleibt der eingefrorene Bericht -- was hier gemessen")
    print("  wird, ist Gabbro an einem Programm, nicht Gabbro an einem Ausschnitt.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
