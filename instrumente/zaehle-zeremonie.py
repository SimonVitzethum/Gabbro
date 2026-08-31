#!/usr/bin/env python3
"""**Die Zeremonie des Korpus, gemessen -- Stufe 2, Ziel 3 bekommt seine erste Zahl.**

Von den vier Zielen hatte *„moeglichst gut nutzbar"* als einziges keine. Ohne eine ist es
eine Meinung -- und *„keine Klempnerei beim Endnutzer"* ist eine Nutzbarkeitsaussage.

    ./instrumente/zaehle-zeremonie.py [--je-datei]

DIE ZWEI ACHSEN, UND WARUM SIE GETRENNT BLEIBEN
-----------------------------------------------
Ein Nutzbarkeitsmass wird sofort zum Optimierungsziel. Faellt es unkalibriert, faellt als
erstes das Billigste -- `effects`, `costs`, die Paarungsklauseln. **Genau der Gegenstand der
Sprache.** Darum traegt `gabbro zeremonie` seine Kalibrierung mit:

    ACHSE 1, gemessen    steht diese Tatsache ein ZWEITES Mal in dieser Einheit?
    ACHSE 2, erklaert    darf die Zahl sinken? -- je Regel ein Ja/Nein MIT GRUND

*Achse 1 ist mechanisch, Achse 2 ist eine Entscheidung und steht als eine da* (W19).

DIE SPRECHPROBE IST HIER SCHAERFER ALS SONST
--------------------------------------------
Der Korpus meldete beim ersten Lauf **null redundante Stellen**. Das ist entweder ein
sauberer Korpus oder ein blindes Werkzeug, und der Unterschied ist von aussen nicht zu sehen
-- **Erfolg ohne Arbeit** (W17). Deshalb pruefen wir nicht eine Regel, sondern **jede**:

> **Eine Regel der Tafel, die nirgends einen Treffer hat, ist selbst ein Befund.**
> Die textuelle Fassung von W11, angewandt auf die Regeln statt auf die Muster.

Was der Korpus nicht ausloest, loest die Probe aus -- und was auch die Probe nicht ausloest,
steht als Fund im Bericht. *Eine Regel ohne Treffer misst nichts und sagt es dann nicht.*
"""
import pathlib
import re
import subprocess
import sys

W = pathlib.Path(__file__).resolve().parent.parent
BIN = W / "target" / "debug" / "gabbro"
FRIST = 300

# **Zwei Grundgesamtheiten, und sie bleiben getrennt.** Die Beispiele sind fuer die Sprache
# geschrieben, die drei Stuecke in `messung/` sind ECHTER CODE gegen `../caprock-messbasis`.
# *Eine Quote ueber beiden zusammen verstuende die Frage falsch* -- Ziel 3 fragt, was ein
# Nutzer schreiben muss, nicht was ein Beispiel vorfuehrt (W11: jede Quote nennt ihr N).
LEHRKORPUS = sorted((W / "beispiele").glob("*.gab")) + sorted(
    (W / "messung" / "fragmente").glob("F*.gab")
)
ECHTKORPUS = sorted((W / "messung" / "treiber").glob("*.gab")) + sorted(
    (W / "messung" / "caprock").glob("*.gab")
)
KORPUS = LEHRKORPUS

# **Die Probe.** Sie loest jede Regel aus, die der Korpus nicht ausloest -- und sie steht
# hier statt in `beispiele/`, weil sie absichtlich schlecht geschrieben ist. Ein Beispiel
# soll vorbildlich sein; eine Probe soll treffen.
PROBE = """module zeremonieprobe {

const N : u32 = 64;

table T count N {
    slot { a : u32, }
}

impl fn zwei(p : u32 in 0 ..< N, t : ptr<normal, r> T) -> u32
    requires p < N, p < N
    ensures result <= 4294967295, result <= 4294967295
    effects { reads t, reads t }
    costs <= 16 ops
{
    let x : u32 = t.slots[p].a;
    let y : u32 = x;
    return y;
}

}
"""


def lauf(*args):
    """Ein Lauf mit Frist. **Ohne sie meldet ein Haenger sich als „laeuft noch"** (W17)."""
    befehl = [str(BIN)] + list(args)
    if not BIN.is_file():
        print(f"ABBRUCH: {BIN} fehlt -- gebaut wird auf ki-pc-fisch-101, siehe CLAUDE.md.",
              file=sys.stderr)
        sys.exit(2)
    try:
        return subprocess.run(befehl, cwd=W, capture_output=True, text=True, timeout=FRIST)
    except subprocess.TimeoutExpired:
        print(f"ABBRUCH: `gabbro {' '.join(args)}` ueberschritt {FRIST} s -- "
              "es wurde NICHTS gemessen.", file=sys.stderr)
        sys.exit(2)


def tafel():
    """Die Regeln, wie das Werkzeug sie selbst nennt. **Nicht hier nachgeschrieben** --
    zwei Register ueber derselben Sache laufen auseinander (W7)."""
    r = lauf("zeremonie", "--tafel")
    if r.returncode != 0 or "may fall" not in r.stdout:
        print("ABBRUCH: `gabbro zeremonie --tafel` lief nicht -- die Kalibrierung ist "
              "unbekannt, und ohne sie sagt keine Zahl etwas.", file=sys.stderr)
        sys.exit(2)
    regeln = {}
    kennung = None
    for z in r.stdout.splitlines():
        m = re.match(r"^  ([ART]\d+)\s+(.*)$", z)
        if m:
            kennung, regeln[m.group(1)] = m.group(1), {"was": m.group(2)}
            continue
        m = re.match(r"^\s+may fall:\s+(yes|NO)\s*$", z)
        if m and kennung:
            regeln[kennung]["faellt"] = m.group(1) == "yes"
            continue
        m = re.match(r"^\s+because:\s+(\S.*)$", z)
        if m and kennung:
            regeln[kennung]["grund"] = m.group(1)
    return regeln


def messe(dateien):
    """(Stellen je Regel, gemessene Dateien, abgelehnte Dateien)."""
    r = lauf("zeremonie", "--je-stelle", *[str(p) for p in dateien])
    gemessen = r.stdout.count("-- Ceremony register:")
    abgelehnt = r.stderr.count("has errors -- no count") + r.stderr.count("not readable")
    treffer = {}
    for m in re.finditer(r"^     \[([ART]\d+)\]", r.stdout, re.M):
        treffer[m.group(1)] = treffer.get(m.group(1), 0) + 1
    return treffer, gemessen, abgelehnt


def main():
    regeln = tafel()
    if not regeln:
        print("ABBRUCH: die Kalibriertafel ist leer.", file=sys.stderr)
        # **Every refusal in this file ends with 2, not 1** (2026-08-31). This counter joined
        # `abnahme.py` that day, so its return code is now read as a VERDICT -- and the sixth
        # requirement applies: `1` means the TREE has to change, `2` means the SETUP does.
        # Every site below says NOTHING WAS MEASURED, so every one of them is a `2`.
        return 2

    # **Jede Regel braucht einen Grund.** Ein Nein ohne Satz waere ein Machtwort, und ein Ja
    # ohne Satz waere eine Einladung.
    ohne_grund = [k for k, v in sorted(regeln.items()) if not v.get("grund")]
    if ohne_grund:
        print(f"FUND: {len(ohne_grund)} Regeln ohne Grund -- {', '.join(ohne_grund)}",
              file=sys.stderr)
        return 1

    treffer, gemessen, abgelehnt = messe(KORPUS)
    if gemessen == 0:
        print("ABBRUCH: keine einzige Datei gemessen -- das ist KEINE Zeremonie von null.",
              file=sys.stderr)
        return 2

    # ---- Sprechprobe: was der Korpus nicht ausloest, muss die Probe ausloesen -------------
    probe = W / "beispiele" / "_zeremonieprobe.gab"
    probe.write_text(PROBE, encoding="utf-8")
    try:
        p_treffer, p_gemessen, _ = messe([probe])
    finally:
        probe.unlink()
    if p_gemessen != 1:
        print("SPRECHPROBE GESCHEITERT: die Probe lief nicht durch -- ohne sie ist "
              "„0 redundant“ ununterscheidbar von einem blinden Werkzeug.", file=sys.stderr)
        return 2

    stumm = sorted(k for k in regeln if k not in treffer and k not in p_treffer)
    print("== Sprechprobe ==")
    print(f"  {len(regeln)} Regeln in der Tafel, jede mit Grund")
    print(f"  Korpus loest {len(treffer)} aus, die Probe zusaetzlich "
          f"{len(set(p_treffer) - set(treffer))}")
    if stumm:
        print(f"  STUMM: {', '.join(stumm)} -- eine Regel ohne Treffer misst nichts,")
        print("         und dass sie nichts misst, sieht wie ein sauberer Korpus aus.")
    else:
        print("  keine stumme Regel")
    print()

    print(f"== Die Zeremonie des Korpus: {gemessen} Dateien gemessen, "
          f"{abgelehnt} abgelehnt ==")
    spalten = {"A": "ableitbar", "R": "redundant", "T": "tragend"}
    summe = faellt = 0
    for buchstabe, name in spalten.items():
        eigene = {k: v for k, v in sorted(treffer.items()) if k.startswith(buchstabe)}
        n = sum(eigene.values())
        summe += n
        print(f"  {name:<12} {n:>5}")
        if "--je-datei" in sys.argv or True:
            for k, v in eigene.items():
                darf = "ja" if regeln[k]["faellt"] else "NEIN"
                print(f"     {k:<4} {v:>5}   darf sinken: {darf}")
                if regeln[k]["faellt"]:
                    faellt += v
    print()
    print(f"  {faellt} von {summe} Stellen duerfen sinken")
    print()

    # ---- Der ECHTE Code, getrennt gezaehlt ------------------------------------------
    e_treffer, e_gemessen, e_abgelehnt = messe(ECHTKORPUS)
    e_summe = sum(e_treffer.values())
    e_faellt = sum(v for k, v in e_treffer.items() if regeln[k]["faellt"])
    e_zeilen = sum(len(p.read_text(encoding="utf-8").splitlines()) for p in ECHTKORPUS)
    l_zeilen = sum(len(p.read_text(encoding="utf-8").splitlines()) for p in LEHRKORPUS)
    print(f"== Echter Code: {e_gemessen} Dateien gemessen, {e_abgelehnt} abgelehnt ==")
    for buchstabe, name in spalten.items():
        eigene = {k: v for k, v in sorted(e_treffer.items()) if k.startswith(buchstabe)}
        print(f"  {name:<12} {sum(eigene.values()):>5}"
              + ("   " + " ".join(f"{k} {v}" for k, v in eigene.items()) if eigene else ""))
    # **Eine eigene Wortmarke**, damit das Zahlenregister die beiden Quoten unterscheiden
    # kann: zwei gleichlautende Zeilen ueber zwei Grundgesamtheiten sind W7 im Kleinen.
    print(f"  echter Code: {e_faellt} von {e_summe} Stellen duerfen sinken")
    print()
    print("  Und der Vergleich ist der eigentliche Befund:")
    print(f"    Lehrkorpus   {100*faellt/summe:>5.1f} % duerfen sinken   "
          f"({summe} Stellen auf {l_zeilen} Zeilen)")
    print(f"    echter Code  {100*e_faellt/e_summe:>5.1f} % duerfen sinken   "
          f"({e_summe} Stellen auf {e_zeilen} Zeilen)")
    print(f"    Dichte      Lehrkorpus {100*summe/l_zeilen:.1f}, echter Code "
          f"{100*e_summe/e_zeilen:.1f} Stellen je 100 Zeilen")
    print("  Im echten Code ist der ableitbare Anteil mehr als doppelt so hoch -- und er")
    print("  besteht AUSSCHLIESSLICH aus A4, der Wirkungszeile, die ein Gerufener ohnehin")
    print("  erklaert. *Ein Beispiel ruft wenig; ein Treiber ruft staendig.*")
    print()

    if "--je-datei" in sys.argv:
        print("== Je Datei ==")
        for p in LEHRKORPUS + ECHTKORPUS:
            t, g, _ = messe([p])
            if g:
                print(f"  {p.relative_to(W)!s:<44} {sum(t.values()):>4}")
        print()

    print("== Und was das NICHT heisst ==")
    print("  `ableitbar` heisst: dieselbe Tatsache steht mechanisch lesbar ein zweites Mal")
    print("  in DIESER Einheit, und das Register nennt wo. Es heisst NICHT „weg damit“ --")
    print("  ob eine ableitbare Zeile trotzdem dastehen soll, ist Achse 2 und eine")
    print("  ENTSCHEIDUNG. Sie steht in `gabbro zeremonie --tafel`, je Regel mit Grund.")
    print()
    print("  Und die Doktrinzeile, wie bei den drei anderen Zaehlern:")
    print("  was 0 Befunde hat, ist nicht nutzbar, sondern UNGEMESSEN.")
    print()
    print(f"== Arbeitsmenge: {gemessen + e_gemessen} Dateien, {summe + e_summe} Stellen, "
          f"{len(regeln)} Regeln, 1 Probe ==")
    return 1 if stumm else 0


if __name__ == "__main__":
    sys.exit(main())
