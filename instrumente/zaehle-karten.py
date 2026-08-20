#!/usr/bin/env python3
"""**Zwei Blicke auf dieselbe Karte, und nur einer war modulbewusst -- wie viele gibt es noch?**

Am 2026-08-17 fiel eine Giftprobe nicht, die fallen musste. Die Ursache: `typ_von_ort` schlug
den globalen Traeger ueber `suche` nach (modulbewusst, mit Kandidatenliste), `index_pruefen`
aber mit einem blanken `globale.get(...)`. **In jedem `module`-Block traf der zweite nie**, und
`M103` schwieg fuer jede Tabelle, die ueber ihren globalen Namen adressiert wird.

Behoben und mit Gift 76 belegt. **Was blieb, war die allgemeine Frage** -- und sie stand
seither als Satz im TODO, mit einer Zahl daneben, die niemand nachrechnen konnte:

> *„Gezaehlt: 13 direkte `.get(`-Blicke auf die Karten in `umgebung.rs`."*

**Die Zahl war 13 und ist heute 35** (2026-08-20). Nicht, weil jemand zweiundzwanzig neue
geschrieben haette, sondern weil `.contains_key(` denselben Blick tut und nie mitgezaehlt
wurde -- *eine Zaehlung, die eine der beiden Formen nicht kennt, misst ihre eigene Leseweite*
(W16).

    ./instrumente/zaehle-karten.py [--stellen]

DAS MASS
--------
`Umgebung` fuehrt Karten von einem QUALIFIZIERTEN Namen auf etwas. Der modulbewusste Weg
dorthin ist `suche(...)`: er baut aus `von` und `pfad` eine Kandidatenliste (eigenes Modul,
jedes umgebende, jede `use`-Zeile) und probiert sie der Reihe nach. **Jeder Blick, der die
Karte direkt befragt, hat diese Liste nicht** -- er trifft nur, wenn der Name schon
vollqualifiziert dasteht.

**Und was das NICHT heisst:** ein direkter Blick ist kein Fehler. Wo der Schluessel aus einer
Deklaration stammt, die selbst schon qualifiziert ist, trifft er richtig. *Diese Zaehlung
findet KANDIDATEN, sie spricht keinen frei und klagt keinen an* (W10) -- wie
`zaehle-narrow.py` und aus demselben Grund: was sie nicht entscheiden kann, kippt sie in die
Spalte, die Arbeit macht.
"""
import pathlib
import re
import sys

W = pathlib.Path(__file__).resolve().parent.parent
SRC = W / "crates" / "gabbro-check" / "src"

# **Die gebuchte Marke.** Eine Ratsche, keine Zielzahl: sie darf fallen, nicht steigen. Ein
# neuer direkter Blick ist eine neue Stelle, an der `M103` in einem `module` schweigen kann.
#
# **35/31 -> 36/32 am 2026-08-20**, und die Ratsche hat den Schritt gemeldet, bevor jemand
# hinsah. Die neue Stelle ist `emit.rs:239` (`verbundwert`): sie liest den erklaerten
# Rueckgabetyp des Gerufenen, damit ein `let` OHNE Annotation als Verbund erkannt wird.
# *Sie erbt das Verhalten der Datei* -- `wert_ctyp` schlaegt zwoelf Zeilen weiter unten
# dieselbe Karte genauso nach, und `emit::Namen` ist ueberhaupt nach dem KURZEN Namen
# geschluesselt. **Der Erzeuger ist damit an dieser Karte durchgehend nicht modulbewusst**,
# und das ist ein Posten dieses Zaehlers, kein Nebenbefund dieser einen Zeile.
MARKE_DIREKT = 36
MARKE_UNQUALIFIZIERT = 32

# **Modulbewusst von Hand**: der Blick steht in einer Kandidatenschleife. Das ist der eine
# Fall, in dem ein direkter `.get(` richtig ist, ohne durch `suche` zu gehen.
BEWUSST = re.compile(r"kandidaten|find_map\(\|k\|")


def blicke(text, karten):
    """Ein Blick auf eine Karte: `.<karte>.get(` oder `.<karte>.contains_key(`.

    **Beide, seit 2026-08-20** -- `contains_key` tut denselben Blick und stand in keiner
    Zaehlung.
    """
    for i, z in enumerate(text.split("\n"), 1):
        for k in karten:
            for m in re.finditer(r"\.%s\s*\.\s*(get|contains_key)\s*\(" % re.escape(k), z):
                yield i, k, m.group(1), z.strip()


def karten_von(text):
    """Die Karten der `Umgebung` -- und welche davon ausserhalb ueberhaupt sichtbar sind."""
    alle = re.findall(r"^\s*(?:pub )?([a-z_]+): HashMap<", text, re.M)
    oeffentlich = re.findall(r"^\s*pub ([a-z_]+): HashMap<", text, re.M)
    return alle, oeffentlich


def messe():
    u = (SRC / "umgebung.rs").read_text(encoding="utf-8")
    alle, oeffentlich = karten_von(u)
    stellen = []
    dateien = 0
    for p in sorted(SRC.glob("*.rs")):
        if p.name == "umgebung.rs":
            continue
        t = p.read_text(encoding="utf-8")
        dateien += 1
        zeilen = t.split("\n")
        for nr, k, art, z in blicke(t, oeffentlich):
            umfeld = "\n".join(zeilen[max(0, nr - 3):nr])
            stellen.append((p.name, nr, k, art, bool(BEWUSST.search(umfeld)), z[:74]))
    return alle, oeffentlich, dateien, stellen


def sprechprobe():
    """R14, in beide Richtungen -- an einer ERFUNDENEN Quelle.

    *Ein Zaehler, der nur die eigenen Dateien liest, misst, wie gut sie zu ihm passen.*
    """
    karten = karten_von("    pub erfunden: HashMap<String, u8>,\n")[1]
    gift = list(blicke("        if u.erfunden.get(&n).is_some() {", karten))
    gift2 = list(blicke("        if u.erfunden.contains_key(&n) {", karten))
    sauber = list(blicke("        if u.suche_global(von, &n).is_some() {", karten))
    return karten == ["erfunden"], len(gift) == 1, len(gift2) == 1, not sauber


def main():
    k_ok, g_ok, g2_ok, s_ok = sprechprobe()
    print("== Sprechprobe des Zaehlers ==")
    print("  Karte erkannt:            %s" % ("ja" if k_ok else "NEIN"))
    print("  direkter `.get(` faellt:  %s" % ("ja" if g_ok else "NEIN"))
    print("  `.contains_key(` faellt:  %s" % ("ja" if g2_ok else "NEIN"))
    print("  Weg ueber `suche` frei:   %s" % ("ja" if s_ok else "NEIN"))
    if not (k_ok and g_ok and g2_ok and s_ok):
        print("== KARTEN: der Zaehler misst nicht ==")
        return 1

    alle, oeffentlich, dateien, stellen = messe()
    unqual = [s for s in stellen if not s[4]]
    print()
    print("== %d Karten in `umgebung.rs`, %d davon oeffentlich, %d Passdateien gelesen =="
          % (len(alle), len(oeffentlich), dateien))
    print("   direkte Blicke            %3d   (`.get(` und `.contains_key(`)" % len(stellen))
    print("   davon modulbewusst        %3d   in einer Kandidatenschleife"
          % (len(stellen) - len(unqual)))
    print("   davon UNQUALIFIZIERT      %3d   trifft nur einen vollqualifizierten Namen"
          % len(unqual))
    je_karte = {}
    for _, _, k, _, _, _ in stellen:
        je_karte[k] = je_karte.get(k, 0) + 1
    print("   je Karte: " + ", ".join("%s %d" % (k, n)
                                      for k, n in sorted(je_karte.items(), key=lambda x: -x[1])))
    if "--stellen" in sys.argv:
        print()
        for datei, nr, k, art, bewusst, z in stellen:
            print("   %-8s %s:%d  .%s.%s(   %s"
                  % ("bewusst" if bewusst else "UNQUAL", datei, nr, k, art, z))

    print()
    if len(stellen) > MARKE_DIREKT or len(unqual) > MARKE_UNQUALIFIZIERT:
        print("== KARTEN: %d direkte Blicke (%d unqualifiziert) gegen die Marke %d / %d =="
              % (len(stellen), len(unqual), MARKE_DIREKT, MARKE_UNQUALIFIZIERT))
        print("   **Die Marke ist eine Ratsche, keine Zielzahl.** Jeder neue direkte Blick ist")
        print("   eine neue Stelle, an der eine Pruefung in einem `module`-Block schweigen")
        print("   kann -- genau die Gestalt des Lochs in `M103` vom 2026-08-17.")
        return 1
    print("== KARTEN: %d direkte Blicke, %d unqualifiziert -- keine neue =="
          % (len(stellen), len(unqual)))
    print("   Und was das NICHT heisst: ein direkter Blick ist kein Fehler. Wo der Schluessel")
    print("   aus einer schon qualifizierten Deklaration stammt, trifft er richtig. Diese")
    print("   Zaehlung findet KANDIDATEN -- sie verpflichtet, sie spricht nicht frei (W10).")
    print("   **Wie viele der %d in einem `module` danebengreifen, ist ungemessen** und"
          % len(unqual))
    print("   braeuchte je Stelle eine Giftdatei mit `module`-Block.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
