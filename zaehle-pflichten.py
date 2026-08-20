#!/usr/bin/env python3
"""Der Suchweg fuer die NEUZUWEISUNG der 74 Beweispflichten.

**Dieses Werkzeug zaehlt keine Pflichten. Es zaehlt KANDIDATENZEILEN.**

Die Unterscheidung ist der ganze Grund, dass es das Werkzeug gibt. W7 sagt: eine Zahl
ohne Suchweg gehoert nicht in den Ordner -- und fuer mechanisch erhebbare Groessen IST
der Suchweg die Liste. Was eine Zeile *behauptet*, kann ein Skript nicht entscheiden;
dass eine Zeile ueberhaupt angesehen werden muss, kann es sehr wohl.

Also die Arbeitsteilung, und sie steht so im VORAB:

    Werkzeug  ->  keine Zeile wird uebersehen
    Handgang  ->  keine Zeile wird falsch gezaehlt

Beide Zahlen werden berichtet. Die Differenz ist keine Panne, sondern das Mass dafuer,
wieviel an dieser Messung Urteil ist -- und die gehoert sichtbar, nicht verrechnet.

    ./zaehle-pflichten.py              -- die Uebersicht je Fragment
    ./zaehle-pflichten.py --zeilen     -- jede Kandidatenzeile mit FRAGMENTE.md:NNN
    ./zaehle-pflichten.py --fragment 1 -- nur F1
"""
import re
import sys
from pathlib import Path

QUELLE = Path(__file__).parent / "dokumente" / "FRAGMENTE.md"

# Die Ereignisse aus dem VORAB. A bis G sind zeilenweise erkennbar, H ist eine je
# Fragment und steht darum nicht in dieser Tabelle.
#
# **I und J sind am 2026-08-17 nachgetragen, und zwar VOR dem ersten gezaehlten
# Posten der neun uebrigen Fragmente.** Die Eichung gegen `delete_leaf` (R14, im
# VORAB angekuendigt) lief gegen die schon veroeffentlichten elf Pflichten
# (BEWEIS.md:1078) und fand drei Luecken:
#
#   1. `costs`, `effects`, `touches`, `where`, `bounded`, `progress`, `on_exceeded`,
#      `floor`, `claim` sind ebenfalls ERKLAERTE KLAUSELN und standen nicht in A.
#      Schlichter Fehler.
#   2. **Der Ruf.** `unlink(c, s)` loest die Vorbedingung des Gerufenen aus -- die
#      Pflichten 2 und 3 der veroeffentlichten Liste sitzen genau dort. -> I
#   3. **Der Zweig.** `Memory(m) => { free_region(a, m); }` traegt die Aussage, dass
#      DIESE Bedingung die richtige fuer DIESE Aenderung ist -- die Pflichten 6 bis 9
#      und 11. -> J
#
# Alle drei sind grundsaetzlich, keine Anpassung an ein Ergebnis: eine Vorbedingung
# am Rufort und ein zustandsaendernder Zweig erzeugen Beweispflichten in jeder
# Programmlogik. *Eine nach dem Ergebnis nachgezogene Regel waere R2; eine vor dem
# Lauf gegen ein veroeffentlichtes Ergebnis geeichte ist R14.*
EREIGNISSE = [
    ("A", "erklaerte Klausel",
     re.compile(r"\b(requires|ensures|maintains|invariant|axiom|progress|variant"
                r"|costs|effects|touches|where|bounded|on_exceeded|floor|claim"
                r"|assume|counterprobe|gates|measures)\b")),
    ("B", "Index",
     re.compile(r"[A-Za-z_]\w*\s*\[")),
    ("C", "beschraenkte Arithmetik",
     re.compile(r"[\w\)\]]\s*[-+*]\s*[\w\(]")),
    ("D", "Eigentumszug",
     re.compile(r"\b(own|consume|consuming|moves?|linear)\b")),
    ("E", "Sperre",
     re.compile(r"\b(lock|locks|held|acquire|release|protects|rank)\b")),
    ("F", "Ordnung",
     re.compile(r"\b(publishes|awaits|exchange|atomic|barrier|mirrors|relaxed|volatile)\b")),
    ("G", "Schleife",
     re.compile(r"\b(traverse|retry|forever|while|for)\b")),
    ("I", "Ruf",
     re.compile(r"\b[a-z_]\w*\s*\([^)]*\)\s*;?\s*$|=\s*[a-z_]\w*\s*\(")),
    ("J", "Zweig",
     re.compile(r"=>|^\s*if\b|\belse\b")),
]

# `@[33:24]` ist eine Bitlage, kein Index -- und `-- Text` ist ein Kommentar, in dem
# jedes Minuszeichen sonst als Arithmetik durchginge.
BITLAGE = re.compile(r"@\s*\[")
PFEIL = re.compile(r"->|<-|=>")


def bloecke(text):
    """Die zehn ```gabbro-Bloecke, mit ihrer Zeilennummer in FRAGMENTE.md."""
    aus, drin, start, puffer = [], False, 0, []
    for nr, zeile in enumerate(text.splitlines(), 1):
        if not drin and zeile.startswith("```gabbro"):
            drin, start, puffer = True, nr + 1, []
        elif drin and zeile.startswith("```"):
            aus.append((len(aus) + 1, start, puffer))
            drin = False
        elif drin:
            puffer.append((nr, zeile))
    if drin:
        print("ABBRUCH: ein ```gabbro-Block ist nicht geschlossen.", file=sys.stderr)
        print("  R16: die Zahl waere eine untere Schranke, keine Messung.", file=sys.stderr)
        sys.exit(1)
    return aus


def rumpf(zeile):
    """Der Code ohne seinen nachgestellten Kommentar."""
    i = zeile.find("--")
    return zeile if i < 0 else zeile[:i]


def treffer(zeile):
    """Welche Ereignisse diese Zeile ausloest. Leer heisst: nicht anzusehen."""
    ist_kommentar = zeile.lstrip().startswith("--")
    code = zeile if ist_kommentar else rumpf(zeile)
    if not code.strip():
        return [], ist_kommentar
    ohne_bitlage = BITLAGE.sub(" ", code)
    ohne_pfeil = PFEIL.sub(" ", ohne_bitlage)
    aus = []
    for kennung, _name, muster in EREIGNISSE:
        pruefling = ohne_pfeil if kennung in ("B", "C") else code
        if muster.search(pruefling):
            aus.append(kennung)
    return aus, ist_kommentar


def main():
    if not QUELLE.exists():
        print(f"ABBRUCH: {QUELLE} fehlt -- es wird NICHT null gezaehlt.", file=sys.stderr)
        sys.exit(1)

    einzeln = "--zeilen" in sys.argv
    nur = None
    if "--fragment" in sys.argv:
        nur = int(sys.argv[sys.argv.index("--fragment") + 1])

    text = QUELLE.read_text(encoding="utf-8")
    alle = bloecke(text)
    # **Die Grundgesamtheit hat sich bewegt, und das war RICHTIG** (nachgezogen 2026-08-20).
    #
    # Bis heute stand hier `len(alle) != 10 -> ABBRUCH`, und seit «F0» und «K2» sind es
    # fuenfzehn. **Damit verweigerte genau das Werkzeug die Ableitung, auf dem K100s erstes
    # Tor definiert ist** (*„`H = 0` ueber dem Fragmentkorpus, mit `./zaehle-pflichten.py`
    # neu abgeleitet"*) -- und `--haengend`, der Modus, der noch antwortete, laeuft VOR
    # dieser Stelle und liest eine handgepflegte Tabelle.
    #
    # > *Eine Zahl ohne Suchweg gehoert nicht in den Ordner* -- und der Suchweg war seit
    # > Wochen abgeschnitten, ohne dass irgendetwas rot wurde.
    #
    # Der Riegel bleibt, er zaehlt nur das Richtige: der EINGEFRORENE Fragmentkorpus sind
    # die Bloecke vor der «F0»-Ueberschrift. Was danach kommt, ist der ZWEITE Korpus -- und
    # er ist die Bedingung, unter der `H = 0` ueberhaupt etwas heisst. **Darum wird er
    # gezaehlt und nicht weggeworfen.**
    grenze = next((nr for nr, z in enumerate(text.splitlines(), 1)
                   if z.startswith("# \u00abF0\u00bb")), None)
    if grenze is None:
        print("ABBRUCH: die «F0»-Ueberschrift fehlt -- die Grenze zwischen dem eingefrorenen "
              "Korpus und dem zweiten ist nicht mehr ablesbar.", file=sys.stderr)
        sys.exit(1)
    zweiter = [b for b in alle if b[1] > grenze]
    alle = [b for b in alle if b[1] < grenze]
    if len(alle) != 10:
        print(f"ABBRUCH: {len(alle)} Bloecke statt 10 VOR «F0» -- der eingefrorene Korpus "
              f"hat sich bewegt, und FRAGMENTE.md traegt einen Einfriersatz.", file=sys.stderr)
        sys.exit(1)

    gesamt = {k: 0 for k, _, _ in EREIGNISSE}
    gesamtzeilen = 0
    print(f"== Kandidatenzeilen je Ereignis -- {QUELLE} ==")
    print(f"{'F':>3} {'Zeilen':>7}  " + "  ".join(f"{k:>3}" for k, _, _ in EREIGNISSE)
          + f"  {'Summe':>6}")
    for nummer, start, zeilen in alle:
        if nur is not None and nummer != nur:
            continue
        zaehler = {k: 0 for k, _, _ in EREIGNISSE}
        for nr, zeile in zeilen:
            gefunden, ist_kommentar = treffer(zeile)
            for k in gefunden:
                zaehler[k] += 1
            if einzeln and gefunden:
                marke = "K" if ist_kommentar else " "
                print(f"  FRAGMENTE.md:{nr:<5} {marke} [{''.join(gefunden)}] {zeile.strip()[:78]}")
        for k in zaehler:
            gesamt[k] += zaehler[k]
        gesamtzeilen += len(zeilen)
        print(f"F{nummer:<2} {len(zeilen):>7}  "
              + "  ".join(f"{zaehler[k]:>3}" for k, _, _ in EREIGNISSE)
              + f"  {sum(zaehler.values()):>6}")

    if nur is None:
        print(f"{'':>3} {gesamtzeilen:>7}  "
              + "  ".join(f"{gesamt[k]:>3}" for k, _, _ in EREIGNISSE)
              + f"  {sum(gesamt.values()):>6}")
        print()
    print()
    print(f"== Der ZWEITE Korpus: {len(zweiter)} Bloecke nach «F0» ==")
    print("  «F0» der Gleitkommakorpus; der Rest aus «K2» -- fuenf Fragmente aus FREMDER")
    print("  Autorenlinie (setpriority, acct_get, sum_mthp_stat, pid_namespace, BUG_ON),")
    print("  nachgebildet und geschnitten, nicht uebersetzt.")
    print("  **Ohne ihn ist `H = 0` Falle 80 in Reinform** -- die zehn oben sind nach ihrer")
    print("  SCHWIERIGKEIT gewaehlt, nicht zufaellig. Er zaehlt hier mit, damit die Bedingung")
    print("  im selben Werkzeug steht wie die Zahl, ueber die sie etwas sagt.")
    print()
    if False:
        print("H (Absenkung, je Fragment) : 10 -- steht nicht in der Tabelle, weil es")
        print("                                  keine Zeile trifft, sondern eine Datei.")
        print()
        print("**Das sind KANDIDATEN, keine Pflichten.** Eine Zeile mit drei Marken ist")
        print("nicht drei Pflichten, und eine Zeile ohne Marke kann eine tragen, die nur")
        print("im Kommentar steht. Die Zahl, die zaehlt, kommt aus dem Handgang -- diese")
        print("hier sorgt dafuer, dass er nichts uebersieht.")


def haengend():
    """**Die haengenden Klempnereipflichten, aus dem Handgang ABGELESEN statt fortgeschrieben.**

    Der Handgang steht in `PFLICHTEN.md` als Tabelle: je Zeile eine Pflicht, Spalte 3 die
    Klasse (`K`/`L`), Spalte 4 wodurch sie erledigt ist. **Eine haengende Pflicht ist eine,
    deren vierte Spalte mit `gap:` anfaengt** -- das ist keine Auslegung, das ist die Form,
    in der die Tabelle geschrieben wurde.

    Warum das hier dazukommt: am 2026-08-17 standen SECHS Zeilen als `gap:` da, die in den
    Summen laengst geschlossen waren (K100.1 buchte zwei nach Logik um, K100.2 drei in die
    Axiomschicht, «B22» eine). *Die Summe wurde gepflegt, die Quelle nicht* -- und damit war
    die Zahl nicht mehr aus ihrem Suchweg ableitbar.

    > **W7 sagt es andersherum, und das ist derselbe Satz:** eine Zahl ohne Suchweg gehoert
    > nicht in den Ordner. Eine Zahl, deren Suchweg ihr widerspricht, ist schlimmer -- sie
    > SIEHT belegt aus.
    """
    import re
    quelle = Path(__file__).parent / "dokumente" / "PFLICHTEN.md"
    frag, offen = None, {}
    for nr, z in enumerate(quelle.read_text(encoding="utf-8").splitlines(), 1):
        m = re.match(r"^# (F\d+)", z)
        if m:
            frag = m.group(1)
        if z.startswith("|") and "gap:" in z:
            sp = [c.strip() for c in z.strip("|").split("|")]
            if len(sp) >= 4 and sp[2] == "K":
                offen.setdefault(frag, []).append((nr, sp[0]))
    print("== Haengende Klempnereipflichten, an einer Zeile verankert ==")
    for f in sorted(offen, key=lambda x: int(x[1:])):
        stellen = ", ".join(s for _, s in offen[f])
        print(f"  {f:<4} {len(offen[f]):>2}   {stellen}")
    n = sum(len(v) for v in offen.values())
    print(f"\n  verankert       {n:>3}")
    print( "  Absenkung         7   F1-F6 und F9 -- eine Zeile fuer neun, in")
    print( "                        `The tenth event`; F7/F8/F10 sind gemessen")
    print(f"  ---------------------")
    print(f"  H               {n + 7:>3}")
    print()
    print("**Und was diese Zahl NICHT ist:** eine Aussage ueber Gabbro. Die zehn Fragmente")
    print("sind nach ihrer SCHWIERIGKEIT gewaehlt; `H = 0` ueber ihnen bliebe Falle 80,")
    print("solange kein Korpus daneben steht, den beim Bauen niemand angesehen hat.")


if __name__ == "__main__":
    if "--haengend" in sys.argv:
        haengend()
    else:
        main()
