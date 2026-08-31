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

    ./instrumente/zaehle-pflichten.py              -- die Uebersicht je Fragment
    ./instrumente/zaehle-pflichten.py --zeilen     -- jede Kandidatenzeile mit FRAGMENTE.md:NNN
    ./instrumente/zaehle-pflichten.py --fragment 1 -- nur F1
"""
import re
import sys
from pathlib import Path

QUELLE = Path(__file__).resolve().parent.parent / "dokumente" / "FRAGMENTE.md"

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
        # **Every refusal in this file ends with 2, not 1** (2026-08-31). This counter joined
        # `abnahme.py` that day, so its return code is now read as a VERDICT -- and the sixth
        # requirement applies: `1` means the TREE has to change, `2` means the SETUP does.
        # Every site below says NOTHING WAS MEASURED, so every one of them is a `2`.
        sys.exit(2)
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
        sys.exit(2)

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
    # Tor definiert ist** (*„`H = 0` ueber dem Fragmentkorpus, mit `./instrumente/zaehle-pflichten.py`
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
        sys.exit(2)
    zweiter = [b for b in alle if b[1] > grenze]
    alle = [b for b in alle if b[1] < grenze]
    if len(alle) != 10:
        print(f"ABBRUCH: {len(alle)} Bloecke statt 10 VOR «F0» -- der eingefrorene Korpus "
              f"hat sich bewegt, und FRAGMENTE.md traegt einen Einfriersatz.", file=sys.stderr)
        sys.exit(2)

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


def abgesenkt(quelle=None):
    """**Which fragments have MEASURED their lowering obligation -- read out of the guard.**

    The obligation of the ten reads *"the generated C computes what the fragment says"*, and
    it is discharged by one thing: `pruefe-emission.sh` emits, compiles, **runs** and compares
    against a handwritten expectation. Whoever does that for a fragment writes a
    `lauf "fragmentN"` line into the guard.

    Until 2026-08-25 the answer sat beside it as a hand-kept list in this file's own source --
    `["F1", "F2", ...]`. **That made `H` a number somebody has to update**, and this file says
    in three other places where that leads: *a metric somebody has to keep is wrong sooner or
    later.*

    > Now it is derived: **whoever builds a differential test lowers `H`; whoever removes one
    > raises it.** An entry without a run is no longer writable.
    """
    import re
    if quelle is None:
        quelle = (Path(__file__).resolve().parent.parent
                  / "instrumente" / "pruefe-emission.sh").read_text(encoding="utf-8")
    return {f"F{m}" for m in re.findall(r'^lauf "fragment(\d+)"', quelle, re.M)}


# **The K/L split, DERIVED instead of carried forward** (2026-08-30).
#
# `PFLICHTEN.md` closes with two summary tables, and on 2026-08-30 both were wrong about the
# same thing. The column table listed eleven fragments; its own `K` column adds up to 173 and
# its `L` column to 65, and the total row beneath it read **171 / 67**. *Both readings sum to
# 238, and that is exactly why it stood: a split whose total matches is not recomputed.*
#
# One level deeper the count found the cause -- **F4 has 31 rows, not 30**: 24 `K` and seven
# `L`, while its section header carried six. So neither pair booked so far was the object.
#
# > **The split is now read off the rows.** Whoever adds an obligation moves it; whoever
# > reclassifies one moves it. *A number nobody has to keep cannot go stale.*
#
# The splitter is the load-bearing part. A markdown row may carry an ESCAPED pipe inside a
# cell (`F2`:498 writes `\|\|` for a disjunction), and a naive `split("|")` turns that row
# into nine cells and drops it. **A counter that silently skips a row reports a smaller
# population, not an error** -- the same class as the invalid mutation of 2026-08-30.
def _zellen(z):
    """Split a markdown row on UNESCAPED pipes only."""
    out, buf, i = [], "", 0
    while i < len(z):
        if z[i] == "\\" and i + 1 < len(z) and z[i + 1] == "|":
            buf += "|"
            i += 2
            continue
        if z[i] == "|":
            out.append(buf)
            buf = ""
            i += 1
            continue
        buf += z[i]
        i += 1
    out.append(buf)
    return [c.strip() for c in out]


def spalten(probe=None, still=False):
    """**Die Spalten des Handgangs -- je Fragment, aus den ZEILEN gezaehlt.**

    A row counts when its third column is `K` or `L` after the markup is stripped. **A
    struck-through class counts too** -- `~~K~~ **zu**` is a CLOSED obligation, not a
    removed one, and the summary tables have always counted it. *That is the opposite rule
    from `gap:`, and on purpose: a withdrawn gap is no obligation, a discharged obligation
    still is one.*
    """
    import re
    quelle = Path(__file__).resolve().parent.parent / "dokumente" / "PFLICHTEN.md"
    text = quelle.read_text(encoding="utf-8")
    if probe is not None:
        text = text.replace(probe[0], probe[1], 1)
    frag, je = None, {}
    for z in text.splitlines():
        # **The section must be RESET at every heading, not only set at a fragment one.**
        # Without the `else` branch every row after `# F10` -- the lowering table and the two
        # summary tables -- is still booked to F10, and the first run of this mode reported
        # `F10 16 = 14 K + 2 L` for a section with eleven rows. *A counter that never leaves
        # its last section counts the epilogue as part of it.*
        if z.startswith("# "):
            m = re.match(r"^# (F\d+)", z)
            if m:
                frag = m.group(1)
                je.setdefault(frag, {"K": 0, "L": 0})
            else:
                frag = None
        if frag is None or not z.startswith("|"):
            continue
        c = _zellen(z.strip())
        if len(c) != 6 or c[0] != "" or c[-1] != "":
            continue
        blank = re.sub(r"[^A-Za-z]", "", c[3])
        if blank.startswith("K"):
            je[frag]["K"] += 1
        elif blank.startswith("L"):
            je[frag]["L"] += 1
    k = sum(v["K"] for v in je.values())
    l = sum(v["L"] for v in je.values())
    if still:
        return k, l
    print("== Die Spalten des Handgangs, je Fragment ==")
    for f in [f"F{i}" for i in range(1, 11)]:
        v = je.get(f, {"K": 0, "L": 0})
        print(f"  {f:<4} {v['K'] + v['L']:>3} = {v['K']:>3} K + {v['L']:>3} L")
    a = len([f for f in je])
    print(f"  ---------------------------------")
    print(f"  verankert  {k + l:>3} = {k:>3} K + {l:>3} L")
    print(f"  Absenkung  {a:>3} = {a:>3} K +   0 L   eine Zeile je Fragment,")
    print(f"                                     in `The tenth event`")
    print(f"  ---------------------------------")
    print(f"  insgesamt  {k + l + a:>3} = {k + a:>3} K + {l:>3} L")
    print()
    print("**Und was das NICHT heisst:** die Klasse `K`/`L` ist ein URTEIL, das ein Mensch in")
    print("die dritte Spalte geschrieben hat -- dieses Werkzeug zaehlt sie, es faellt sie")
    print("nicht. Was es ausschliesst, ist nur das eine: dass die Summe von ihrer Spalte")
    print("abweicht. *Genau das war am 2026-08-30 der Fall, sechzehn Tage lang* (W10).")


# **What MAKES a hanging obligation: the FOURTH COLUMN, not the line.**
#
# Until 2026-08-25 this read `"gap:" in z` over the WHOLE table row -- so every row of class
# `K` counted in which the string occurred anywhere, prose included. **The docstring below
# had described the narrow rule all along** (*"whose fourth column starts with `gap:`"*);
# only the code did not keep to it.
#
# > *On 2026-08-25 a CORRECTION wrote the words `gap:`-column into its own prose, and `H`
# > rose from 10 to 11.* **A number that can be shifted by mentioning its own keyword is no
# > measure.**
#
# The markers `**`, `*`, `_` may stand in front -- the table sets every gap in bold. **`~~`
# expressly NOT:** a struck-through gap is a WITHDRAWN one, and that is exactly the shape
# the «B9» row was left in on 2026-08-25. *Whoever counts it counts a retraction as an
# obligation.*
GAP_SPALTE = re.compile(r"^(?:\*\*|\*|_)*gap:")


def haengend(probe=None, still=False, locker=False):
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
    quelle = Path(__file__).resolve().parent.parent / "dokumente" / "PFLICHTEN.md"
    text = quelle.read_text(encoding="utf-8")
    if probe is not None:
        text = text.replace(probe[0], probe[1], 1)
    frag, offen = None, {}
    for nr, z in enumerate(text.splitlines(), 1):
        m = re.match(r"^# (F\d+)", z)
        if m:
            frag = m.group(1)
        if z.startswith("|") and "gap:" in z:
            sp = [c.strip() for c in z.strip("|").split("|")]
            # `locker` is the OLD, wide rule. It survives only so the backward probe below
            # can show that the narrowing does any work at all.
            eng = len(sp) >= 4 and bool(GAP_SPALTE.match(sp[3]))
            if len(sp) >= 4 and sp[2] == "K" and (locker or eng):
                offen.setdefault(frag, []).append((nr, sp[0]))
    n_roh = sum(len(v) for v in offen.values())
    if still:
        return n_roh
    print("== Haengende Klempnereipflichten, an einer Zeile verankert ==")
    for f in sorted(offen, key=lambda x: int(x[1:])):
        stellen = ", ".join(s for _, s in offen[f])
        print(f"  {f:<4} {len(offen[f]):>2}   {stellen}")
    n = sum(len(v) for v in offen.values())
    # **Die Spalte je Fragment -- ABGELEITET statt gepflegt** (2026-08-20).
    #
    # `PFLICHTEN.md` fuehrte eine Tabelle „hanging / of which K" je Fragment. Ihre Spalte
    # summierte sich zu 33, die Summenzeile sagte 18, und die Fussnoten der Abschnitte sagten
    # ein Drittes. **Drei Register ueber derselben Sache** (W7) -- und keins davon abgeleitet.
    #
    # *Die Absenkungspflicht ist je Fragment bekannt und steht nur als eine Zeile in der
    # Tabelle:* F1-F6 und F9 sind offen, F7/F8/F10 gemessen. Damit ist die Spalte hier
    # ableitbar, und die Tabelle drueben braucht sie nicht mehr von Hand.
    ABSENKUNG_OFFEN = [f for f in [f"F{i}" for i in range(1, 11)]
                       if f not in abgesenkt()]
    print("\n  je Fragment (verankert + Absenkung):")
    for f in [f"F{i}" for i in range(1, 11)]:
        v = len(offen.get(f, []))
        a = 1 if f in ABSENKUNG_OFFEN else 0
        if v or a:
            print(f"    {f:<4} {v} + {a} = {v + a}")
    a = len(ABSENKUNG_OFFEN)
    gemessen = ", ".join(sorted(abgesenkt(), key=lambda x: int(x[1:])))
    print(f"\n  verankert       {n:>3}")
    print(f"  Absenkung       {a:>3}   eine Zeile je Fragment, in `The tenth event`;")
    print(f"                        GEMESSEN sind {gemessen}")
    print(f"  ---------------------")
    print(f"  H               {n + a:>3}")
    print()
    print("**Und was diese Zahl NICHT ist:** eine Aussage ueber Gabbro. Die zehn Fragmente")
    print("sind nach ihrer SCHWIERIGKEIT gewaehlt; `H = 0` ueber ihnen bliebe Falle 80,")
    print("solange kein Korpus daneben steht, den beim Bauen niemand angesehen hat.")


if __name__ == "__main__":
    if "--spalten" in sys.argv:
        # **The speaking probe, both ways.** An invented `L` row must raise `L` by one and
        # leave `K` alone -- otherwise the split answers something other than the rows.
        k0, l0 = spalten(still=True)
        gift = ("| 999 | Sprechprobe | L | erfunden |\n"
                "**F2: 24 obligations")
        k1, l1 = spalten(probe=("**F2: 24 obligations", gift), still=True)
        if (k1, l1) != (k0, l0 + 1):
            print(f"SPRECHPROBE GESCHEITERT: eine erfundene `L`-Zeile aendert die Spalten "
                  f"nicht wie erwartet ({k0}/{l0} -> {k1}/{l1}).", file=sys.stderr)
            sys.exit(2)
        print(f"== Sprechprobe: ok (eine erfundene `L`-Zeile hebt L von {l0} auf {l1}, "
              f"K bleibt {k1}) ==")
        # **And the escaped pipe** -- the row shape that a naive splitter drops. Without this
        # the counter would report a smaller population and look green doing it.
        gift2 = ("| 998 | Sprechprobe mit `a \\| b` in der Zelle | K | erfunden |\n"
                 "**F2: 24 obligations")
        k2, l2 = spalten(probe=("**F2: 24 obligations", gift2), still=True)
        if (k2, l2) != (k0 + 1, l0):
            print(f"SPRECHPROBE GESCHEITERT: eine Zeile mit maskierter Pipe faellt aus dem "
                  f"Zaehler ({k0}/{l0} -> {k2}/{l2}). **Dann misst er eine geschrumpfte "
                  f"Grundgesamtheit.**", file=sys.stderr)
            sys.exit(2)
        print(f"== Sprechprobe: ok (eine Zeile mit maskierter Pipe zaehlt mit: "
              f"K {k0} -> {k2}) ==\n")
        spalten()
    elif "--haengend" in sys.argv:
        # **Die Sprechprobe, in beide Richtungen** (2026-08-20, gefunden von
        # `pruefe-waechter.py`). `H` ist die Zahl, auf der K100s erstes Tor definiert ist --
        # und dieser Modus las sie aus einer handgepflegten Tabelle, ohne je zu zeigen, dass
        # er eine geaenderte Tabelle bemerkt. *Ein Waechter, der nicht rot werden kann, misst
        # nichts* (R14).
        vorher = haengend(still=True)
        # Eine erfundene `gap:`-Zeile MUSS mitzaehlen.
        gift = ("| 999 | Sprechprobe | K | **gap: erfunden** |\n"
                "**F2: 24 obligations")
        nachher = haengend(probe=("**F2: 24 obligations", gift), still=True)
        if nachher != vorher + 1:
            print(f"SPRECHPROBE GESCHEITERT: eine zusaetzliche `gap:`-Zeile aendert die Zahl "
                  f"nicht ({vorher} -> {nachher}). **Diese Zahl misst nichts.**",
                  file=sys.stderr)
            sys.exit(2)
        print(f"== Sprechprobe: ok (eine erfundene `gap:`-Zeile hebt H von {vorher} auf "
              f"{nachher}) ==")
        # **And the same probe BACKWARDS** (2026-08-25).
        #
        # The probe above shows that a REAL gap RAISES `H`. It does NOT show that a mere
        # MENTION fails to -- and that is exactly where the number slipped that day: a
        # CORRECTION wrote the words `gap:`-column into its own prose, and `H` rose from 10
        # to 11. *Nothing had been built and nothing had torn; the number had reacted to its
        # own keyword.*
        #
        # > **A number that can be shifted by mentioning its keyword is no measure** -- and
        # > `pruefe-waechter.py` demands the speaking probe expressly *"in both directions:
        # > what should fall, falls; what should not, does not."*
        #
        # **It is TWO-SIDED, or it measures nothing itself.** A backward probe that only
        # checks "H stays equal" also passes when the invented row never reaches the counter
        # at all -- the same class as a guard that selects nothing and ends green. So BOTH
        # are demanded: under the old, wide rule the row MUST count (only that makes the
        # narrowing work), under the narrow one it must NOT.
        RUECKWAERTS = [
            ("Erwaehnung im Fliesstext",
             "| 998 | die `gap:`-Spalte wird hier nur ERWAEHNT | K | closed by «B99» |\n"),
            ("zurueckgezogene Luecke, durchgestrichen",
             "| 997 | BERICHTIGT | K | **eine Richtigstellung, keine Buchung.** "
             "~~*gap: «B99» -- war falsch*~~ |\n"),
        ]
        weit_vorher = haengend(still=True, locker=True)
        for was, zeile in RUECKWAERTS:
            p_gift = ("**F2: 24 obligations", zeile + "**F2: 24 obligations")
            weit = haengend(probe=p_gift, still=True, locker=True)
            eng = haengend(probe=p_gift, still=True)
            if weit != weit_vorher + 1:
                print(f"RUECKWAERTSPROBE UNTAUGLICH ({was}): die erfundene Zeile erreicht "
                      f"den Zaehler gar nicht -- schon die WEITE Regel sieht sie nicht "
                      f"({weit_vorher} -> {weit}). **Dann belegt ein Gleichstand unter der "
                      f"engen Regel nichts.**", file=sys.stderr)
                sys.exit(1)
            if eng != vorher:
                print(f"RUECKWAERTSPROBE GESCHEITERT ({was}): eine blosse ERWAEHNUNG von "
                      f"`gap:` verstellt H ({vorher} -> {eng}). **Eine Zahl, die sich durch "
                      f"ihr eigenes Schluesselwort heben laesst, ist kein Mass.**",
                      file=sys.stderr)
                sys.exit(1)
            print(f"== Rueckwaertsprobe: ok ({was}: weit {weit_vorher} -> {weit}, "
                  f"eng {vorher} -> {eng}) ==")
        # **The same probe for the SECOND half of `H`** (2026-08-25). Since the lowering
        # column is derived from `pruefe-emission.sh`, the number rests on a second guard --
        # and *a derivation nobody has seen fail is a claim about a script.*
        gemessen = abgesenkt()
        quelle = (Path(__file__).resolve().parent.parent
                  / "instrumente" / "pruefe-emission.sh").read_text(encoding="utf-8")
        ohne = abgesenkt(quelle.replace('lauf "fragment', 'lauf "GENOMMEN'))
        if not gemessen or ohne:
            print(f"SPRECHPROBE GESCHEITERT: die Absenkungsspalte antwortet auf einen "
                  f"herausgenommenen Differenztest nicht ({sorted(gemessen)} -> "
                  f"{sorted(ohne)}). **Diese Haelfte von H misst nichts.**", file=sys.stderr)
            sys.exit(2)
        print(f"== Sprechprobe: ok (ohne die Differenztests faellt die Absenkungsspalte "
              f"von {len(gemessen)} auf 0 gemessene) ==\n")
        haengend()
    else:
        main()
