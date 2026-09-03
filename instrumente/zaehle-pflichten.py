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


# **The lowering column reads the RUN, not the source line** (2026-08-31).
# ----------------------------------------------------------------------
# Until today this stood here:
#
#     return {f"F{m}" for m in re.findall(r'^lauf "fragment(\d+)"', quelle, re.M)}
#
# -- the answer read off `pruefe-emission.sh`'s OWN SOURCE TEXT, at the bare presence of a
# `lauf` line. **Not at whether the run holds.** On 2026-08-31 `F06` stood at `N043`
# (`measures eich`, a carrier that is in no excerpt): it no longer checked, no longer
# emitted, its differential test was gone, the guard was RIGHTLY red -- **and `H` said 4.**
#
# > *Same family as `W25`, one step further: there a correct number carried an UNMEASURED
# > LABEL, here a number carried an UNMEASURED PRECONDITION.* While the line stands, the run
# > may fall and the number stays.
#
# The guard now answers the question itself (`--absenkung`): it runs only the six fragment
# differential tests, a fallen one is a RESULT and not an abort, and each leaves one verdict
# line behind -- the two tokens are the regular expressions in `_messe_absenkung` below.
# Measured 2026-08-31 on `ki-pc-fisch-101`: **1,7 s** -- the `cargo run` calls hit a warm
# build, and stages 9 and 10 do not run.
#
# **And the source line is still read -- as a CROSS-CHECK, not as the answer.** Every
# `lauf "fragmentN"` in the guard must come back with a verdict; a line without one means
# the run did not reach it, and then nothing was measured (a `2`, not a number).
FRIST_ABSENKUNG = 300  # Sekunden. Ein Waechter ohne Frist meldet einen Haenger als „laeuft".
_ABSENKUNG = None


def absenkung(neu_messen=False):
    """**Der gemessene Absenkungsstand: `(haelt, faellt, ausgabe)`.**

    Der Waechter wird EINMAL je Prozess gerufen und die Antwort gemerkt -- `haengend()` fragt
    sie mehrfach, und zwei Laeufe desselben Waechters ueber demselben Baum sind kein zweites
    Mass, sondern zweimal dieselbe Wanduhr.
    """
    global _ABSENKUNG
    if _ABSENKUNG is None or neu_messen:
        _ABSENKUNG = _messe_absenkung()
    return _ABSENKUNG


def _absage(*zeilen):
    for z in zeilen:
        print(z, file=sys.stderr)
    # **Every refusal here ends with `2`**: nothing was measured, and then the SETUP has
    # to change and not the tree.
    sys.exit(2)


def _messe_absenkung():
    import re
    import subprocess
    w = Path(__file__).resolve().parent.parent
    waechter = w / "instrumente" / "pruefe-emission.sh"
    if not waechter.is_file():
        _absage(f"ABBRUCH: {waechter} fehlt -- die Absenkung wurde NICHT gemessen.")
    try:
        r = subprocess.run([str(waechter), "--absenkung"], cwd=w, capture_output=True,
                           text=True, timeout=FRIST_ABSENKUNG)
    except subprocess.TimeoutExpired:
        _absage(f"ABBRUCH: der Waechter ueberschreitet die Frist ({FRIST_ABSENKUNG} s) -- "
                f"ein Haenger sieht aus wie „laeuft noch“, nicht wie ein Befund.")
    except OSError as e:
        _absage(f"ABBRUCH: der Waechter laesst sich nicht starten ({e}) -- es wurde "
                f"NICHTS gemessen.")
    if r.returncode != 0:
        _absage(f"ABBRUCH: `pruefe-emission.sh --absenkung` endet mit {r.returncode} -- "
                f"in diesem Modus ist ein GEFALLENER Durchstich ein Ergebnis, also hat der "
                f"Waechter selbst NICHTS gemessen.",
                *(r.stdout.splitlines()[-8:] + r.stderr.splitlines()[-8:]))
    haelt = set(re.findall(r'^DURCHSTICH fragment(\d+) HAELT\b', r.stdout, re.M))
    faellt = set(re.findall(r'^DURCHSTICH fragment(\d+) FAELLT\b', r.stdout, re.M))
    # **The speech test lives in the guard and is DEMANDED here.** A counter that takes a
    # tool's answer without that tool ever having been able to answer wrongly has passed the
    # assurance on, not checked it (R14).
    if not re.search(r'^SPRECHPROBE ok\b', r.stdout, re.M):
        _absage("ABBRUCH: der Waechter belegt seine eigene Falsifizierbarkeit nicht -- "
                "die Zeile `SPRECHPROBE ok` fehlt. **Dann misst DURCHSTICH ... HAELT nichts.**")
    # **And the cross-check against the source text, in the direction that is left.** The
    # source no longer says WHAT is lowered -- but it says how many verdicts have to come
    # back. A `lauf` line without one means the run never reached it.
    geschrieben = set(re.findall(r'^lauf "fragment(\d+)"',
                                 waechter.read_text(encoding="utf-8"), re.M))
    if geschrieben != haelt | faellt:
        _absage(f"ABBRUCH: der Waechter traegt {sorted(geschrieben)} als Fragmentlaeufe und "
                f"urteilt ueber {sorted(haelt | faellt)}. **Eine `lauf`-Zeile ohne Urteil "
                f"heisst, dass der Lauf nicht bis dorthin gekommen ist** -- es wurde nicht "
                f"weniger abgesenkt, es wurde weniger GEMESSEN.")
    if not geschrieben:
        _absage("ABBRUCH: der Waechter traegt keinen einzigen Fragmentlauf -- eine leere "
                "Grundgesamtheit ist die billigste Absage, und sie wird hier nicht als "
                "„nichts offen“ gebucht.")
    return ({f"F{m}" for m in haelt}, {f"F{m}" for m in faellt}, r.stdout)


def abgesenkt():
    """Die Fragmente, deren Durchstich HAELT -- gemessen, nicht abgelesen."""
    return absenkung()[0]


# **The lowering column is TWO registers, and until 2026-09-04 it was one** (`K100.1`).
# ------------------------------------------------------------------------------------
# `PLAN.md` says it of itself, in the very paragraph that names this phase: *"Die
# lowering column counts «Gabbro cannot do that» and «this text is not a program»
# in one number."* `K100.1` did the same separation one level down -- three
# hand-written `narrow`s, of which only ONE was plumbing -- and it is the precedent
# this follows, down to the shape of its gate: *a yardstick that does not tell a
# check from a rite measures the wrong thing.*
#
# THE CRITERION, and it is stated so that it CAN come out the other way
# ---------------------------------------------------------------------
# **A plumbing obligation is one that Gabbro's own machinery can discharge without changing
# what the program says** -- it falls to a change under `crates/` alone: no new source word,
# no new grammar production, no edit to the frozen excerpt.
#
# For a LOWERING obligation that question has a mechanical answer, and this is it:
#
#     `gabbro pruefe F` == 0 errors  ->  the language ACCEPTS the text and only the
#                                        generator is missing. Write the emitter arm and
#                                        the obligation is discharged. **PLUMBING.**
#     `gabbro pruefe F`  > 0 errors  ->  the checker refuses the text before the emitter is
#                                        ever reached. There is no arm to write, because
#                                        there is no accepted input to lower. **NOTATION.**
#
# **Calibration -- it reproduces the nine piercings and does not invent a tenth.** F1, F5
# and F9 checked clean and did not lower; all three were discharged on 2026-09-03 by emitter
# code (`D19`-`D22`), which is what "plumbing" has to mean if the word means anything. This
# rule would have called all three plumbing, and all three were.
#
# **What would refute it, named in advance:** a fragment that checks clean while its
# differential test does not hold lands in `klempnerei` and RAISES `H`. That is not
# hypothetical -- it is the state F1, F5 and F9 were in on 2026-09-02, and it is the state
# `F03` returns to the moment someone repairs its eighteen refusals. *A criterion that can
# only subtract is not a criterion*, and the speaking probe below drives exactly that case
# through the classifier, in both directions.
#
# **What this does NOT say.** A notation-blocked lowering is not discharged, not excused and
# not smaller. It is booked where `K100.3` books its kind -- in the «B» register -- and it
# leaves `H` because `H` counts *Klempnerei*, and a gap that costs a source word is not
# plumbing under the definition `K100` itself runs on.
FRIST_PRUEFE = 120  # seconds per fragment. Same reason as `FRIST_ABSENKUNG`.
_BEFUND = re.compile(r":\s*\d+ items?, (\d+) errors?, \d+ hints?\s*$", re.M)


def _pruefe_fehler(quelle):
    """The error count `gabbro pruefe` reports over ONE file -- run, not read.

    Refuses with `2` if the checker cannot be run or prints no verdict at all: an unmeasured
    file must not pass for a clean one, which is the direction this classification would
    fail in silently.
    """
    import subprocess
    w = Path(__file__).resolve().parent.parent
    try:
        r = subprocess.run(
            ["cargo", "run", "-q", "--manifest-path", str(w / "Cargo.toml"),
             "--bin", "gabbro", "--", "pruefe", str(quelle)],
            cwd=w, capture_output=True, text=True, timeout=FRIST_PRUEFE)
    except subprocess.TimeoutExpired:
        _absage(f"ABBRUCH: `gabbro pruefe {quelle.name}` ueberschreitet die Frist "
                f"({FRIST_PRUEFE} s) -- ein Haenger sieht aus wie „laeuft noch“.")
    except OSError as e:
        _absage(f"ABBRUCH: `gabbro pruefe` laesst sich nicht starten ({e}) -- es wurde "
                f"NICHTS gemessen.")
    m = _BEFUND.search(r.stdout + r.stderr)
    if m is None:
        _absage(f"ABBRUCH: `gabbro pruefe {quelle.name}` nennt keinen Befund "
                f"(`N items, M errors, K hints`). **Dann waere die Einordnung der "
                f"Absenkungsspalte geraten und nicht gemessen.**",
                *(r.stdout.splitlines()[-6:] + r.stderr.splitlines()[-6:]))
    return int(m.group(1))


def absenkungsklasse(sonde=None, locker=False):
    """**The open lowering obligations, split into the two registers.**

    Returns `(klempnerei, notation, fehlerzahl)`: the fragments whose lowering a generator
    can discharge, those the checker refuses before the generator is reached, and the error
    count per open fragment.

    `sonde` is the speaking probe's handle -- `(name, pfad)` is treated as an eleventh
    fragment with no holding differential test, so a case can be driven through the
    classifier without touching the tree. `locker` is the OLD, undivided rule and survives
    only so the probe can show that the division does any work at all.
    """
    wurzel = Path(__file__).resolve().parent.parent / "messung" / "fragmente"
    offen = [(f, wurzel / f"F{int(f[1:]):02d}.gab")
             for f in [f"F{i}" for i in range(1, 11)] if f not in abgesenkt()]
    if sonde is not None:
        offen.append(sonde)
    klempnerei, notation, fehlerzahl = [], [], {}
    for name, quelle in offen:
        n = _pruefe_fehler(quelle)
        fehlerzahl[name] = n
        if n == 0 or locker:
            klempnerei.append(name)
        else:
            notation.append(name)
    return klempnerei, notation, fehlerzahl


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
    # **And the open ones are SPLIT since 2026-09-04** -- see `absenkungsklasse` above for
    # the criterion and for what would have refuted it. Only the plumbing half counts in `H`.
    klempnerei, notation, fehlerzahl = absenkungsklasse()
    print("\n  je Fragment (verankert + Absenkung):")
    for f in [f"F{i}" for i in range(1, 11)]:
        v = len(offen.get(f, []))
        a = 1 if f in klempnerei else 0
        if v or a:
            print(f"    {f:<4} {v} + {a} = {v + a}")
    a = len(klempnerei)
    haelt, faellt, _ = absenkung()
    def _liste(s):
        return ", ".join(sorted(s, key=lambda x: int(x[1:]))) or "keines"
    print(f"\n  verankert       {n:>3}")
    print(f"  Absenkung       {a:>3}   eine Zeile je Fragment, in `The tenth event`;")
    print(f"                        GEMESSEN sind {_liste(haelt)}")
    # **Two different states, and telling them apart is the whole yield of today.** A
    # fragment without a differential test is one nobody has worked on; one WITH a
    # differential test whose run FALLS is a discharge that has FALLEN AWAY. Both raise `H`
    # by one -- but only the second is a step back, and until 2026-08-31 it did not appear in
    # this output at all, because the counter read the line and not the run.
    if faellt:
        print(f"                        GEBAUT, aber der Durchstich FAELLT: {_liste(faellt)}")
    ohne_lauf = [f for f in ABSENKUNG_OFFEN if f not in faellt]
    print(f"                        OHNE Differenztest: {_liste(ohne_lauf)}")
    print(f"  ---------------------")
    print(f"  H               {n + a:>3}")
    # **The other half of the split, and it is PRINTED and not subtracted** (2026-09-04).
    #
    # A lowering the checker refuses before the emitter is reached is not discharged -- it is
    # booked in the other register. *A number that shrinks without the second one appearing
    # beside it is the move `K100.1` warns against*, so the two stand together or neither
    # does.
    print(f"  Notation        {len(notation):>3}   {_liste(notation)} -- refused by the "
          f"CHECKER, so no")
    for f in notation:
        print(f"                        emitter arm reaches them: {f} carries "
              f"{fehlerzahl[f]} errors.")
    print(f"                        They belong in the «B» register (`K100.3`'s kind),")
    print(f"                        not in `H`. See `absenkungsklasse` for the criterion.")
    print()
    print("**Und was diese Zahl NICHT ist:** eine Aussage ueber Gabbro. Die zehn Fragmente")
    print("sind nach ihrer SCHWIERIGKEIT gewaehlt; `H = 0` ueber ihnen bliebe Falle 80,")
    print("solange kein Korpus daneben steht, den beim Bauen niemand angesehen hat.")


# **GabbroV's obligation population -- the DENOMINATOR, out of a command** (2026-09-03).
#
# `AUFTRAG-GABBROV.md` §2.2 asks for the rebooking of the three `progress` rows to land
# **here and not in the table**, and it gives the reason from 2026-08-20: three numbers stood
# over one thing and the one WITH the search path was the wrong one. The remedy is not to
# distrust search paths but to make sure exactly one place defines the population.
#
# **`L` does NOT move, and that is measured elsewhere.** `PFLICHTEN.md`'s third column asks
# *who* the statement is about -- machine or subject -- and these three are about the device,
# the client and the token. They stay `L`. What moves is a different population: the rows
# GabbroV is supposed to CHECK, which is the `L` rows minus the rows that are not obligations
# at all. `messung/GABBROV-V2.md` §1.6 carries that argument; this function carries the count.
#
# THE SEARCH PATH, and it has TWO SIDES that have to meet
# -------------------------------------------------------
#   source side  `messung/fragmente/F*.gab` -- every real `progress <name>` clause. These are
#                the executable fragments the checker reads, not the frozen prose of
#                `FRAGMENTE.md`, whose line anchors are from revision `708beed` and no longer
#                point where they say.
#   table side   `dokumente/PFLICHTEN.md` -- every `L` row whose fourth column names one of
#                those names.
#
# **If the two sides disagree the mode REFUSES.** A `progress` clause with no rebooked row
# means a row was missed; a rebooked row with no clause means a name was invented. *Either way
# the number would be a subtraction rather than a measurement, and the mandate asked for the
# second.*
#
# The rule the source side rests on is not prose but a pass: `schleifen.rs`:221 raises `S003`
# when a `progress` name resolves to no declared assumption and `S004` when that assumption is
# unfalsifiable. **So a legal `progress` name is a declared assumption by construction** -- the
# mode asserts it anyway, because an assertion that never fires costs nothing and an
# unchecked one costs a wrong number.
PROGRESS_KLAUSEL = re.compile(r"^\s*progress\s+([a-z_][a-z_0-9]*)\s*$")
ASSUME_ZEILE = re.compile(r"^\s*assume\s+([a-z_][a-z_0-9]*)\b")


def _progressnamen(zusatz=None):
    """The `progress` names of the ten fragments, with the file they stand in.

    `zusatz` is the speech test's handle: `(dateiname, text)` is treated as an eleventh
    fragment source, so an invented clause can be pushed in without touching the tree.
    """
    wurzel = Path(__file__).resolve().parent.parent / "messung" / "fragmente"
    quellen = [(q.name, q.read_text(encoding="utf-8")) for q in sorted(wurzel.glob("F*.gab"))]
    if zusatz is not None:
        quellen.append(zusatz)
    namen, angenommen = {}, set()
    for name, text in quellen:
        for z in text.splitlines():
            m = PROGRESS_KLAUSEL.match(z)
            if m:
                namen[m.group(1)] = name
            a = ASSUME_ZEILE.match(z)
            if a:
                angenommen.add(a.group(1))
    return namen, angenommen


def gabbrov(zusatz=None, tafelprobe=None, still=False):
    """**GabbroV's obligation population, from both sides at once.**

    Returns `(l, ausgebucht, bevoelkerung, namen, fehlend, ueberzaehlig)`.
    """
    quelle = Path(__file__).resolve().parent.parent / "dokumente" / "PFLICHTEN.md"
    text = quelle.read_text(encoding="utf-8")
    if tafelprobe is not None:
        text = text.replace(tafelprobe[0], tafelprobe[1], 1)
    namen, angenommen = _progressnamen(zusatz)
    # The table side. Same row parser as `spalten` -- one splitter, one notion of a row.
    frag, l, getroffen = None, 0, {}
    for z in text.splitlines():
        if z.startswith("# "):
            m = re.match(r"^# (F\d+)", z)
            frag = m.group(1) if m else None
        if frag is None or not z.startswith("|"):
            continue
        c = _zellen(z.strip())
        if len(c) != 6 or c[0] != "" or c[-1] != "":
            continue
        if not re.sub(r"[^A-Za-z]", "", c[3]).startswith("L"):
            continue
        l += 1
        for n in namen:
            if n in c[4]:
                getroffen.setdefault(n, []).append(c[1])
    fehlend = sorted(n for n in namen if n not in getroffen)
    ueberzaehlig = sorted(n for n, wo in getroffen.items() if len(wo) > 1)
    ausgebucht = sum(len(wo) for wo in getroffen.values())
    if not still:
        print("== GabbroV's obligation population -- the two sides, and they have to meet ==")
        print(f"  `L` rows in `PFLICHTEN.md`                    {l:>3}")
        print(f"  of these discharged by the assumption layer   {ausgebucht:>3}")
        print(f"  ------------------------------------------------")
        print(f"  GabbroV obligation population                 {l - ausgebucht:>3}")
        print()
        print(f"  `progress` clauses in `messung/fragmente/`    {len(namen):>3}")
        for n in sorted(namen):
            wo = ", ".join(getroffen.get(n, []))
            print(f"     {n:<34} {namen[n]:<9} anchor {wo or 'NO ROW'}")
        print()
        print("**And what this number is NOT:** a statement that the three are discharged.")
        print("They are assumptions with a falsifier, and a falsifier is a promise that")
        print("someone COULD refute them -- not that anyone has. *They leave GabbroV's")
        print("population because they are not obligations, not because they are settled.*")
    return l, ausgebucht, l - ausgebucht, namen, fehlend, ueberzaehlig


if __name__ == "__main__":
    if "--gabbrov" in sys.argv:
        # **The speech test, and it runs in THREE directions** (R14), because this mode has
        # two sides and a mismatch between them is the thing it exists to catch.
        l0, a0, b0, n0, fehlend, ueberzaehlig = gabbrov(still=True)
        if fehlend:
            print(f"ABBRUCH: `progress` ohne umgebuchte Zeile: {', '.join(fehlend)}.\n"
                  f"  Die Quellseite kennt einen Namen, den die Tafel nicht nennt -- die\n"
                  f"  Bevoelkerung waere zu GROSS, und zwar still.", file=sys.stderr)
            sys.exit(2)
        if ueberzaehlig:
            print(f"ABBRUCH: ein Name steht in mehr als einer `L`-Zeile: "
                  f"{', '.join(ueberzaehlig)}.", file=sys.stderr)
            sys.exit(2)
        namen, angenommen = _progressnamen()
        nicht_erklaert = sorted(n for n in namen if n not in angenommen)
        if nicht_erklaert:
            print(f"ABBRUCH: `progress` ohne `assume`: {', '.join(nicht_erklaert)}.\n"
                  f"  `S003` sollte das im Pruefer abweisen -- entweder hat sich die Regel\n"
                  f"  bewegt oder dieser Suchweg liest die falschen Dateien.", file=sys.stderr)
            sys.exit(2)
        print(f"== Sprechprobe: ok (jeder der {len(n0)} `progress`-Namen ist ein erklaertes "
              f"`assume`) ==")
        # ONE -- an invented `progress` clause with no row must REFUSE, not shrink the number.
        erfunden = ("F99-sprechprobe.gab",
                    "assume sprechprobe_erfunden\n        progress sprechprobe_erfunden\n")
        _, _, _, n1, f1, _ = gabbrov(zusatz=erfunden, still=True)
        if len(n1) != len(n0) + 1 or f1 != ["sprechprobe_erfunden"]:
            print("SPRECHPROBE GESCHEITERT: eine erfundene `progress`-Klausel ohne Zeile "
                  "wird NICHT bemerkt.", file=sys.stderr)
            sys.exit(2)
        print("== Sprechprobe: ok (eine erfundene `progress`-Klausel ohne Tafelzeile faellt) ==")
        # TWO -- taking one rebooking out of the table must lower the count by exactly one.
        eines = sorted(n0)[0]
        _, a2, b2, _, f2, _ = gabbrov(tafelprobe=(eines, "SPRECHPROBE_ENTFERNT"), still=True)
        if (a2, b2, f2) != (a0 - 1, b0 + 1, [eines]):
            print(f"SPRECHPROBE GESCHEITERT: eine entfernte Umbuchung bewegt die Zahl nicht "
                  f"({a0}/{b0} -> {a2}/{b2}).", file=sys.stderr)
            sys.exit(2)
        print(f"== Sprechprobe: ok (eine entfernte Umbuchung hebt die Bevoelkerung "
              f"{b0} -> {b2} und wird als fehlend GEMELDET) ==\n")
        gabbrov()
    elif "--spalten" in sys.argv:
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
                # **2, not 1** (2026-08-31). A fallen probe says *this tool does not
                # measure what it claims* -- nothing was measured, and what it prints
                # afterwards is not a statement about the tree. The two places here read as
                # FINDINGS until today; the sixth requirement listed the forward direction
                # by name (`SPRECHPROBE GESCHEITERT`) and never saw the backward one.
                sys.exit(2)
            if eng != vorher:
                print(f"RUECKWAERTSPROBE GESCHEITERT ({was}): eine blosse ERWAEHNUNG von "
                      f"`gap:` verstellt H ({vorher} -> {eng}). **Eine Zahl, die sich durch "
                      f"ihr eigenes Schluesselwort heben laesst, ist kein Mass.**",
                      file=sys.stderr)
                sys.exit(2)
            print(f"== Rueckwaertsprobe: ok ({was}: weit {weit_vorher} -> {weit}, "
                  f"eng {vorher} -> {eng}) ==")
        # **The same probe for the SECOND half of `H`, and since 2026-08-31 it is a RUN.**
        #
        # Until today the probe here replaced `lauf "fragment` by `lauf "GENOMMEN` **in a
        # string** and checked that the column then went empty. *That showed the regular
        # expression works.* It could not show what the number is supposed to say -- that the
        # differential test HOLDS -- because nothing was ever run.
        #
        # > **And that is exactly where it broke.** On 2026-08-31 `F06` stood at `N043`, the
        # > guard was rightly red, and `H` said 4. The old probe was green throughout: the
        # > `lauf` line had not moved.
        #
        # Now both directions come out of the guard's own run:
        #
        #   * FORWARD -- `pruefe-emission.sh --absenkung` runs a POISONED `F07` (two boot
        #     steps swapped) beside the real ones. It checks, it emits, it compiles without a
        #     warning, and the EXECUTED run says `124356` instead of `123456`. Falls it not,
        #     the guard ends with `2` and this counter refuses (`_messe_absenkung`).
        #   * BACKWARD -- the healthy fragments in the same run report `HAELT` and do NOT
        #     raise `H`. *A probe that only shows the fall also passes when everything falls.*
        haelt, faellt, _ausgabe = absenkung()
        if not haelt and not faellt:
            print("SPRECHPROBE GESCHEITERT: der Waechter urteilt ueber kein einziges "
                  "Fragment. **Diese Haelfte von H misst nichts.**", file=sys.stderr)
            sys.exit(2)
        print(f"== Sprechprobe: ok (der Waechter laesst einen vertauschten Durchstich "
              f"FALLEN und {len(haelt)} heile HALTEN) ==")
        # **The SPLIT of that half, and it is probed in both directions** (2026-09-04).
        #
        # The classification `absenkungsklasse` makes is the one move `K100.1` warns about in
        # its own text: it can degenerate into defining a debt out of existence. **`K100.1`
        # did not, because its test could have gone the other way** -- an `else` branch a
        # hostile input CAN take is logic, one that cannot be taken is a hole. So this test
        # has to be able to come out "yes, it is plumbing", and the two probes below are that
        # demonstration, run on every invocation and not asserted in prose.
        #
        #   * FORWARD -- a synthetic fragment that CHECKS CLEAN and has no differential test
        #     must land in `klempnerei` and RAISE `H`. That is the case the criterion is
        #     accused of being unable to produce, so it is produced.
        #   * BACKWARD -- one the checker REFUSES must land in `notation` and NOT raise `H`,
        #     **and under the old, undivided rule it must have counted.** Without that second
        #     half a tie proves nothing: a probe the classifier never reaches is also quiet.
        import tempfile
        SAUBER = """module sonde::sauber {
impl fn zwei() -> u32 effects { pure } costs <= 2 ops { return 2; }
}
"""
        KAPUTT = """module sonde::kaputt {
impl fn zwei() -> u32 effects { pure } costs <= 2 ops { return nirgends_erklaert; }
}
"""
        k0, n0, _ = absenkungsklasse()
        with tempfile.TemporaryDirectory() as d:
            for was, text, erwartet in (("sauber", SAUBER, "klempnerei"),
                                        ("kaputt", KAPUTT, "notation")):
                p = Path(d) / f"sonde-{was}.gab"
                p.write_text(text, encoding="utf-8")
                k1, n1, fz = absenkungsklasse(sonde=("F99", p))
                if erwartet == "klempnerei":
                    if "F99" not in k1 or len(k1) != len(k0) + 1:
                        print(f"SPRECHPROBE GESCHEITERT: eine SAUBER pruefende Datei ohne "
                              f"Durchstich landet nicht in der Klempnerei ({len(k0)} -> "
                              f"{len(k1)}). **Dann kann dieses Mass nur subtrahieren, und "
                              f"dann ist es kein Mass.**", file=sys.stderr)
                        sys.exit(2)
                    print(f"== Sprechprobe: ok (eine sauber pruefende, nicht abgesenkte "
                          f"Datei hebt H von {vorher + len(k0)} auf "
                          f"{vorher + len(k1)}) ==")
                else:
                    if "F99" not in n1 or len(k1) != len(k0):
                        print(f"SPRECHPROBE GESCHEITERT: eine vom Pruefer ABGEWIESENE Datei "
                              f"landet nicht in der Notation ({len(k0)} -> {len(k1)}).",
                              file=sys.stderr)
                        sys.exit(2)
                    weit, _, _ = absenkungsklasse(sonde=("F99", p), locker=True)
                    if len(weit) != len(k0) + len(n0) + 1:
                        print(f"RUECKWAERTSPROBE UNTAUGLICH: schon die ALTE, ungeteilte "
                              f"Regel sieht die erfundene Datei nicht ({len(weit)}). "
                              f"**Dann belegt ein Gleichstand unter der neuen nichts.**",
                              file=sys.stderr)
                        sys.exit(2)
                    print(f"== Rueckwaertsprobe: ok (eine abgewiesene Datei zaehlt unter der "
                          f"ALTEN Regel mit -- {len(weit)} -- und unter der neuen NICHT: H "
                          f"bleibt {vorher + len(k1)}, sie steht mit {fz['F99']} Fehlern in "
                          f"der Notation) ==")
        if faellt:
            gefallen = ", ".join(sorted(faellt, key=lambda x: int(x[1:])))
            print(f"== Gemessen: {gefallen} traegt eine `lauf`-Zeile und der Durchstich "
                  f"FAELLT -- das hebt H ==\n")
        else:
            print("== Gemessen: jede `lauf`-Zeile hat einen HALTENDEN Durchstich unter "
                  "sich ==\n")
        haengend()
    else:
        main()
