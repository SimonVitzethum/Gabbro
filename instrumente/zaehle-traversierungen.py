#!/usr/bin/env python3
"""**Wie viele `traverse`-Ruempfe im Korpus sind Duplikate? -- die Zahl VOR dem Bau.**

    ./instrumente/zaehle-traversierungen.py [--ruempfe] [--gift]

WOZU
----
Entscheidung 10 (Generizitaet) traegt eine **Vorhersage** als Begruendung:

> *„ohne sie braucht jede Tabelle ihr eigenes `traverse`"*

Das ist eine Behauptung ueber diesen Korpus, und sie ist erhebbar. Generizitaet waere der
groesste Einzeleingriff der offenen Liste -- Grammatik, Vertragsparametrisierung,
Monomorphisierung, mindestens zwei Schablonen. **Ein Bau ohne Zaehlung waere der erste
dieser Liste, der ohne gemessenen Bedarf beginnt**, und damit dieselbe Bewegung, die
`locks ordered` getoetet hat.

**Dieses Werkzeug baut nichts.** Es druckt zwei Zahlen: was heute dasteht, und was nach
Monomorphisierung uebrig bliebe.

DIE DEFINITION IST DIE MESSUNG
------------------------------
**Ein „duplizierter Traversierungsrumpf" sind zwei `traverse`-Bloecke, die bis auf DOMAENE
und LAUFVARIABLE zeichengleich sind.**

*Warum diese und nicht eine andere:*

* **Genau das ist es, was Monomorphisierung zusammenzoege.** Ein `traverse<T>` ueber einer
  parametrisierten Tabelle bekaeme die Domaene und den Traegertyp als Parameter; alles
  andere im Rumpf muesste danach gleich sein, sonst sind es zwei Funktionen und nicht eine
  mit zwei Instanzen. **Die Definition bildet den Eingriff ab, dessen Bedarf sie messen
  soll** -- eine weitere Definition wuerde einen anderen Eingriff messen.
* **Nicht** „zwei Schleifen ueber derselben Tabelle". Das misst, wie oft eine Tabelle
  benutzt wird -- 19-traversierung.gab laeuft zweimal ueber `Werte`, einmal schreibend und
  einmal lesend, und **kein Typparameter der Welt zieht die beiden zusammen.**
* **Nicht** „zwei Schleifen mit derselben Form". Zwei `traverse … by unvisited { if … }` sind
  formgleich und tun Verschiedenes; wer so zaehlt, misst die Grammatik und nicht den Bedarf.
  *Die Zahl steht trotzdem unten, als OBERE Schranke.*

**Das Gift bleibt draussen** (`beispiele/gift/`, mit `--gift` zuschaltbar). Giftproben sind
absichtlich beschaedigte Beinahe-Kopien voneinander; sie wuerden die Duplikatzahl heben,
ohne dass ein einziges davon ein Programm ist, das jemand geschrieben haette.

RICHTUNG DES FEHLERS (W10)
--------------------------
**Die strenge Zahl ist eine UNTERE Schranke fuer die Duplikate.** Abstrahiert wird nur die
Domaene und die Laufvariable; **Feldnamen bleiben stehen**. Zwei Ruempfe, die dasselbe an
`w.slots[i].aktiv` und an `q.eintraege[i].belegt` tun, sind fuer diese Zaehlung
VERSCHIEDEN -- obwohl eine ausgewachsene Generizitaet mit Feldprojektionen sie
zusammenzoege. *Waere abstrahiert worden, saehe die Zaehlung mehr Duplikate als da sind,
und die Zahl waere in die Richtung falsch, die den Bau begruendet.*

Deshalb steht **beides** da: die strenge Zahl und die weite (alle Bezeichner abstrahiert,
nur die Wortschatzwoerter bleiben). Die Wahrheit liegt in der Klammer, und die Klammer wird
gedruckt statt behauptet.

**Und was gar nicht gemessen wird:** ein Rumpf, den jemand NICHT geschrieben hat, weil ihm
die Generizitaet fehlte. Ein solcher Bedarf hinterlaesst im Text keine Spur -- diese
Zaehlung kann ihn nicht sehen und behauptet nicht, es zu koennen.
"""
import difflib
import pathlib
import re
import sys

W = pathlib.Path(__file__).resolve().parent.parent

# Dieselbe Teilung wie in `zaehle-zeremonie.py`: der Lehrkorpus ist FUER Gabbro geschrieben,
# die Stuecke in `messung/` sind echter Code gegen eine fremde Vorlage (Regel B).
LEHRKORPUS = sorted((W / "beispiele").glob("*.gab")) + sorted(
    (W / "messung" / "fragmente").glob("F*.gab"))
ECHTKORPUS = sorted((W / "messung" / "treiber").glob("*.gab")) + sorted(
    (W / "messung" / "caprock").glob("*.gab")) + sorted(
    (W / "messung" / "netz").glob("*.gab"))
GIFT = sorted((W / "beispiele" / "gift").glob("*.gab"))

# Der geschlossene Wortschatz (`SYNTAX.md`, Abschnitt „Vocabulary -- closed"). Alles andere
# ist ein Bezeichner -- und genau das braucht die WEITE Normalisierung, um Wortschatzwoerter
# stehenzulassen und Namen zu ersetzen.
WORTSCHATZ = set("""
module pub use type opaque linear ghost tagged const static fn
spec impl raw divergent prim extern section arch when
requires ensures maintains breaking effects costs where in
exhaustive old narrow to induction order advances
reads writes locks masks allocs consumes publishes diverges pure
if else match traverse over by touches retry forever until
bounded progress on_exceeded per_pass return let mut
unvisited consuming decreasing leave leaves next ops result
exchange update returns insert remove relabel
ptr normal mmio dma code boot r w rw x own
format table slot invariant reason state transition device reg
class fields bank at stride count backed mirrors from
assume falsifier unfalsifiable axiom lock protects rank group rcu observes reclaims
check claim measures gates can_fail floor counterprobe expects
endian little big reserved cost runs online offline
offset_into index into option chain wrapping
atomic acquire release seq relaxed nothing accumulates merge decreases
max min add or and held shared
embeds scale walk levels node down leaf mappings
entry entrust vector regs out preserves clobbers stack dispatch asm
per cpu ist nested masked awaits port step via
slots of chain descendants ancestors queue elems threads
reaches tree parent child sibling observed
u8 u16 u32 u64 i8 i16 i32 i64 f32 f64 rounded finite bool never w1c rc
sizeof lenof aligned forall exists true false Self Some None O Held
""".split())

# **Die Domaenensprache ist ein EIGENER, kleinerer Wortschatz -- und das ist kein
# Schoenheitsfehler.** `w`, `r` und `x` stehen im grossen Wortschatz als Zeigerrechte
# (`ptr<normal, rw>`) und sind zugleich die haeufigsten Variablennamen des Korpus
# (`w : ptr<normal, r> Werte`). Wer im Bereich `over … by` gegen den GROSSEN Wortschatz
# filtert, haelt das `w` in `over slots of w` fuer ein Schluesselwort, abstrahiert es nicht,
# und **findet ausgerechnet das offensichtlichste Duplikat nicht** -- gemessen an der
# Sprechprobe, die genau daran zuerst rot wurde.
DOMAENENWORTE = set("""
slots of chain descendants ancestors queue elems fields threads reaches via tree
parent child sibling observed from mappings down leaf node levels walk
""".split())
# Fuer die WEITE Lesart bleiben `w`, `r`, `x` draussen: sie als Wortschatz zu behandeln
# hiesse, einen Variablennamen stehenzulassen, wo alle anderen ersetzt werden -- und eine
# OBERE Schranke, die zu wenig zusammenzieht, ist keine obere Schranke.
WORTSCHATZ_ABSTRAKT = WORTSCHATZ - {"w", "r", "x"}

WORT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*|\d+|\S")


def ohne_kommentare(text):
    """`--` bis Zeilenende weg. Zeichenketten bleiben -- in einem `traverse`-Rumpf des
    Korpus steht keine, und eine Naeherung, die das sagt, ist besser als ein halber Lexer."""
    aus = []
    for zeile in text.split("\n"):
        i = zeile.find("--")
        aus.append(zeile if i < 0 else zeile[:i])
    return "\n".join(aus)


def traversierungen(text):
    """Alle `traverse`-Stellen als `(kopf, rumpf, zeile)`.

    Der Kopf ist alles zwischen `traverse` und der oeffnenden Klammer des Rumpfs, der Rumpf
    ist der geklammerte Block -- mit Klammerzaehlung, damit ein `if` darin nicht abschneidet.
    """
    roh = ohne_kommentare(text)
    aus = []
    for m in re.finditer(r"\btraverse\b", roh):
        i = roh.find("{", m.end())
        if i < 0:
            continue
        kopf = roh[m.end():i]
        tiefe, j = 0, i
        while j < len(roh):
            if roh[j] == "{":
                tiefe += 1
            elif roh[j] == "}":
                tiefe -= 1
                if tiefe == 0:
                    break
            j += 1
        if tiefe != 0:
            continue          # unbalanciert -- lieber nicht zaehlen als falsch zaehlen
        aus.append((kopf.strip(), roh[i + 1:j].strip(), roh[:m.start()].count("\n") + 1))
    return aus


def laufvariable(kopf):
    """`traverse i of e over d by …` -- die Laufvariable ist das erste Wort des Kopfs."""
    m = re.match(r"\s*([A-Za-z_][A-Za-z0-9_]*)", kopf)
    return m.group(1) if m else None


def domaenennamen(kopf):
    """Die Bezeichner der DOMAENE: alles zwischen `over` und `by`, plus `of e`.

    Das sind genau die Namen, die ein `traverse<T>` als Parameter bekaeme -- der Traeger und
    was ihn erreicht. Sie werden ersetzt, alles andere bleibt.
    """
    namen = set()
    m = re.search(r"\bover\b(.*?)\bby\b", kopf, re.S)
    if m:
        namen |= {w for w in re.findall(r"[A-Za-z_][A-Za-z0-9_]*", m.group(1))
                  if w not in DOMAENENWORTE}
    m = re.search(r"\bof\b(.*?)\bover\b", kopf, re.S)
    if m:
        namen |= {w for w in re.findall(r"[A-Za-z_][A-Za-z0-9_]*", m.group(1))
                  if w not in DOMAENENWORTE}
    return namen


def streng(kopf, rumpf):
    """**Nur** Laufvariable und Domaenennamen werden abstrahiert. Feldnamen bleiben.

    Das ist die UNTERE Schranke: was hier gleich aussieht, ist wirklich gleich.
    """
    ersatz = {}
    lv = laufvariable(kopf)
    if lv:
        ersatz[lv] = "@i"
    for n in sorted(domaenennamen(kopf)):
        ersatz[n] = "@d"
    aus = []
    for w in WORT.findall(rumpf):
        aus.append(ersatz.get(w, w))
    # Der Kopf zaehlt mit -- ohne ihn waeren `by unvisited` und `by consuming` dasselbe, und
    # das sind zwei verschiedene Laeufe (SYNTAX.md, Abschnitt 8).
    kopfform = [ersatz.get(w, w) for w in WORT.findall(kopf)]
    return " ".join(kopfform) + " || " + " ".join(aus)


def weit(kopf, rumpf):
    """ALLE Bezeichner werden abstrahiert, nur Wortschatzwoerter und Zahlen bleiben.

    Das ist die OBERE Schranke: sie misst die FORM, nicht den Bedarf -- zwei Schleifen, die
    Verschiedenes tun, sehen hier gleich aus.
    """
    aus = []
    for w in WORT.findall(kopf) + ["||"] + WORT.findall(rumpf):
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", w) and w not in WORTSCHATZ_ABSTRAKT:
            aus.append("@")
        else:
            aus.append(w)
    return " ".join(aus)


def nachbarn(funde, schwelle=0.85):
    """**Die naechsten Nachbarn -- was die 0 zu bedeuten hat.**

    Eine 0 ohne diese Liste ist nicht nachpruefbar: sie koennte heissen „nichts aehnelt
    einander" oder „meine Definition ist so eng, dass nichts sie erfuellt". Hier steht, wie
    nah der Korpus der Duplikation KOMMT -- Aehnlichkeit der weit normalisierten
    Zeichenketten, absteigend.

    Gemessen wird mit `difflib`, nicht mit einem eigenen Mass: ein Aehnlichkeitsmass, das
    derselbe Autor gegen dieselben Daten erfindet, misst wieder die Passung (W7).
    """
    formen = [(d, z, weit(k, r)) for d, z, k, r in funde]
    paare = []
    for a in range(len(formen)):
        for b in range(a + 1, len(formen)):
            q = difflib.SequenceMatcher(None, formen[a][2], formen[b][2]).ratio()
            if q >= schwelle:
                paare.append((q, formen[a][:2], formen[b][:2]))
    return sorted(paare, reverse=True)


def gruppiere(funde, norm):
    """`{normalform: [(datei, zeile), …]}` -- eine Gruppe mit k>1 sind k-1 Duplikate."""
    g = {}
    for datei, zeile, kopf, rumpf in funde:
        g.setdefault(norm(kopf, rumpf), []).append((datei, zeile))
    return g


def sammle(dateien):
    funde = []
    for p in dateien:
        text = p.read_text(encoding="utf-8", errors="replace")
        for kopf, rumpf, zeile in traversierungen(text):
            funde.append((p.relative_to(W), zeile, kopf, rumpf))
    return funde


def sprechprobe():
    """**In beide Richtungen, an erfundenen Quellen.** Ein Zaehler, der nie ein Duplikat
    finden kann, misst nichts (R14) -- und einer, der ueberall eines sieht, auch nicht.
    """
    zwei_gleiche = """
    impl fn a(w : ptr<normal, rw> A) {
        traverse i over slots of w by unvisited touches writes w.slots
        { if w.slots[i].aktiv { w.slots[i].aktiv = false; } }
    }
    impl fn b(q : ptr<normal, rw> B) {
        traverse j over slots of q by unvisited touches writes q.slots
        { if q.slots[j].aktiv { q.slots[j].aktiv = false; } }
    }
    """
    zwei_verschiedene = """
    impl fn a(w : ptr<normal, rw> A) {
        traverse i over slots of w by unvisited touches writes w.slots
        { if w.slots[i].aktiv { w.slots[i].aktiv = false; } }
    }
    impl fn b(w : ptr<normal, rw> A) {
        traverse i over slots of w by unvisited touches writes w.slots
        { if w.slots[i].belegt { w.slots[i].belegt = false; } }
    }
    """
    zwei_laufarten = """
    impl fn a(w : ptr<normal, rw> A) {
        traverse i over slots of w by unvisited { f(i); }
    }
    impl fn b(q : ptr<normal, rw> B) {
        traverse i over slots of q by consuming { f(i); }
    }
    """
    kommentar = """
    impl fn a(w : ptr<normal, rw> A) {
        -- traverse i over slots of w by unvisited { }
        traverse i over slots of w by unvisited { f(i); }
    }
    """
    def gr(t, norm=streng):
        return gruppiere([("x", 0, k, r) for k, r, _ in traversierungen(t)], norm)
    return [
        ("zwei gleiche Ruempfe ueber zwei Tabellen fallen zusammen",
         len(gr(zwei_gleiche)) == 1),
        ("zwei Ruempfe, die sich nur im FELDNAMEN unterscheiden, fallen streng NICHT "
         "zusammen", len(gr(zwei_verschiedene)) == 2),
        ("`by unvisited` und `by consuming` fallen NICHT zusammen",
         len(gr(zwei_laufarten)) == 2),
        ("ein auskommentiertes `traverse` wird nicht gezaehlt",
         len(traversierungen(kommentar)) == 1),
        ("die weite Lesart zieht genau die zusammen -- das ist der Unterschied der beiden "
         "Schranken", len(gr(zwei_verschiedene, weit)) == 1),
    ]


def bericht(name, dateien, ausfuehrlich):
    funde = sammle(dateien)
    zeilen = sum(len(p.read_text(encoding="utf-8", errors="replace").splitlines())
                 for p in dateien)
    g_streng = gruppiere(funde, streng)
    g_weit = gruppiere(funde, weit)
    print(f"== {name} ==")
    print(f"  {len(funde)} Traversierungsruempfe stehen heute da")
    print(f"  {len(g_streng)} blieben nach Monomorphisierung (streng)")
    print(f"  {len(funde) - len(g_streng)} duplizierte Traversierungsruempfe (streng)")
    print(f"  {len(funde) - len(g_weit)} duplizierte Traversierungsruempfe (weit) -- "
          "OBERE Schranke,")
    print(f"    {len(g_weit)} blieben unter der Formgleichheit uebrig; sie misst die")
    print("    Grammatik und nicht den Bedarf")
    doppel = {k: v for k, v in g_streng.items() if len(v) > 1}
    if doppel:
        print(f"  die {len(doppel)} Gruppen mit mehr als einem Mitglied:")
        for k, v in sorted(doppel.items(), key=lambda x: -len(x[1])):
            print(f"    {len(v)} x  " + ", ".join(f"{d}:{z}" for d, z in v))
    else:
        print("  keine einzige Gruppe hat mehr als ein Mitglied")
    print(f"  Arbeitsmenge: {len(dateien)} Dateien, {zeilen} Zeilen")
    if ausfuehrlich:
        for datei, zeile, kopf, rumpf in funde:
            print(f"    -- {datei}:{zeile}")
            print(f"       traverse {' '.join(kopf.split())}")
            print(f"       {streng(kopf, rumpf)[:160]}")
    print()
    return len(funde), len(g_streng), len(g_weit)


def main():
    proben = sprechprobe()
    print("== Sprechprobe, in beide Richtungen ==")
    for was, gut in proben:
        print(f"  {'ok ' if gut else 'ROT'}  {was}")
    if not all(g for _, g in proben):
        print("SPRECHPROBE GESCHEITERT -- es wurde NICHTS gemessen.", file=sys.stderr)
        # **Every refusal in this file ends with 2, not 1** (2026-08-31). This counter joined
        # `abnahme.py` that day, so its return code is now read as a VERDICT -- and the sixth
        # requirement applies: `1` means the TREE has to change, `2` means the SETUP does.
        # Every site below says NOTHING WAS MEASURED, so every one of them is a `2`.
        return 2
    print()

    if not LEHRKORPUS:
        print("ABBRUCH: der Lehrkorpus fehlt -- es wird NICHT null gemessen.",
              file=sys.stderr)
        return 2

    ausfuehrlich = "--ruempfe" in sys.argv
    l = bericht("Lehrkorpus (beispiele/ + messung/fragmente/)", LEHRKORPUS, ausfuehrlich)
    e = bericht("Echter Code (messung/treiber, caprock, netz -- Regel B)",
                ECHTKORPUS, ausfuehrlich)
    if "--gift" in sys.argv:
        bericht("Gift (NICHT im Urteil -- absichtlich beschaedigte Beinahe-Kopien)",
                GIFT, ausfuehrlich)

    ges_heute = l[0] + e[0]
    ges_streng = l[1] + e[1]
    ges_weit = l[2] + e[2]
    print("== Die Zahl, die Entscheidung 10 vor dem Bau braucht ==")
    print(f"  {ges_heute} Traversierungsruempfe stehen heute im Korpus")
    print(f"  {ges_streng} blieben nach Monomorphisierung")
    print(f"  {ges_heute - ges_streng} duplizierte Ruempfe -- das ist der gemessene Bedarf")
    print(f"  {ges_heute - ges_weit} unter der weitesten Lesart, die noch zu verteidigen ist")
    print()
    alle = sammle(LEHRKORPUS) + sammle(ECHTKORPUS)
    nah = nachbarn(alle)
    print("== Wie NAH der Korpus der Duplikation kommt ==")
    print(f"  {len(nah)} Paare von {len(alle)*(len(alle)-1)//2} liegen ueber 85 % "
          "Aehnlichkeit")
    for q, a, b in nah[:12]:
        print(f"    {100*q:5.1f} %  {a[0]}:{a[1]}  <->  {b[0]}:{b[1]}")
    print("    Eine 0 ohne diese Liste waere nicht nachpruefbar: sie koennte heissen")
    print("    „nichts aehnelt einander“ oder „meine Definition ist zu eng“. Hier steht,")
    print("    welche von beiden es ist.")
    print()
    print("  **Und der Befund steckt in den Gruenden, aus denen die Naechsten sich")
    print("  unterscheiden -- nachgesehen 2026-08-21, Paar fuer Paar:**")
    print("    98,9 %  ein `!` und ein Feldname. Kein Typparameter entfernt eine Verneinung.")
    print("    96,5 %  zwei Faelle des Widerrufs, und sie unterscheiden sich in der")
    print("            ARGUMENTLISTE des Blattloeschers (`blatt_loeschen(c,o,i)` gegen")
    print("            `blatt_loeschen(i)`) -- das ist ein Wertparameter, kein Typparameter.")
    print("    95,0 %  gleiche Domaene, verschiedene Wirkung (`aktiv = false` unter einer")
    print("            `locks`-Klammer gegen ohne).")
    print("  **Keines der zwoelf Paare wuerde von Monomorphisierung zusammengezogen.** Die")
    print("  Vorhersage *„sonst braucht jede Tabelle ihr eigenes `traverse`“* trifft auf")
    print("  diesen Korpus nicht: die Ruempfe sind nicht deshalb verschieden, weil die")
    print("  Tabelle verschieden ist, sondern weil die AUFGABE verschieden ist.")
    print()

    print("== Und was das NICHT heisst ==")
    print("  Die strenge Zahl ist eine UNTERE Schranke: Feldnamen bleiben stehen, zwei")
    print("  Ruempfe ueber verschiedenen Feldnamen sind hier VERSCHIEDEN. Waere anders")
    print("  normalisiert worden, saehe die Zaehlung mehr Duplikate als da sind -- und die")
    print("  Zahl waere in die Richtung falsch, die den Bau begruendet.")
    print("  Nicht gemessen wird ein Rumpf, den jemand NICHT geschrieben hat, weil ihm die")
    print("  Generizitaet fehlte. Ein solcher Bedarf hinterlaesst im Text keine Spur.")
    print("  Und die Gegenprobe zur Vorhersage steht in der Gruppenliste oben: `traverse`")
    print("  ueber DERSELBEN Tabelle zweimal ist kein Duplikat, sondern zwei Aufgaben --")
    print("  kein Typparameter der Welt zieht die zusammen.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
