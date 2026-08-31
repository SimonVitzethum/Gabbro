#!/usr/bin/env python3
"""**Die fehlende VERDRAHTUNG. Zwei Teile stehen, jedes fuer sich richtig, und keines
weiss vom anderen.**

    ./instrumente/zaehle-verdrahtung.py [--lang]

Am Abend des 2026-08-30 ist SECHSMAL dieselbe Form gefallen, an sechs unabhaengigen
Stellen und keine davon aus derselben Bahn:

    Griff  /  Freiliste            der lineare Zeuge existiert, die Freiliste benutzt ihn nicht
    boot   /  backed               `bss_nullen(0x2000,0x3000)` = 4 KiB, groesstes Feld 16 MiB
    Pruefer/  Erzeuger (Griff)     `match g { Griff(i) => … }` prueft gruen, `C001` beim Erzeuger
    lean   /  Resolver             `lean` KLEBT TEXT; `umgebung::kandidaten` folgte `use` laengst
    m2::endet / crate::endet_immer ein VIERTES Register derselben Dreierliste, andere Semantik
    breite_von / zwei Verteiler    eine Wurzel, zwei Wege, keiner kennt den anderen

> **Die Teile entstehen einzeln und korrekt, die Verdrahtung entsteht nie -- weil sie zu
> keinem Konstrukt gehoert und deshalb in keiner Bahn steht.**

Sechs Funde an einem Abend sind kein Zufall, sondern ein fehlendes Werkzeug -- dieselbe
Begruendung, mit der `pruefe-klauseln.py` entstand. Der Unterschied: **jenes Werkzeug misst
EIN Feld gegen seine Leser, dieses misst ZWEI Teile gegeneinander.**

DIE FUENF FORMEN, UND WARUM ES FUENF SIND
-----------------------------------------
Die Klasse ist maschinell schwer zu fassen, und darum ist **die Ehrlichkeit ueber den
Nenner wichtiger als die Zahl** (W25: *eine Zahl belegt ihren Nenner, nicht ihre
Beschriftung*). Jede Form nennt ihren eigenen Nenner, und keine Form addiert sich zu einer
anderen -- die Summe unten ist eine SUMME VON FORMEN, keine Anzahl von Fehlern.

    V1  zwei Konstrukte, die im Korpus zusammen vorkommen, und keine Passfunktion,
        die BEIDE liest                       Nenner: Konstruktpaare mit Korpusstelle
    V2  zwei Register ueber derselben Menge -- dasselbe Oder-Muster an >= 2 Stellen
                                              Nenner: alle Oder-Muster >= 3 Alternativen
    V3  der Pruefer schweigt, der Erzeuger weigert sich (`C001`)
                                              Nenner: alle `weigere`-Stellen in `emit.rs`
    V4  eine Klausel, die kein Pass liest     Nenner: `pruefe-klauseln.py`, uebernommen
    V5  ein Angebot, das keine Pflicht ist -- ein reserviertes Wort ohne Korpusstelle
                                              Nenner: alle reservierten Woerter

**V4 wird nicht nachgebaut, sondern GEFRAGT.** `pruefe-klauseln.py` misst dieselbe Klasse
auf Feldebene seit dem 2026-08-18; sie hier ein zweites Mal zu zaehlen waere selbst ein
Doppelregister -- *genau die Form, die V2 zaehlt.*

DIE EICHUNG IST DER HALBE BERICHT
---------------------------------
Ein Zaehlwerkzeug fuer eine Klasse, die von Hand gefunden wurde, muss sagen, **wie viele
der von Hand gefundenen es selbst sieht.** Die sechs oben sind der Startkorpus, und der
Bericht fuehrt sie einzeln mit *gesehen* oder *blind*. Was es nicht sieht, ist der Beleg
dafuer, dass jede Zahl hier eine UNTERE Schranke ist (W10) -- sie verpflichtet und spricht
nicht frei.

**V1 traegt einen KNOPF, und er wird mitgedruckt.** Eine Funktion, die mehr als die HAELFTE
aller Itemarten anfasst, laeuft ueber den Baum; sie verdrahtet nicht zwei Konstrukte,
sondern besucht alle. Wer sie mitzaehlt, bekommt **0 offene Paare** -- nicht weil nichts
offen ist, sondern weil `bindung::genannte_namen` jedes Paar einmal beruehrt. Die Schranke
steht deshalb bei der Haelfte, und **die ganze Empfindlichkeitskurve steht im Bericht**:
eine Zahl, die mit ihrem Knopf von 0 auf 94 wandert, darf nicht ohne ihn genannt werden.
"""
import argparse
import collections
import itertools
import pathlib
import re
import subprocess
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import abschnitt  # noqa: E402

W = pathlib.Path(__file__).resolve().parent.parent
PRUEFER = W / "crates/gabbro-check/src"
SYNTAX = W / "crates/gabbro-syntax/src"

# `emit.rs` and `zeugnis.rs` LOWER and REPORT, they check nothing -- the same split
# `pruefe-klauseln.py` draws. Counting them as readers would book every construct as read.
TRAGEND = {"emit.rs", "zeugnis.rs"}


def ohne_kommentar(text):
    """Zeilenweise die Kommentare leeren, ohne die Zeilennummern zu verschieben."""
    return "\n".join(
        "" if z.lstrip().startswith("//") else z for z in text.splitlines()
    )


def korpusdateien():
    """Der SAUBERE Korpus. `beispiele/gift` steht absichtlich nicht darin: eine
    Giftprobe ist eine Datei, die FALLEN soll, und was in ihr zusammensteht, ist kein
    Beleg dafuer, dass zwei Konstrukte zusammen vorkommen duerfen."""
    q = sorted(W.glob("beispiele/*.gab")) + sorted(W.glob("messung/**/*.gab"))
    return [p for p in q if "/gift/" not in str(p)]


def konstrukte():
    """`Kw::X => ItemArt::Y` aus dem Leser, `Kw::X => "x"` aus der Wortliste.

    **Mechanisch und nicht kuratiert** -- wer ein Konstrukt hinzufuegt, kann es nicht aus
    dieser Liste heraushalten, und das ist der ganze Punkt (dieselbe Bauart wie
    `pruefe-klauseln.py`, das jedes `pub`-Feld aus `ast.rs` nimmt)."""
    kw = (SYNTAX / "kw.rs").read_text(encoding="utf-8")
    wortliste = dict(re.findall(r'^\s*(\w+)\s*=>\s*"([^"]+)"', kw, re.M))
    par = (SYNTAX / "parse.rs").read_text(encoding="utf-8")
    paare = re.findall(r"Art::Wort\(Kw::(\w+)\) => ItemArt::(\w+)\(", par)
    return {v: wortliste[k] for k, v in paare if k in wortliste}


def passfunktionen(wort):
    """Je Funktion des Pruefers: welche Itemarten fasst sie an?

    **Je FUNKTION und nicht je Datei.** Wer `Entry` in der einen und `Lock` in der
    anderen Funktion liest, hat die beiden nicht verdrahtet -- er hat sie nebeneinander
    gelegt. *Die Datei als Mass haette `namen.rs` alles verdrahten lassen.*"""
    aus = []
    for f in sorted(PRUEFER.glob("*.rs")):
        if f.name in TRAGEND:
            continue
        t = f.read_text(encoding="utf-8")
        anfaenge = [
            (m.start(), m.group(1))
            for m in re.finditer(r"(?m)^(?:pub(?:\(crate\))? )?fn (\w+)", t)
        ]
        anfaenge.append((len(t), None))
        for i in range(len(anfaenge) - 1):
            rumpf = ohne_kommentar(t[anfaenge[i][0]:anfaenge[i + 1][0]])
            traefe = {v for v in wort if re.search(r"ItemArt::%s\b" % v, rumpf)}
            if traefe:
                zeile = t[: anfaenge[i][0]].count("\n") + 1
                aus.append((f.name, anfaenge[i][1], zeile, traefe))
    return aus


def v1_konstruktpaare(wort, fn_liest, schranke):
    """Paare, die im Korpus zusammenstehen und die keine Passfunktion zusammen liest."""
    zusammen = collections.Counter()
    for p in korpusdateien():
        txt = "\n".join(
            z for z in p.read_text(encoding="utf-8").splitlines()
            if not z.lstrip().startswith("--")
        )
        da = {
            v for v, w in wort.items()
            if re.search(r"(?m)^\s*(pub\s+)?%s\s" % re.escape(w), txt)
        }
        for a, b in itertools.combinations(sorted(da), 2):
            zusammen[(a, b)] += 1
    verdrahtet, sammler = set(), []
    for datei, name, zeile, treffer in fn_liest:
        if len(treffer) > schranke:
            sammler.append((datei, name, zeile, len(treffer)))
            continue
        for a, b in itertools.combinations(sorted(treffer), 2):
            verdrahtet.add((a, b))
    offen = {p: n for p, n in zusammen.items() if p not in verdrahtet}
    return zusammen, offen, sammler


def odermuster(text):
    """Jedes Oder-Muster mit >= 3 verschiedenen Alternativen, als (Menge, Zeile).

    **Ueber TEXT und nicht ueber eine Datei** -- damit die Sprechprobe unten dieselbe
    Funktion fahren kann, die der Bericht fuehrt. *Ein Selbsttest gegen einen Nachbau misst
    den Nachbau* (W7)."""
    roh = ohne_kommentar(text)
    aus = []
    for m in re.finditer(
        r"((?:\w+::)+\w+(?:\([^()]*\))?\s*\|\s*){2,}(?:\w+::)+\w+(?:\([^()]*\))?",
        roh,
    ):
        alt = frozenset(
            re.sub(r"\(.*\)", "", a) for a in re.split(r"\s*\|\s*", m.group(0).strip())
        )
        if len(alt) >= 3:
            aus.append((alt, roh[: m.start()].count(chr(10)) + 1))
    return aus


def ohne_stelle(woerter, korpustext):
    """Welche der Woerter stehen NIRGENDS im Korpustext? Die reine Haelfte von V5."""
    return [w for w in woerter if not re.search(r"\b%s\b" % re.escape(w), korpustext)]


def v2_doppelregister():
    """Dasselbe Oder-Muster (>= 3 Alternativen) an >= 2 Stellen des Baums.

    **Und die schaerfere Frage vor dem Zusammenziehen ist, ob sie dasselbe sagen SOLLEN.**
    `m2::endet` und `crate::endet_immer` fuehren dieselbe Dreierliste und antworten
    verschieden auf einen indirekten Ruf -- *zwei Register ueber derselben Menge sind ein
    Verdacht, keine Absage.* Das Werkzeug nennt die Stellen; die Entscheidung ist ein
    Urteil und steht nicht hier."""
    muster = collections.defaultdict(list)
    for f in sorted(PRUEFER.glob("*.rs")) + sorted(SYNTAX.glob("*.rs")):
        for alt, zeile in odermuster(f.read_text(encoding="utf-8")):
            muster[alt].append("%s:%d" % (f.name, zeile))
    return muster, {k: v for k, v in muster.items() if len(v) >= 2}


def v3_erzeugerweigerung():
    """`weigere(...)` in `emit.rs`: jede Stelle ist eine, an der der Pruefer gruen war.

    *Der Erzeuger weigert sich mit `C001`, und der Pruefer hat nichts gesagt.* Ob die
    Weigerung richtig ist, sagt diese Zahl nicht -- sie zaehlt die STELLEN, an denen die
    beiden Haelften verschieden viel wissen."""
    t = (PRUEFER / "emit.rs").read_text(encoding="utf-8")
    stellen = []
    for m in re.finditer(r"(?<!fn )weigere\(", ohne_kommentar(t)):
        stellen.append(t[: m.start()].count("\n") + 1)
    grund = re.findall(r'weigere\([^;]*?"([^"]{4,})"', t, re.S)
    return stellen, grund


def v4_klauseln():
    """`pruefe-klauseln.py` gefragt, nicht nachgebaut."""
    u = subprocess.run(
        [sys.executable, str(W / "instrumente/pruefe-klauseln.py")],
        capture_output=True, text=True, timeout=300,
    )
    def zahl(marke):
        m = re.search(r"%s: (\d+)" % marke, u.stdout)
        return int(m.group(1)) if m else None
    m = re.search(r"Quelle: (\d+) Feldnamen", u.stdout)
    return zahl("NUR GETRAGEN"), zahl("UNGELESEN"), (int(m.group(1)) if m else None)


def v5_angebot_ohne_pflicht():
    """Ein reserviertes Wort, das im sauberen Korpus nirgends steht.

    `linear ghost` gibt es, und zwei Tabellen mit `ops` fuehren es nicht -- die allgemeine
    Form davon ist: **die Grammatik bietet etwas an, und kein Programm hat es je
    gebraucht.** Regel A sagt, dass so etwas nicht haette gebaut werden duerfen; diese
    Zahl sagt, wie oft es doch geschah."""
    kw = (SYNTAX / "kw.rs").read_text(encoding="utf-8")
    woerter = [
        (m.group(1), m.group(2))
        for m in re.finditer(r'^\s*(\w+)\s*=>\s*"([^"]+)"', kw, re.M)
    ]
    text = []
    for p in korpusdateien():
        text.append("\n".join(
            z for z in p.read_text(encoding="utf-8").splitlines()
            if not z.lstrip().startswith("--")
        ))
    return woerter, ohne_stelle([w for _, w in woerter], "\n".join(text))


# **The calibration.** One line per case of the starting corpus: which form ought to see
# it, and why. Whoever adds a form adds its calibration line, or the number below stops
# meaning anything.
EICHUNG = [
    ("Griff / Freiliste",
     None,
     "`linear ghost type Griff` steht in beispiele/58, und beispiele/27-freiliste.gab "
     "traegt das Wort `linear` nirgends -- keine Form sieht einen Ort, an dem etwas "
     "NICHT steht"),
    ("boot / backed",
     "V1",
     "`Boot` steht mit `Format`, `Konst`, `Walk` und `Modul` offen im Paarbericht; die "
     "Rechnung 0x3000-0x2000 gegen `count 1048576` sieht auch V1 nicht"),
    ("Pruefer / Erzeuger (Griff)",
     "V3",
     "emit.rs:7170, `match` ueber etwas anderes als `option index into T` -- eine der "
     "gezaehlten Stellen; WELCHE, sagt die Form nicht"),
    ("lean / Resolver",
     None,
     "`umgebung::kandidaten` kann es, `main.rs:308` baut mit `push_str` daran vorbei -- "
     "V2 sieht gleiche MUSTER, nicht gleiche Absichten"),
    ("m2::endet / crate::endet_immer",
     "V2",
     "`StmtArt::Return|Leave|Next` an vier Stellen: kosten.rs:594, lib.rs:900, "
     "m1.rs:1406, m1.rs:1416"),
    ("breite_von / zwei Verteiler",
     None,
     "drei Breitentafeln (emit.rs:3449, umgebung.rs:1583, bitlage.rs:73) in drei "
     "Einheiten -- eine Wurzel mit zwei Rufern ist kein Oder-Muster"),
]


def sprechprobe():
    """**Misst dieses Werkzeug ueberhaupt?** In beide Richtungen, je Form.

    Ein Zaehler ohne Selbsttest ist eine Zahl ohne Zeugen: eine kaputte Form meldet **0**,
    und 0 liest sich wie *„nichts offen"*. Jede Zeile hier faehrt die Funktion, die auch der
    Bericht faehrt -- kein Nachbau, sonst misst die Probe den Nachbau (W7).

    Gibt eine Liste der VERLETZUNGEN; leer heisst bestanden."""
    schlecht = []

    # V2 -- one pattern at two sites is found, one at a single site is not.
    zwei = odermuster(
        "match x { A::Ein(_) | A::Zwei(_) | A::Drei(_) => 1, _ => 0 }\n"
        "match y { A::Ein(_) | A::Zwei(_) | A::Drei(_) => 2, _ => 0 }\n"
    )
    if len({m for m, _ in zwei}) != 1 or len(zwei) != 2:
        schlecht.append("V2: dasselbe Muster an zwei Stellen wird nicht als EINES gezaehlt")
    if odermuster("match x { A::Ein(_) | A::Zwei(_) => 1, _ => 0 }\n"):
        schlecht.append("V2: zwei Alternativen sind kein Register und muessen durchfallen")
    # **And a COMMENT is no register.** Otherwise every explanation would count.
    if odermuster("// A::Ein(_) | A::Zwei(_) | A::Drei(_) -- nur erklaert\n"):
        schlecht.append("V2: ein Muster im Kommentar zaehlt mit")

    # V5 -- a word with no corpus site shows up, one with a site does not.
    ohne = ohne_stelle(["gibtsnicht", "steht"], "hier steht etwas")
    if ohne != ["gibtsnicht"]:
        schlecht.append("V5: %r statt genau dem fehlenden Wort" % ohne)
    # A PARTIAL word is no site -- `\b` carries the whole statement.
    if ohne_stelle(["steh"], "hier steht etwas") != ["steh"]:
        schlecht.append("V5: ein Teilwort gilt faelschlich als Fundstelle")

    # V1 -- the bound excludes collectors, and only those.
    fn = [("a.rs", "eng", 1, {"Entry", "Lock"}),
          ("b.rs", "sammler", 2, {"Entry", "Lock", "Boot", "Walk"})]
    _, offen_eng, weg_eng = v1_konstruktpaare({}, fn, 2)
    if not any(n == "sammler" for _, n, _, _ in weg_eng):
        schlecht.append("V1: die Schranke schliesst den Sammler nicht aus")
    if any(n == "eng" for _, n, _, _ in weg_eng):
        schlecht.append("V1: die Schranke schliesst eine enge Funktion aus")
    _, _, weg_weit = v1_konstruktpaare({}, fn, 9)
    if weg_weit:
        schlecht.append("V1: eine hohe Schranke schliesst trotzdem aus")
    return schlecht


def main():
    p = argparse.ArgumentParser(add_help=True)
    p.add_argument("--lang", action="store_true", help="jede Fundstelle einzeln")
    p.add_argument("--schranke", type=int, default=None,
                   help="V1: hoechste Zahl Itemarten, bis zu der eine Funktion als "
                        "verdrahtend gilt (Vorgabe: die Haelfte)")
    a = p.parse_args()

    if schlecht := sprechprobe():
        print("ABBRUCH: die SPRECHPROBE dieses Werkzeugs faellt -- es misst nicht, was es")
        print("  behauptet, und jede Zahl darunter waere geraten:", file=sys.stderr)
        for s in schlecht:
            print("    " + s, file=sys.stderr)
        return 2
    print("== Sprechprobe: ok (jede Form faellt und schweigt am richtigen Gegenstand) ==")

    wort = konstrukte()
    schranke = a.schranke if a.schranke is not None else len(wort) // 2
    fn_liest = passfunktionen(wort)

    print("== Verdrahtung: zwei Teile, die nichts voneinander wissen ==")
    print("   %d Itemarten, mechanisch aus `parse.rs` + `kw.rs`" % len(wort))
    print("   %d Korpusdateien (ohne `beispiele/gift`), %d Passfunktionen mit Itemzugriff"
          % (len(korpusdateien()), len(fn_liest)))
    print()

    zusammen, offen, sammler = v1_konstruktpaare(wort, fn_liest, schranke)
    print("-- V1  Konstruktpaar ohne gemeinsame Passfunktion: %d von %d --"
          % (len(offen), len(zusammen)))
    print("   Schranke %d (= die Haelfte von %d): eine Funktion, die MEHR anfasst, laeuft"
          % (schranke, len(wort)))
    print("   ueber den Baum und verdrahtet nichts. %d so ausgeschlossen:" % len(sammler))
    for datei, name, zeile, n in sorted(sammler, key=lambda x: -x[3]):
        print("      %-20s %-24s %s:%d" % (name, "%d Itemarten" % n, datei, zeile))
    print("   **Und die Kurve steht daneben, weil die Zahl an diesem Knopf haengt:**")
    for s in sorted({1, 2, 3, 4, 6, 8, schranke, len(wort)}):
        _, o2, w2 = v1_konstruktpaare(wort, fn_liest, s)
        print("      Schranke %2d -> %3d offen  (%d Funktionen ausgeschlossen)"
              % (s, len(o2), len(w2)))
    for (x, y), n in sorted(offen.items(), key=lambda z: (-z[1], z[0]))[
            : None if a.lang else 12]:
        print("      %-12s / %-12s  in %d Korpusdatei(en)" % (x, y, n))
    if not a.lang and len(offen) > 12:
        print("      ... %d weitere, `--lang` zeigt alle" % (len(offen) - 12))
    print()

    alle_m, doppelt = v2_doppelregister()
    print("-- V2  dasselbe Oder-Muster an mehreren Stellen: %d von %d --"
          % (len(doppelt), len(alle_m)))
    for k, v in sorted(doppelt.items(), key=lambda x: -len(x[1])):
        print("      %dx  %s" % (len(v), ", ".join(sorted(k))[:78]))
        print("          %s" % ", ".join(v))
    print()

    stellen, gruende = v3_erzeugerweigerung()
    print("-- V3  Pruefer gruen, Erzeuger `C001`: %d Stellen in `emit.rs` --" % len(stellen))
    print("   Jede ist ein Programm, das drei Stufen passiert und an der vierten steht.")
    if a.lang:
        for g in sorted(set(gruende)):
            print("      %s" % g[:96])
    print()

    getragen, ungelesen, feldnenner = v4_klauseln()
    if getragen is None:
        print("ABBRUCH: `pruefe-klauseln.py` antwortete nicht -- V4 FEHLT, und eine")
        print("  fehlende Zahl ist keine Null. Was dahinter steht, waere eine Summe mit")
        print("  einem leeren Summanden.", file=sys.stderr)
        return 2
    v4 = getragen + ungelesen
    print("-- V4  Klausel ohne Pass, aus `pruefe-klauseln.py`: %d von %d Feldnamen --"
          % (v4, feldnenner))
    print("      %d nur getragen (emit/zeugnis), %d ungelesen" % (getragen, ungelesen))
    print()

    woerter, ohne = v5_angebot_ohne_pflicht()
    print("-- V5  reserviertes Wort ohne Korpusstelle: %d von %d --" % (len(ohne), len(woerter)))
    for x in ohne:
        print("      %s" % x)
    print()

    summe = len(offen) + len(doppelt) + len(stellen) + v4 + len(ohne)
    print("== VERDRAHTUNGSZAHL: %d ==" % summe)
    print("   V1 %d + V2 %d + V3 %d + V4 %d + V5 %d."
          % (len(offen), len(doppelt), len(stellen), v4, len(ohne)))
    print("   **Und was diese Summe NICHT ist: eine Anzahl von Fehlern.** Fuenf Formen mit")
    print("   fuenf Nennern addieren sich zu einer Summe von Formen. Die einzige Aussage,")
    print("   die sie traegt: die Klasse ist nicht acht Faelle gross (W25).")
    print()

    print("== DIE EICHUNG: was das Werkzeug von seinen eigenen sechs sieht ==")
    gesehen = 0
    for fall, form, wieso in EICHUNG:
        gesehen += form is not None
        print("   %-8s %-30s %s" % (form or "BLIND", fall, wieso))
    print()
    print("   **%d von 6 gesehen, %d blind.** Das ist der Nenner dieser Zahl und nicht ihre"
          % (gesehen, 6 - gesehen))
    print("   Beschriftung: was von Hand gefunden wurde, findet dieses Werkzeug zur Haelfte")
    print("   NICHT wieder. Jede Zahl oben ist damit eine UNTERE Schranke (W10) -- sie")
    print("   verpflichtet und spricht nicht frei.")
    print()
    print("   Was ungemessen bleibt, benannt statt verschwiegen:")
    print("     * die drei blinden Faelle oben -- alle drei sind ABSICHTEN, keine Muster")
    print("     * ob ein offenes Paar aus V1 verdrahtet WERDEN SOLL: `Konst/Reason` steht")
    print("       in 14 Dateien zusammen und hat vermutlich nichts miteinander zu tun")
    print("     * ob zwei Register aus V2 dasselbe sagen SOLLEN -- die schaerfere Frage")
    print("     * `beispiele/gift` ist nicht im Korpus: was nur dort zusammensteht, faellt")
    print("       aus V1 und V5 heraus")
    print("     * V3 zaehlt Weigerungen, nicht ihre BERECHTIGUNG -- eine Weigerung, auf die")
    print("       man baut, ist eine Zusage, und keine dieser %d ist hier geprueft" % len(stellen))
    print("     * **und der teuerste Blindfleck steht an einem Paar, das dieses Werkzeug")
    print("       SELBST veranlasst hat:** `H102` verdrahtet seit dem 2026-08-31 `entry`")
    print("       und `lock` in `kontexte.rs`, und `Entry / Lock` steht oben trotzdem")
    print("       offen. Die Kopplung laeuft ueber die prueferinterne `Kontext`-Struktur,")
    print("       nicht ueber `ItemArt::Entry` in derselben Funktion. *V1 sieht Syntax,")
    print("       nicht Datenfluss* -- wer eine Zwischenstruktur baut, verschwindet aus")
    print("       dieser Zaehlung, und das macht die 32 zu einer OBEREN Schranke fuer")
    print("       V1 statt zu einer unteren.")
    abschnitt.fertig()
    return 0


if __name__ == "__main__":
    sys.exit(abschnitt.fahre(main))
