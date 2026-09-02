#!/usr/bin/env python3
"""**Die Ratsche ueber dem Wortschatz -- und sie steht auf ZWEI Marken.**

    ./instrumente/zaehle-wortschatz.py [--je-wort]

`OA1`/`PLAN-HARDWARE.md` §11 nennt den Posten und die Regel:

> **Ein neues Wort nennt entweder das Wort, das es abloest, oder die Messung, warum keine
> vorhandene Form es traegt.**

**Die Regel hat zwei Haelften, und darum hat dieser Waechter zwei Marken.** Die erste zaehlt
die Woerter: wer eines abloest, laesst sie stehen, wer eines hinzufuegt, hebt sie. Die zweite
zaehlt die Woerter OHNE einen Grund am Eintrag: wer die Messung hinschreibt, laesst sie
stehen, wer schweigt, hebt sie.

    neues Wort, Grund dabei, nichts abgeloest    Woerter STEIGT      -> rot
    neues Wort, kein Grund                       BEIDE steigen       -> zweimal rot
    ein Wort gegen ein anderes getauscht         beide bleiben       -> gruen
    ein Wort faellt ersatzlos                    Woerter FAELLT      -> gruen

*Das ist die Regel, mechanisch: „entweder abloesen oder begruenden" ist genau die
Konjunktion, unter der beide Marken halten.*

WARUM DIE ZAHL, DIE HIER STAND, FALSCH WAR
-------------------------------------------
`PLAN.md` und `PLAN-HARDWARE.md` §11 buchten **234 Woerter**. Nachgezaehlt sind es **222**,
und der Irrtum ist reproduzierbar:

    grep -oE '"[a-z_][a-z0-9_]*"' kw.rs | sort -u | wc -l     ->  234

Der Ausdruck nimmt jede kleingeschriebene Zeichenkette der Datei, also auch die **15** aus
den Kommentaren (`zustand`, `naechst`, `plaetze`, `stapel`, …), und verliert die **3**
grossgeschriebenen Woerter (`None`, `Self`, `Some`), die keine Kommentarzeile je nennt.
*Zwei Fehler in verschiedene Richtungen, netto zwoelf zu viel* -- und weil 234 plausibel
aussah, hat sie niemand nachgerechnet. **Dieselbe Klasse wie `W16`: ein Messgeraet, das
seinen eigenen Rand mitzaehlt.**

> Die Grundgesamtheit ist deshalb hier **der Makroaufruf** `wortschatz! { … }` und nicht die
> Datei. Was ausserhalb der Klammern steht, ist Prosa und kein Wort.

WAS DIESE RATSCHE NICHT FAENGT -- und die Zahl steht in der Ausgabe
--------------------------------------------------------------------
**Ein Wort, das ein anderes still weiter macht, waechst nicht in der Zahl.** `invariant`
stand an einer `table` und steht seit dem 2026-08-28 an allen drei Schleifenformen --
dieselbe Reichweite wie ein neues Wort, und der Zaehler hat sich nicht bewegt. `SYNTAX.md`
sagt es selbst: *„It is not a new word."*

Der Waechter misst darum die zweite Groesse mit: die **Stellungen**, also Terminal mal
EBNF-Regel. Sie ist **keine Ratsche** -- sie SOLL steigen, denn genau das heisst „ein Wort
statt siebzehn". *Die zwei Zahlen muessen in verschiedene Richtungen laufen, sonst ist der
Handel keiner:* faellt die erste, ohne dass die zweite steigt, wurde Ausdruck verloren und
nicht getauscht.
"""
import pathlib
import re
import sys
from collections import Counter

# **Whoever leaves mid-run says WHERE** -- the shared form, out of `abschnitt.py`.
# `sys.path` gets the tool's own directory because this file is also LOADED by
# `abnahme.py` (via `importlib`), and then `sys.path[0]` is the working directory.
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import abschnitt  # noqa: E402

W = pathlib.Path(__file__).resolve().parent.parent
KW = W / "crates" / "gabbro-syntax" / "src" / "kw.rs"
SYNTAX = W / "dokumente" / "SYNTAX.md"

# **THE FIRST MARK -- the count.** A ratchet, not a target: it may fall, never rise.
#
# 2026-09-01, booked at 222 (213 reserved, 9 contextual). The number the plans carried was
# 234 and was never measured; the docstring above holds the arithmetic of the error.
# **Whoever raises this line writes beside it WHICH word was displaced, or the measurement
# saying that no existing form carries the new one.** A raise without one of the two is the
# growth rule this mark exists against.
#
# **222 -> 221 on the same day, and by the ratchet's OWN first case.** `decreasing` fell: it
# stood as a third run form at `traverse` while the emitter had written down since
# 2026-08-20 that it is not one -- *three modes, two runs*. The witness became a clause,
# `by ( unvisited | consuming ) [ decreases expr ]`, and the word it is spelled with was
# already in the vocabulary («K5.4», at a `fn` head, the same measure over the recursion).
# **Nothing new was added**, and the position count stayed at 333 while this denominator
# fell -- 1,49 became 1,50 per terminal. *That is the shape of a trade; a fall in both would
# have been a loss.*
MARKE_WOERTER = 221

# **THE SECOND MARK -- words without a reason at the entry.** Also a ratchet, downwards.
#
# 2026-09-01, booked at 210 of 222. A "reason" is a comment block of at least two lines
# directly above the entry in `kw.rs`, section separators not counted. Twelve words carry
# one today: `refines`, `insert`, `w1c`, `backed`, `rcu`, `order`, `retires`, `entrust`,
# `observed`, `occupied`, `f32`, `Some`.
#
# **Two-hundred-ten missing reasons are NOT a backlog to work off**, and that is why this is
# a ratchet and not a target. The rule is about the NEXT word. What the mark buys is that
# the next one cannot arrive silently -- and every reason written on the way past lowers it.
#
# **210 -> 208 on 2026-09-01**, out of the same change: one word left the population, and the
# ledger entry for its fall sits above `unvisited`, which therefore now carries a reason too.
# *A mark that is only ever touched on the way up is a mark and not a ratchet* -- so it
# travels down with the measurement, in the same run that measured it.
MARKE_OHNE_GRUND = 208

# **The single lowering theorem, booked with its address.** `beweise/Absenkung_Parametrisch.thy`
# holds `ops relabel` against the emitted C -- and its result is that the sentence *"the
# emitted thing computes the model function"* is FALSE at the free slot. It is the only
# theorem in the tree that makes the statement at all.
#
# **It is booked and not derived, and the reason is a measurement:** a word-boundary match of
# the 222 words over all fifteen theories answers `81`, and that number is worthless -- it
# counts `r`, `w`, `x`, `in`, `to`, `if`, `else`, `and`, `or`, `at`, `max`, `min` because
# Isabelle spells ordinary identifiers the same way Gabbro spells words. *A loose upper bound
# beside a booked exact number is the honest pair; a loose number alone would be a coverage
# claim.* The upper bound is printed, with its refutation.
ABSENKUNGSSAETZE = 1
ABSENKUNG_ADRESSE = "beweise/Absenkung_Parametrisch.thy -- `ops relabel`, und der Satz FAELLT"
# **An address is a claim about a place, and nothing went there** (2026-09-02). The two
# lines above are a Python constant printed as a standing fact about a theorem in another
# language: that the file exists, that it is about `ops relabel`, and that the sentence
# falls. None of the three was checked -- a rename, a move or a repair of that theorem would
# leave this line saying something false, with nothing to catch it.
#
# The first two are text and are checked here. The third is not text and is NOT checked
# here: whether the theorem still goes through is what `isabelle build` says, and the way
# there is `./instrumente/pruefe-beweise.sh`. **The run says which of the three it verified**
# rather than letting the printed sentence imply all three.
ABSENKUNG_DATEI = "beweise/Absenkung_Parametrisch.thy"
ABSENKUNG_NAMEN = ("relabel_am_freien_platz_ist_wirkungslos",
                   "absenkung_geht_am_freien_platz_auseinander")

# Character material: single-character terminals come out of ranges and are not words.
# Same exception, and for the same reason, as in `pruefe-wortschatz.py`.
ZEICHENREGELN = {"letter", "digit", "hexdigit", "char", "quote", "newline", "hex", "bin"}

EINTRAG = re.compile(
    r'^\s*([A-Za-z][A-Za-z0-9_]*)\s*=>\s*"([^"]*)"\s*,\s*(res|ctx)\s*;')


def woerter(quelle=None):
    """The vocabulary, out of the MACRO CALL and not out of the file.

    Returns `[(variant, text, class, reason_lines)]` in table order. `reason_lines` counts
    the comment lines directly above the entry, section separators excluded -- that is the
    mechanical form of *"names the measurement why no existing form carries it"*.
    """
    text = (quelle or KW).read_text(encoding="utf-8")
    zeilen = text.splitlines()
    try:
        start = next(i for i, z in enumerate(zeilen) if z.startswith("wortschatz! {"))
    except StopIteration:
        return []
    aus = []
    for i in range(start, len(zeilen)):
        m = EINTRAG.match(zeilen[i])
        if not m:
            continue
        j, block = i - 1, []
        while j > start and zeilen[j].lstrip().startswith("//"):
            z = zeilen[j].lstrip()[2:].strip()
            # A separator (`-- Domains ------`) is furniture, not a reason.
            if z and not re.match(r"^-{2,}", z):
                block.append(z)
            j -= 1
        aus.append((m.group(1), m.group(2), m.group(3), len(block)))
    return aus


def korpusdateien():
    """The CLEAN corpus -- `beispiele/gift` deliberately left out.

    A poison sample is a file that is SUPPOSED to fall; a word occurring only there is not
    in use, it is under test. Same population as `zaehle-verdrahtung.py::korpusdateien`.
    """
    q = sorted(W.glob("beispiele/*.gab")) + sorted(W.glob("messung/**/*.gab"))
    return [p for p in q if "/gift/" not in str(p)]


def traeger(wortliste):
    """Per word: in how many corpus files does it stand?

    **A text match, and that is the limit of it.** `parent` as a slot field name counts here
    like `parent` as a domain edge -- the nine contextual words are identifiers everywhere
    else, and this measurement cannot tell the two apart. It is therefore an UPPER bound on
    use and a LOWER bound on the reserved-only set (W10).
    """
    texte = []
    for p in korpusdateien():
        try:
            roh = p.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        texte.append("\n".join(z for z in roh.splitlines()
                               if not z.lstrip().startswith("--")))
    zahl = {}
    for w in wortliste:
        muster = re.compile(r"\b%s\b" % re.escape(w))
        zahl[w] = sum(1 for t in texte if muster.search(t))
    return zahl, len(texte)


def stellungen():
    """Terminal x EBNF rule -- the size the word count does NOT see.

    Returns `(positions_per_terminal, number_of_rules)`.
    """
    md = SYNTAX.read_text(encoding="utf-8")
    roh = "\n".join(re.findall(r"```ebnf\n(.*?)```", md, re.S))
    # Comments out FIRST: the rule regex looks for the `;` at end of line, and a trailing
    # `(* … *)` makes it swallow the following rule. Same trap as in `pruefe-wortschatz.py`.
    ebnf = re.sub(r"\(\*.*?\*\)", "", roh, flags=re.S)
    regeln = re.findall(r"^\s*([a-z][a-z0-9_]*)\s*=(.*?);\s*$", ebnf, re.M | re.S)
    zeichenmaterial = set()
    for k, v in regeln:
        if k in ZEICHENREGELN:
            zeichenmaterial |= set(re.findall(r'"([^"]*)"', v))
    zahl = Counter()
    for _, v in regeln:
        for t in set(re.findall(r'"(@?[A-Za-z_][A-Za-z0-9_]*)"', v)):
            if t not in zeichenmaterial and (len(t) > 1 or t.isupper()):
                zahl[t] += 1
    return zahl, len(regeln)


def beweisdeckung(wortliste):
    """The LOOSE upper bound: which words does any theory name in its text?

    Printed with its refutation, never alone -- see `ABSENKUNGSSAETZE`.
    """
    thy = sorted((W / "beweise").glob("*.thy"))
    if not thy:
        return None, 0
    alle = "\n".join(p.read_text(encoding="utf-8", errors="replace") for p in thy)
    return [w for w in wortliste if re.search(r"\b%s\b" % re.escape(w), alle)], len(thy)


def main():
    je_wort = "--je-wort" in sys.argv

    if not KW.is_file():
        print(f"ABBRUCH: {KW} fehlt -- der Gegenstand dieses Waechters ist der Wortschatz,",
              file=sys.stderr)
        print("  und ohne ihn wurde NICHTS gemessen.", file=sys.stderr)
        return 2
    if not SYNTAX.is_file():
        print(f"ABBRUCH: {SYNTAX} fehlt -- ohne Grammatik gibt es keine Stellungen,",
              file=sys.stderr)
        print("  und die Blindstelle dieser Ratsche waere unbenannt statt gemessen.",
              file=sys.stderr)
        return 2

    liste = woerter()
    # **W17: an empty population is a green verdict about nothing.** A `kw.rs` this tool
    # cannot read looks exactly like a vocabulary that shrank to zero -- and the first mark
    # would hold, triumphantly.
    if not liste:
        print("ABBRUCH: der Makroaufruf `wortschatz! { … }` gab NULL Eintraege her.")
        print("  Eine leere Menge unterschreitet jede Ratsche, und das ist kein Ergebnis,")
        print("  sondern eine Datei, die dieses Werkzeug nicht lesen konnte. NICHTS gemessen.")
        return 2

    n = len(liste)
    res = sum(1 for e in liste if e[2] == "res")
    ctx = n - res
    ohne_grund = [e[1] for e in liste if e[3] < 2]
    mit_grund = [e[1] for e in liste if e[3] >= 2]

    print("== Die Zahl: %d Woerter ==" % n)
    print("   %d reserviert · %d kontextuell" % (res, ctx))
    print("   Marke %d -- eine Ratsche, keine Zielzahl: sie darf fallen, nicht steigen."
          % MARKE_WOERTER)
    print()

    print("== Der Grund am Eintrag: %d von %d ==" % (len(mit_grund), n))
    print("   %s" % ", ".join(mit_grund))
    print("   %d ohne, Marke %d -- auch das eine Ratsche, und sie laeuft nach unten."
          % (len(ohne_grund), MARKE_OHNE_GRUND))
    # **The number in the sentence is the COMPUTED one.** The first draft wrote `210` into
    # the prose beside a number this run works out, and the two disagreed the moment a word
    # fell -- a hand-kept figure running parallel to the truth, one line apart. *Trap 80, in
    # a tool built against exactly that.*
    print("   **Die %d sind kein Rueckstand, den jemand abarbeiten soll.** Die Regel gilt"
          % len(ohne_grund))
    print("   dem NAECHSTEN Wort; was die Marke kauft, ist, dass es nicht still ankommt.")
    print()

    zahl, ndateien = traeger([e[1] for e in liste])
    ohne_stelle = sorted(w for w, k in zahl.items() if k == 0)
    print("== Der Nenner: %d benutzt, %d nur reserviert ==" % (n - len(ohne_stelle),
                                                               len(ohne_stelle)))
    print("   ueber %d Korpusdateien (`beispiele/*.gab` + `messung/**/*.gab`, ohne `gift/`)"
          % ndateien)
    if ndateien == 0:
        print("   ABBRUCH: NULL Korpusdateien -- ueber einer leeren Menge ist jedes Wort")
        print("   „nur reserviert\", und die Zahl darueber waere eine Aussage ueber nichts.")
        return 2
    print("   nur reserviert: %s" % (", ".join(ohne_stelle) or "(keines)"))
    # **`k == 0` gets tested FIRST, and that is not cosmetic.** The first draft asked
    # `k < 10` before it asked `k == 0`, so the word with no site at all landed in the
    # `3-9` column -- the bucket table said 222 while the line above it said 221 + 1, and
    # the two disagreed by exactly the case the whole section is about.
    v = Counter()
    for w, k in zahl.items():
        v["0" if k == 0 else "1 Datei" if k == 1 else "2 Dateien" if k == 2
          else "3-9" if k < 10 else ">=10"] += 1
    print("   Traeger je Wort:  " + " · ".join(
        "%s %d" % (s, v[s]) for s in ("0", "1 Datei", "2 Dateien", "3-9", ">=10") if v[s]))
    print("   **Ein Textabgleich, und das ist seine Grenze:** `parent` als Slotfeldname")
    print("   zaehlt hier wie `parent` als Baumkante. Die 9 kontextuellen Woerter sind")
    print("   ueberall sonst Bezeichner -- also eine OBERE Schranke fuer „benutzt\" und")
    print("   eine UNTERE fuer „nur reserviert\" (W10).")
    if je_wort:
        for w, k in sorted(zahl.items(), key=lambda x: (x[1], x[0])):
            print("      %-14s %d" % (w, k))
    print()

    genannt, nthy = beweisdeckung([e[1] for e in liste])
    print("== Die Beweisschuld: %d Absenkungssatz auf %d Woerter ==" % (ABSENKUNGSSAETZE, n))
    print("   %s" % ABSENKUNG_ADRESSE)
    p_abs = W / ABSENKUNG_DATEI
    if not p_abs.is_file():
        print("   ABBRUCH: diese Datei gibt es nicht. Die Zeile darueber ist eine Adresse,")
        print("   und eine Adresse ohne Ort ist keine Buchung. *Was hier steht, waere dann")
        print("   eine Behauptung ueber einen Beweis, den niemand mehr findet.*")
        return 2
    t_abs = p_abs.read_text(encoding="utf-8")
    fehlend = [s for s in ABSENKUNG_NAMEN if s not in t_abs]
    if fehlend:
        print("   ABBRUCH: die Datei steht da, aber diese Saetze nicht mehr: %s"
              % ", ".join(fehlend))
        print("   Umbenannt oder entfernt -- so oder so sagt die Adresse etwas anderes,")
        print("   als sie behauptet.")
        return 2
    print("   geprueft: die Datei steht da und traegt beide Saetze (%s)."
          % ", ".join(ABSENKUNG_NAMEN))
    print("   NICHT geprueft: ob der Satz heute noch faellt. Das sagt `isabelle build`,")
    print("   und der Weg dorthin ist `./instrumente/pruefe-beweise.sh`.")
    if genannt is None:
        print("   (`beweise/` fehlt -- die obere Schranke wurde NICHT erhoben)")
    else:
        print("   Die obere Schranke, und sie ist unbrauchbar: %d der %d Woerter stehen im"
              % (len(genannt), n))
        print("   Text der %d Theorien -- darunter `r`, `w`, `x`, `in`, `to`, `if`, `else`,"
              % nthy)
        print("   `and`, `or`, `at`, `max`, `min`. **Isabelle schreibt gewoehnliche")
        print("   Bezeichner so, wie Gabbro Woerter schreibt.** Die Zahl misst die")
        print("   Rechtschreibung und nicht die Deckung; sie steht hier, damit niemand sie")
        print("   ein zweites Mal erhebt und fuer eine Deckung haelt.")
    print("   **Damit ist die Ratsche ueber dem Wortschatz zugleich eine ueber der")
    print("   Beweisschuld:** jedes Wort ist eine erzeugte Form, und ein Satz deckt eine.")
    print()

    st, nregeln = stellungen()
    print("== Was diese Ratsche NICHT faengt ==")
    if not st:
        print("   ABBRUCH: NULL Terminale aus %d EBNF-Regeln -- die Blindstelle laesst sich"
              % nregeln)
        print("   ueber einer leeren Grammatik nicht messen, und unbenannt gehoert sie nicht")
        print("   in eine Ausgabe, die sonst wie eine vollstaendige aussieht.")
        return 2
    summe = sum(st.values())
    mehrfach = sorted(((t, k) for t, k in st.items() if k >= 2), key=lambda x: (-x[1], x[0]))
    print("   %d Stellungen (Terminal x Regel) auf %d Terminale in %d Regeln -- %s je Terminal"
          % (summe, len(st), nregeln, ("%.2f" % (summe / len(st))).replace(".", ",")))
    print("   Der Nenner ist %d und nicht %d: `@version`, `Held`, `O` und `TESTBUILD` sind"
          % (len(st), n))
    print("   Terminale und keine Woerter, `r`, `w` und `x` Woerter und keine Terminale.")
    print("   %d Terminale stehen in mehr als einer Regel; die zehn weitesten:" % len(mehrfach))
    print("      " + " · ".join("%s %d" % x for x in mehrfach[:10]))
    print()
    print("   **Diese Zahl ist KEINE Ratsche, und das ist der Punkt.** Sie soll steigen --")
    print("   `invariant` stand an einer `table` und steht seit dem 2026-08-28 an allen drei")
    print("   Schleifenformen, ohne dass ein Wort dazukam. Genau das heisst „ein Wort statt")
    print("   siebzehn\".")
    print("   *Die beiden Zahlen muessen in verschiedene Richtungen laufen, sonst ist der")
    print("   Handel keiner:* faellt die erste, ohne dass die zweite steigt, wurde Ausdruck")
    print("   verloren statt getauscht.")
    print()
    print("   Was ungemessen bleibt, benannt statt verschwiegen:")
    print("     * **eine neue Stellung eines vorhandenen Wortes** -- die Zahl oben zaehlt")
    print("       sie, die Ratsche faengt sie nicht, und sie ist die Form, in der der")
    print("       Wortschatz seit dem 2026-08-28 nachweislich gewachsen ist")
    print("     * **eine Mehrwortform aus vorhandenen Woertern** (`nested masked`,")
    print("       `chain(a, b) in`, `lock … masks irqs`) -- neue Bedeutung, kein neues Wort;")
    print("       `namen.rs:294` fuehrt vier davon und keine Zahl zaehlt sie")
    print("     * **ein neuer Zweig an einem vorhandenen Wort** -- eine `ItemArt`-Variante")
    print("       mehr ist eine Sprachaenderung und bewegt weder Marke noch Stellung")
    print("     * ob ein Grundblock zum Wort DARUNTER gehoert: die Zuordnung geht ueber")
    print("       Nachbarschaft im Text. Wer ein Wort direkt hinter ein begruendetes")
    print("       einfuegt, erbt dessen Grund -- die zweite Marke faengt das nicht, die")
    print("       erste schon")
    print("     * ob ein Grund STIMMT. Zwei Zeilen ueber einem Eintrag sind zwei Zeilen.")

    abschnitt.fertig()

    befunde = 0
    if n > MARKE_WOERTER:
        print()
        print("  RATSCHE GEBROCHEN: %d Woerter, gebucht sind %d." % (n, MARKE_WOERTER))
        print("  **Ein neues Wort nennt entweder das Wort, das es abloest, oder die Messung,")
        print("  warum keine vorhandene Form es traegt.** Steht das eine da, faellt ein")
        print("  anderes Wort und diese Zahl bleibt; steht das andere da, gehoert es an den")
        print("  Eintrag in `kw.rs` -- und diese Marke wird MIT der Begruendung gehoben,")
        print("  nicht vor ihr.")
        befunde = 1
    if len(ohne_grund) > MARKE_OHNE_GRUND:
        print()
        print("  RATSCHE GEBROCHEN: %d Woerter ohne Grund am Eintrag, gebucht sind %d."
              % (len(ohne_grund), MARKE_OHNE_GRUND))
        print("  Ein Grund ist ein Kommentarblock von mindestens zwei Zeilen unmittelbar")
        print("  ueber dem Eintrag. Er steht dort und nicht in der Commit-Nachricht, weil")
        print("  er mit dem Wort wandert.")
        befunde = 1
    if n < MARKE_WOERTER or len(ohne_grund) < MARKE_OHNE_GRUND:
        print()
        print("  Die Marken sind GEFALLEN: %d/%d Woerter, %d/%d ohne Grund. Sie gehoeren"
              % (n, MARKE_WOERTER, len(ohne_grund), MARKE_OHNE_GRUND))
        print("  in diesem Lauf nachgezogen -- eine Ratsche, die nur beim Steigen angefasst")
        print("  wird, ist eine Marke und keine Ratsche.")
        befunde = 1
    return befunde


# **The speech test, and it runs over an INVENTED source.**
#
# *A guardian that only ever reads its own file measures how well that file suits it.* The
# probe builds a vocabulary of three entries -- one with a reason, two without -- and demands
# exactly those three numbers. When it falls the return code is 2 and not 1: nothing was
# measured then, and a number out of a broken counter is worse than no number.
# speech_test: begin
def sprechprobe():
    import tempfile
    quelle = (
        "//! Kopf.\n"
        "wortschatz! {\n"
        "    // -- Struktur ----------------------------------------------\n"
        "    Alpha         => \"alpha\",         res;\n"
        "    // **Ein Grund**, zwei Zeilen lang, und er gehoert zu `beta`.\n"
        "    // Die zweite Zeile ist da, damit der Block zaehlt.\n"
        "    Beta          => \"beta\",          res;\n"
        "    Gamma         => \"gamma\",         ctx;\n"
        "}\n"
        "// \"schwindel\" steht in einem Kommentar und ist KEIN Wort.\n"
    )
    with tempfile.TemporaryDirectory() as d:
        p = pathlib.Path(d) / "kw.rs"
        p.write_text(quelle, encoding="utf-8")
        aus = woerter(p)
    texte = [w for _, w, _, _ in aus]
    klassen = [k for _, _, k, _ in aus]
    gruende = [g for _, _, _, g in aus]
    fehler = []
    if texte != ["alpha", "beta", "gamma"]:
        fehler.append("die drei Woerter: %r" % (texte,))
    if "schwindel" in texte:
        fehler.append("ein Kommentarwort wurde mitgezaehlt -- genau der Irrtum der 234")
    if klassen != ["res", "res", "ctx"]:
        fehler.append("res/ctx: %r" % (klassen,))
    if gruende != [0, 2, 0]:
        fehler.append("Grundzeilen (Abschnittsstrich darf nicht zaehlen): %r" % (gruende,))
    return fehler


# speech_test: end


if __name__ == "__main__":
    if "--sprechprobe" in sys.argv:
        f = sprechprobe()
        for z in f:
            print("  SPRECHPROBE GESCHEITERT: %s" % z, file=sys.stderr)
        print("    Sprechprobe: %s" % ("ok" if not f else "GESCHEITERT"))
        sys.exit(2 if f else 0)
    f = sprechprobe()
    if f:
        for z in f:
            print("ABBRUCH: die Sprechprobe faellt -- %s" % z, file=sys.stderr)
        print("  Dieser Zaehler kann seinen eigenen Gegenstand nicht lesen; jede Zahl",
              file=sys.stderr)
        print("  darunter waere geraten. NICHTS gemessen.", file=sys.stderr)
        sys.exit(2)
    sys.exit(abschnitt.fahre(main))
