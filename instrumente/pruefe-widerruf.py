#!/usr/bin/env python3
"""**Widerrufene Saetze -- die Klasse, die dreimal von Hand gefunden wurde.**

`pruefe-todo.py` haelt `TODO.md` gegen sechs Klassen, darunter *stehengebliebene Zahl*. Er
sieht **genau eine Datei.** Am 2026-08-19 standen in `dokumente/PLAN.md` sechs Saetze, die
das Gegenteil des Gebauten sagten -- vier Abschnitte ueber dem Bauplan, der sie widerlegt.

    Zeile 1742  "Gleitkomma -- nicht im Kern"
    Zeile 1826  "M1 ist ueber Intervallen ganzer Zahlen gebaut"
    Zeile 1983  3D-Renderer: fuer immer draussen
    Zeile 2018  "hat keinen Bereich, den M101 vergleichen koennte"
    Zeile 2150  "opaque zum Beissen bringen -- eingeschoben"
    Zeile 2158  Punkt 5: nicht bauen

**Der Unterschied zu einer bloszen Ungenauigkeit:** ein widerrufener Satz sagt nicht *"hier
ist noch etwas offen"*, sondern *"das geht nie"*. Er verhindert Arbeit statt sie zu
verzoegern -- und er tut es leise, weil er wie ein Ergebnis aussieht.

**Die Ausnahme ist die Durchstreichung.** Der Ordner streicht durch, er loescht nicht:
`~~alt~~ **neu**` ist die vorhandene Form (aarch64, Festkomma, das Memo). Ein Vorkommen in
einem durchgestrichenen Absatz ist deshalb erlaubt -- ebenso eines in einem Block zwischen
`<!-- widerruf:aus -->` und `<!-- widerruf:an -->`, damit ein Widerrufsregister den
widerrufenen Satz ZITIEREN kann.

**Und die Grenze, damit die Zahl nicht mehr verspricht als sie misst:** der Waechter findet
nur, was jemand als widerrufen aufgeschrieben hat. *Er ist ein Gedaechtnis, kein Urteil.*

    ./instrumente/pruefe-widerruf.py
"""
import pathlib
import re
import sys

# **Whoever leaves mid-run says WHERE** -- the shared form, out of `abschnitt.py`.
# `sys.path` gets the tool's own directory because this file is also LOADED by
# `abnahme.py` (via `importlib`), and then `sys.path[0]` is the working directory.
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import abschnitt  # noqa: E402

W = pathlib.Path(__file__).resolve().parent.parent

# Five fields per entry, and without all five it is not accepted (TOOTH 1):
#   muster  what must no longer stand there -- IN BOTH LANGUAGES
#   datum   when it was revoked
#   grund   WHAT revoked it -- a file, an example, an identifier
#   ersatz  what holds instead
#   probe   two specimen sentences, German and English; BOTH have to fall (TOOTH 2)
#
# **`probe` and the second language became mandatory on 2026-09-01, and the reason is this
# guardian's construction.** It looks for what must NOT stand there. A pattern that hits
# nothing is therefore INDISTINGUISHABLE from a tree without an occurrence -- the miss and
# the pass print the same line. Over 170 files moving into English that means: every
# German-bound revocation drops out silently at the moment its document is translated, and
# the run over it reports `ALL PASS`.
#
# > *The other guardians go red when their pattern loses its object. This one cannot* -- its
# > green IS the empty result. **So the proof has to be carried, not inferred:** each entry
# > brings one sentence per language, and the speech test demands that both fall.
WIDERRUFE = [
    dict(kennung="WF1",
         muster=r"[Gg]leitkomma[^.\n]{0,40}nicht im Kern"
                r"|kein[e]? Gleitkomma[^.\n]{0,20}im Kern"
                r"|[Nn]o floating\s*\n?\s*point in the core"
                r"|[Ff]loating[- ]point[^.\n]{0,40}not in the (?:core|kernel)",
         datum="2026-08-18", grund="«F1», `typen.rs`: `Typ::Gleitkomma(FBereich)`",
         ersatz="`f32`/`f64` mit Bereich, NaN- und Unendlichbit -- `beispiele/26-gleitkomma.gab`",
         probe=("Gleitkomma ist nicht im Kern, und dabei bleibt es.",
                "Floating-point is not in the core, and that is that.")),
    # **`\*\*?` demands at least one asterisk** -- so the unemphasised German sentence, the
    # one that actually stood in `PLAN.md`:1826, never matched. Found 2026-09-01 by the
    # specimen sentence, not by the eye.
    dict(kennung="WF2",
         muster=r"M1 ist (?:ueber|über) Intervallen (?:\*\*)?ganzer(?:\*\*)? Zahlen"
                r"|M1 is (?:built )?over intervals of \*\*?integers\*\*?"
                r"|M1 is (?:built )?over integer intervals",
         datum="2026-08-18", grund="`typen.rs`: `FBereich { breite, lo, hi, kann_nan, … }`",
         ersatz="M1 traegt beide Bereichsarten; `M101` vergleicht auch Gleitkommabereiche",
         probe=("M1 ist ueber Intervallen ganzer Zahlen gebaut.",
                "M1 is built over intervals of **integers**.")),
    dict(kennung="WF3",
         muster=r"keinen Bereich, den `M101` vergleichen"
                r"|no range (?:that )?`M101` (?:could|can) compare",
         datum="2026-08-18", grund="`m1.rs`: der Gleitkommazweig von `passt`",
         ersatz="`M101` vergleicht ihn, und `F001` prueft die zwei Bits daneben",
         probe=("Es hat keinen Bereich, den `M101` vergleichen koennte.",
                "It has no range that `M101` could compare.")),
    dict(kennung="WF4",
         muster=r"Gleitkomma[^\n]{0,60}f(?:[uü]|ue)r immer drau(?:[sß]|ss)en"
                r"|f(?:[uü]|ue)r immer drau(?:[sß]|ss)en[^\n]{0,60}Gleitkomma"
                r"|[Ff]loating[- ]point[^\n]{0,60}out for good"
                r"|out for good[^\n]{0,60}[Ff]loating[- ]point",
         datum="2026-08-18", grund="dieselbe Spalte der Drei-Spalten-Tabelle",
         ersatz="3D-Renderer: teilweise heute, ganz nach der Erweiterung",
         probe=("3D-Renderer: Gleitkomma bleibt fuer immer draussen.",
                "3D renderer: floating-point stays out for good.")),
    # **`h[aä]lt` never matched `haelt`** -- found on 2026-09-01 while writing the specimen
    # sentence for this entry. The folder writes the umlaut both ways, and the class this
    # guardian stands against does not care which one an author picked. *A specimen sentence
    # is a better reader of a pattern than the eye that wrote it.*
    dict(kennung="WD1",
         muster=r"`opaque`[^\n]{0,30}h(?:[aä]|ae)lt nicht"
                r"|undurchsichtige[rn]? Typ[^\n]{0,40}keine Wirkung"
                r"|`opaque`[^\n]{0,30}does not hold"
                r"|opaque type[^\n]{0,40}(?:has )?no effect",
         datum="2026-08-18", grund="`D003` (die Rechnung) und `D004` (die Modulgrenze)",
         ersatz="`opaque` beisst; offen ist die TUER, nicht der Biss",
         probe=("Der `opaque`-Riegel haelt nicht.",
                "The `opaque` bolt does not hold.")),
    dict(kennung="WE1",
         muster=r"[Kk]ein Pass liest `?ensures`?"
                r"|`ensures` (?:wird von keinem Pass gelesen|liest niemand)"
                r"|Tippfehler in einem `ensures` f[aä]llt nicht"
                r"|`ensures`[^\n]{0,40}gez[aä]hlt, nie gehalten"
                r"|[Kk]ein Pass liest Pr[aä]dikate"
                r"|prueft auch keiner ihre NAMEN|prüft auch keiner ihre Namen"
                r"|[Nn]o pass reads `?ensures`?"
                r"|`ensures` (?:is read by no pass|is what nobody reads)"
                r"|[Aa] typo in an? `ensures` does not fall"
                r"|`ensures`[^\n]{0,40}counted, never held"
                r"|[Nn]o pass reads predicates"
                r"|nobody checks their (?:NAMES|names) either",
         datum="2026-08-18", grund="`m1.rs`: `ensures_pruefen` -- `M109`/`M110`/`M111`",
         ersatz="die WOHLGEFORMTHEIT wird geprueft (Namen, `result`, Herstellbarkeit); "
                "was offen bleibt, ist die EINLOESUNG durch den Rumpf",
         probe=("Kein Pass liest `ensures`.",
                "No pass reads `ensures`.")),
    dict(kennung="WB1",
         muster=r"«B24»[^\n]{0,80}(?:ist offen|bleibt offen|blockiert|eine Entscheidung, und sie ist die einzige)"
                r"|[Ww]as blockiert, ist der IP-Kopf"
                r"|«B24» is (?:an )?open"
                r"|`format` weigert sich f[uü]r jede davon"
                r"|Netzwerkstack[^\n|]{0,40}blockiert an"
                r"|blockiert an \*\*einer\*\* Entscheidung"
                r"|[Ww]hat blocks is the IP header"
                r"|[Nn]etwork stack[^\n|]{0,40}block(?:ed|s) (?:on|at)"
                r"|block(?:ed|s) on \*\*one\*\* decision",
         datum="2026-08-18", grund="`PFLICHTEN.md`:141/:155 -- entschieden; "
                                   "`beispiele/24-ip-kopf.gab` und `emit.rs`:1416 -- gebaut",
         ersatz="entschieden UND gebaut; seit 2026-08-19 auch im Pruefer (`N007`/`N008`)",
         probe=("«B24» ist offen und blockiert an **einer** Entscheidung.",
                "«B24» is open, and what blocks is the IP header.")),
    # **The decimal separator is part of the spelling** (2026-09-01). `1,9` is German, `1.9`
    # is English, and a pattern pinned to the comma stops reading the number the day the
    # sentence around it moves. *A figure is written in a language too.*
    dict(kennung="WM1",
         muster=r"(?:Kennzahl|metric|kennzahl)[^\n]{0,60}(?:>=|≥)\s*1[.,]9"
                r"|(?:>=|≥)\s*1[.,]90\b|(?:>=|≥)\s*1[.,]98\b|(?:>=|≥)\s*2[.,]03\b"
                r"|stands? (?:die Kennzahl|the metric)[^\n]{0,30}1[.,]9"
                r"|steht (?:die Kennzahl|the metric)[^\n]{0,30}1[.,]9",
         datum="2026-08-19", grund="`w` war an VERUS-Zeilen gemessen; Gabbro beweist in "
                                   "Isabelle/HOL, und dessen zehn Theorien tragen NULL W",
         ersatz="unbekannt, > 0,5 -- die untere Schranke ist ein Argument (W > 0), "
                "die obere hat heute niemand",
         probe=("Damit steht die Kennzahl bei >= 1,9.",
                "That puts the metric at >= 1.9.")),
    # **WK1, 2026-08-23.** The sentence stood on 2026-08-19 and was right then. The BUILD of
    # P6 refuted it two days later: `messung/P6.md` measures that 16 of the 23 genuinely open
    # obligations hang on exactly the body effect it declares dispensable.
    # *It is expensive because it makes the blocker look CHEAPER than it is* -- the class this
    # guardian stands against: a sentence that prevents work instead of merely delaying it.
    dict(kennung="WK1",
         muster=r"[Kk]eine Sprachsemantik n[oö]etig"
                r"|[Kk]eine Sprachsemantik n[oö]tig"
                r"|not an Isabelle semantics of Gabbro"
                r"|[Nn]o language semantics (?:is )?(?:needed|necessary|required)",
         datum="2026-08-21", grund="`messung/P6.md`: 16 der 23 offenen Pflichten sitzen "
                                   "an der Rumpfwirkung, 7 am Weltmodell",
         ersatz="die ISABELLE-SEMANTIK EINES GABBRO-RUMPFS ist der Blocker der Kennzahl, "
                "nicht die Bruecke -- `TODO.md`, Abschnitt DIE KENNZAHL",
         probe=("Dafuer ist keine Sprachsemantik noetig.",
                "No language semantics is needed for that.")),
    dict(kennung="WD2",
         muster=r"`opaque` zum Bei(?:[sß]|ss)en bringen[^\n]{0,30}\*\*eingeschoben\*\*"
                r"|[Bb]ring(?:ing)? `opaque` to bite[^\n]{0,30}\*\*inserted\*\*",
         datum="2026-08-18", grund="`m1.rs`:745, Gift 79 und vier Sprechproben",
         ersatz="gebaut; Punkt 3 der Reihenfolge ist zu",
         probe=("`opaque` zum Beissen bringen -- **eingeschoben**.",
                "Bringing `opaque` to bite -- **inserted**.")),
    # **WB2, entered 2026-08-25.** The sentence stood in the HEAD of stage 7 -- the place a
    # builder looks to see what is next -- and it did not say *"open"*, it said *"the
    # language does not have it"*. All four halves were built on 2026-08-21
    # (`messung/FNPTR.md`); the sentence stood four days longer than it was true.
    #
    # *This guardian could not catch it, and its own head says why:* it is a memory, not a
    # judgement -- it finds what somebody wrote down as revoked. **That is exactly why the
    # entry stands here now and not in a report.**
    dict(kennung="WB2",
         muster=r"`fnptr`[^\n]{0,60}(?:null Korpusstellen|keinen Erzeuger)"
                r"|null Korpusstellen und keinen Erzeuger"
                r"|[Dd]ie Sprache kennt kein `&f`"
                r"|`fnptr`[^\n]{0,40}\bNICHT gebaut\b"
                r"|no corpus sites and no producer"
                r"|[Tt]he language (?:has|knows) no `&f`"
                r"|`fnptr`[^\n]{0,40}\bNOT built\b",
         datum="2026-08-21", grund="`messung/FNPTR.md`: Erzeuger `ExprArt::FnWert` "
                                   "(`M127`/`M128`), Ruf ueber einen Ort (`M129`), die "
                                   "Absenkung und der Vertrag am Typ (`N035`-`N037`); "
                                   "`beispiele/49-dispatch-tabelle.gab` mit 0 Fehlern",
         ersatz="`fnptr` ist in allen vier Haelften gebaut -- offen ist nur, wie zwei "
                "unabhaengige Rangskalen zueinander stehen (ABI2), nicht der Zeiger",
         probe=("Die Sprache kennt kein `&f`.",
                "The language has no `&f`.")),
    # **WB3, entered 2026-08-25 -- and the reason it exists is that `WB2` did NOT catch this
    # sentence.**
    #
    # `WB2` remembers the claim about the CONSTRUCT: *"the language has no `&f`"*, *"no corpus
    # sites and no producer"*. The sentence that was still standing one day later in
    # `PFLICHTEN.md`:175 is a DIFFERENT claim about the same item -- the one about the
    # CONTRACT: *"`fnptr` carries no `requires`, no `ensures`, no `effects`"*. It stood there
    # as an open gap and therefore carried one point of `H`.
    #
    # **Two claims about one item, and the memory held only the first.** That is exactly what
    # the head above means by *"a memory, not a judgement"* -- and exactly why one entry per
    # ITEM is not enough. *One per revoked SENTENCE.*
    #
    # Re-measured, and it reproduces:
    #
    #     $ printf 'type T = { f : fn(u8), };' > /tmp/b9.gab
    #     $ gabbro pruefe /tmp/b9.gab
    #     Fehler: [N035] /tmp/b9.gab:1:16: `fn(#1)` declares no `effects` and no `costs`
    #
    # **And the limit of this entry, so it does not promise more than it measures:** it looks
    # for the THREE-PART ENUMERATION, not for every way of saying the same thing. `PLAN.md`:951
    # (*"`fnptr` without a contract"*) and `MESSUNGEN.md`:6721 say it in other words; the first
    # was struck by hand on 2026-08-25, the second stands in a dated measurement table.
    # *A wording is a pattern, a claim is not.*
    dict(kennung="WB3",
         muster=r"(?:carries|tr[aä]e?gt) no `requires`, no `ensures`, no `effects`"
                r"|kein `requires`, kein `ensures`, kein `effects`"
                r"|no `requires`, no `ensures`, (?:and )?no `effects`",
         datum="2026-08-21", grund="`N035` macht `effects` UND `costs` am `fn(...)`-Typ zur "
                                   "Pflicht, `N036` traegt die Wirkungswoerter durch den "
                                   "indirekten Ruf, `N037` weist `requires`/`ensures` mit "
                                   "GEMESSENER Begruendung ab; `messung/FNPTR.md`",
         ersatz="der Vertrag steht am Zeigertyp und ist PFLICHT -- `effects` und `costs`; "
                "abgewiesen sind nur `requires`/`ensures`, und das begruendet `N037`",
         probe=("Er traegt kein `requires`, kein `ensures`, kein `effects`.",
                "It carries no `requires`, no `ensures`, no `effects`.")),
]

# Welche Dateien der Waechter liest. TODO.md und DONE.md stehen mit drin: ein widerrufener
# Satz ist dort genauso teuer, und `pruefe-todo.py` sieht diese Klasse nicht.
DATEIEN = (sorted(W.glob("dokumente/*.md"))
           + [W / "TODO.md", W / "DONE.md", W / "README.md"]
           # **Und die Beispiele.** Ihre Kommentare sind Prosa, die gelesen wird wie ein
           # Dokument -- `22-bootstrecke.gab` traegt fuenf Zeilen Befundtext ueber `ensures`.
           # *Ein widerrufener Satz ist dort genauso teuer und faellt sonst niemandem auf.*
           + sorted(W.glob("beispiele/*.gab"))
           # **And the REPORTS under `messung/`, since 2026-08-25.**
           #
           # They were outside the whole time, and that was the biggest gap in the reach: a
           # report is the kind of text that looks most like a result -- it carries numbers,
           # a date and a command to recompute it.
           #
           # *Measured while entering `WB2`: THREE live hits, all three about `fnptr`.*
           # `ERZEUGER.md`:15 and :266 booked as not built an item that was built **on the
           # same day** (`FNPTR.md`); `FNPTR.md`:14 quotes the sentence in a before/after
           # table and is therefore wrapped in the exempting marker pair now.
           #
           # > **A guardian that does not read the file the sentence stands in is no
           # > guardian against it** -- and the head above promises a memory, not a
           # > selection of files.
           + sorted(W.glob("messung/*.md"))
           + sorted(W.glob("messung/*/*.md")))

# **FROZEN, and therefore exempt -- entered 2026-08-25 while building `WB3`.**
#
# `dokumente/FRAGMENTE.md` is a report from 2026-08-14 and carries its freeze sentence;
# `messung/fragmente/README.md` says why, right beside it: *"an excerpt cannot be executed"*,
# and overwriting it would move the yardstick instead of discharging an obligation.
#
# **The reason for the exemption is not convenience, it is consistency:** `WB3` finds its
# three-part enumeration in TWO places -- in `PFLICHTEN.md` (live, and struck there now) and in
# `FRAGMENTE.md`:628, the source it was copied from. **The second cannot be struck without
# breaking the freeze sentence.** A guardian that only turns green by breaking another rule is
# no longer measuring.
#
# > *A frozen report is dated by its construction.* It does not say "this can never work", it
# > says "on 14.8. it did not" -- and that is precisely the distinction the head above stands
# > on. **The exemption is PRINTED**, so the file count does not promise more than it measures.
AUSGENOMMEN = [W / "dokumente" / "FRAGMENTE.md"]
DATEIEN = [d for d in DATEIEN if d not in AUSGENOMMEN]

AUS = re.compile(r"<!--\s*widerruf:aus\s*-->.*?<!--\s*widerruf:an\s*-->", re.S)


def absaetze(text):
    """(Zeilennummer, Absatztext) -- Absaetze sind durch Leerzeilen getrennt."""
    zeile, puffer, start = 1, [], 1
    for z in text.split("\n"):
        if z.strip() == "":
            if puffer:
                yield start, "\n".join(puffer)
            puffer, start = [], zeile + 1
        else:
            if not puffer:
                start = zeile
            puffer.append(z)
        zeile += 1
    if puffer:
        yield start, "\n".join(puffer)


def suche(text, muster):
    """Lebende Treffer: nicht in einem `widerruf:aus`-Block, nicht durchgestrichen."""
    # Der ausgenommene Block wird laengengleich ersetzt, damit die Zeilennummern stimmen.
    text = AUS.sub(lambda m: re.sub(r"[^\n]", " ", m.group(0)), text)
    treffer = []
    for zeile, absatz in absaetze(text):
        for m in re.finditer(muster, absatz):
            if "~~" in absatz:
                continue  # durchgestrichen -- der Ordner loescht nicht, er streicht durch
            versatz = absatz[:m.start()].count("\n")
            treffer.append((zeile + versatz, m.group(0)[:70].replace("\n", " ")))
    return treffer


def lauf(dateien, widerrufe):
    befunde = []
    for e in widerrufe:
        for d in dateien:
            if not d.exists():
                continue
            for zeile, text in suche(d.read_text(), e["muster"]):
                befunde.append((e["kennung"], d.relative_to(W), zeile, text))
    return befunde


def main():
    # **TOOTH 0 -- the subject has to be there** (2026-08-31). Over a tree without
    # `dokumente/` this tool died of a `FileNotFoundError` inside its own speech test:
    # return code 1, a traceback, and in a chain that reads like a live occurrence.
    # *A crash is not a refusal -- a NAMED refusal is.*
    probe = W / "dokumente" / "PLAN.md"
    if not DATEIEN or not probe.is_file():
        print("ABBRUCH: %d Dateien im Zugriff, Sprechprobendatei %s -- es wurde NICHTS "
              "gemessen." % (len(DATEIEN), "da" if probe.is_file() else "FEHLT"))
        print("   Ohne Text gibt es kein lebendes Vorkommen, und `ALL PASS` waere ein")
        print("   Urteil ueber nichts (W17).")
        return 2
    # ZAHN 1 -- kein Eintrag ohne alle fuenf Felder.
    for e in WIDERRUFE:
        for f in ("muster", "datum", "grund", "ersatz", "probe"):
            if not e.get(f):
                print("FEHLER: Eintrag %s ohne `%s`" % (e["kennung"], f))
                return 2
        # **And `probe` carries TWO sentences, German and English.** An entry that knows only
        # one language is a revocation that drops out silently the day its document moves --
        # and this guardian's green cannot tell that apart from a clean tree.
        if len(e["probe"]) != 2 or not all(e["probe"]):
            print("FEHLER: Eintrag %s hat keine ZWEI Probesaetze (deutsch UND englisch)"
                  % e["kennung"])
            return 2

    befunde = lauf(DATEIEN, WIDERRUFE)

    print("== Widerrufene Saetze: %d Eintraege, %d Dateien ==" % (len(WIDERRUFE), len(DATEIEN)))
    # **The exemption belongs beside the number, not in the source alone** (2026-08-25).
    # A reach that leaves a file out and says so only in a comment promises more than it
    # measures -- the same class as W7.
    for d in AUSGENOMMEN:
        print("   ausgenommen: %s -- eingefroren, ein Bericht mit Datum; siehe Kopf"
              % d.relative_to(W))
    for e in WIDERRUFE:
        eigene = [b for b in befunde if b[0] == e["kennung"]]
        marke = "%d LEBENDE" % len(eigene) if eigene else "zu"
        print("  %-5s %-10s %s" % (e["kennung"], marke, e["ersatz"]))
        for _, datei, zeile, text in eigene:
            print("        %s:%d  %s" % (datei, zeile, text))

    # ZAHN 2 (R14) -- der Waechter weist nach, dass er messen kann. Drei Richtungen:
    # der eingesetzte Satz musz fallen -- DEUTSCH UND ENGLISCH --, der durchgestrichene nicht.
    #
    # **Until 2026-09-01 this test exercised ONE entry in ONE language.** It inserted the
    # German floating-point sentence, saw `WF1` catch it, and called the guardian able to
    # measure. *That is a statement about `WF1` and about German*, and it was read as a
    # statement about the register.
    #
    # Now every entry is measured in both languages, over the SAME live text, so a pattern
    # that only knows German cannot pass. **The point is the counter-direction:** a
    # bilingual pattern that lost its German half would come through a test that only ever
    # spoke English -- the same hole, mirrored.
    probe = W / "dokumente" / "PLAN.md"
    # speech_test: begin
    roh = probe.read_text()
    grundzahl = {e["kennung"]: len(suche(roh, e["muster"])) for e in WIDERRUFE}
    stumm = []
    for e in WIDERRUFE:
        for sprache, satz in (("deutsch", e["probe"][0]), ("englisch", e["probe"][1])):
            gift = roh + "\n\n" + satz + "\n"
            if len(suche(gift, e["muster"])) <= grundzahl[e["kennung"]]:
                stumm.append("%s/%s" % (e["kennung"], sprache))
    sauber = roh + "\n\n~~Gleitkomma ist nicht im Kern~~ -- gefallen 2026-08-18.\n"
    haelt = len(suche(sauber, WIDERRUFE[0]["muster"])) == grundzahl[WIDERRUFE[0]["kennung"]]
    print("\n== Sprechprobe (R14) ==")
    if stumm:
        print("  eingesetzter Satz faellt:      NEIN -- %d von %d Proben bleiben stumm:"
              % (len(stumm), 2 * len(WIDERRUFE)))
        for x in stumm:
            print("        %s" % x)
    else:
        print("  eingesetzter Satz faellt:      ja, %d von %d Proben (je Eintrag deutsch "
              "UND englisch)" % (2 * len(WIDERRUFE), 2 * len(WIDERRUFE)))
    print("  durchgestrichener bleibt frei: %s" % ("ja" if haelt else "NEIN"))
    abschnitt.fertig()
    if stumm or not haelt:
        print("== WIDERRUF: der Waechter misst nicht ==")
        return 2

    # speech_test: end
    if befunde:
        print("\n== WIDERRUF: %d lebende Vorkommen ==" % len(befunde))
        print("   Durchstreichen mit Datum, nicht loeschen -- oder den Eintrag zuruecknehmen,")
        print("   wenn der Widerruf selbst falsch war.")
        return 1
    print("\n== WIDERRUF: ALL PASS -- kein widerrufener Satz steht lebend da ==")
    print("   Und was das NICHT heiszt: der Waechter kennt %d Widerrufe. Gegen einen Satz," % len(WIDERRUFE))
    print("   den niemand als ueberholt erkannt hat, hilft er nicht.")
    return 0


if __name__ == "__main__":
    sys.exit(abschnitt.fahre(main))
