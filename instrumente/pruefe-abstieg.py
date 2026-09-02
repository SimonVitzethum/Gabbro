#!/usr/bin/env python3
"""**Steigt jeder Pass in jede Anweisung ab, die einen Unterblock traegt?**

Die Frage ist der Anweisungs-Zwilling von `pruefe-konstrukte.py`, Mass 2, und sie kommt
aus demselben Werkzeug: **Beruehrung ist keine Pruefung** (W13). Ein Pass, der `StmtArt`
ueberhaupt anfasst, sieht damit noch lange nicht jede Form -- er zaehlt seine Arme selbst
auf und schliesst mit `_ => {}`, und der Sammelzweig sieht aus wie ein Vorbehalt und ist
eine **stille Zusage**: *hier steht nichts, was mich angeht.*

Gemessen am 2026-08-19, ausgeloest von einer Rezension: ein Ruf in einem `observes`-Block
kam im Aufrufgraphen nicht an. Zwei `E008` verschwanden -- `masks IRQ` und `writes G`
standen im Gerufenen und in keiner Wirkungsliste. **Derselbe Ruf eine Zeile hoeher fiel.**

Der Ausweg steht in `lib.rs`: `unterbloecke(&Stmt) -> Vec<&Block>` matcht **ohne
`_`-Zweig**. Wer ihn nimmt, bekommt einen Uebersetzungsfehler, sobald `StmtArt` waechst --
statt eine Luecke zu erben.
"""
import re, pathlib, sys

# **Whoever leaves mid-run says WHERE** -- the shared form, out of `abschnitt.py`.
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import abschnitt  # noqa: E402

WURZEL = pathlib.Path(__file__).resolve().parent.parent
QUELLE = WURZEL / "crates/gabbro-check/src"


def absage(satz):
    """**ABBRUCH: es wurde NICHTS gemessen -- und der Ruecklaufwert sagt es** (2026-08-31).

    Bis heute stand hier ueberall `sys.exit("…")`, und das ist Ruecklaufwert **1** -- also
    genau die Farbe eines neuen Passes mit Luecke. Dieser Waechter kannte damit nur zwei
    Zustaende, wo es drei gibt: eine gefallene Sprechprobe und eine fehlende Liste in
    `lib.rs` lasen sich wie ein Rueckstand in den Paessen. *Ein Werkzeug, das nichts
    gemessen hat, darf nicht so aussehen wie eines, das etwas gefunden hat.*
    """
    print(f"ABBRUCH: {satz}", file=sys.stderr)
    print("  Es wurde NICHTS gemessen -- die Tafel darueber ist keine Aussage ueber die"
          " Paesse.", file=sys.stderr)
    sys.exit(2)

# Die Arten, die einen Unterblock tragen -- aus `lib.rs::unterbloecke`, und der Waechter
# liest sie DORT, statt sie zweitzuschreiben.
def mit_block():
    s = (QUELLE / "lib.rs").read_text()
    m = re.search(r"pub fn unterbloecke.*?\n}\n", s, re.S)
    if not m:
        absage("lib.rs::unterbloecke nicht gefunden -- der Waechter liest dort seine Liste")
    kopf = m.group(0).split("StmtArt::Let(_)")[0]
    return sorted(set(re.findall(r"StmtArt::([A-Za-z]+)", kopf)))

# Die Paesse, die ueber Anweisungen laufen. `emit` steht dabei: ein Erzeuger, der eine
# Anweisungsart nicht kennt, schreibt sie nicht -- und das ist der stillste Fehler von allen.
PAESSE = ["m1", "m2", "m3", "kosten", "wirkungen", "geteilt", "phasen", "paarung",
          "schleifen", "gruppe", "aufrufgraph", "zeugnis", "namen", "kbedingung", "emit"]

# **THE LIST ABOVE IS A FIXTURE, AND UNTIL TODAY NOTHING COMPARED IT TO THE TREE**
# (2026-09-02). It is hand-written; the closing line of this run says *jeder Pass erreicht
# jeden Unterblock*, and `jeder` is a claim about a population this file never counted.
#
# Measured: 19 files under `crates/gabbro-check/src` carry a `StmtArt::` arm for a
# block-bearing kind. Fifteen names stand above. **The claim covered part of what descends,
# and read as if it covered all of it.**
#
# What goes in here is a CENSUS and a booking, not a wider sweep: whether one of these is a
# pass over statements, or a register that happens to look at one, is a decision about the
# architecture, and this guardian does not get to make it by widening a list. What it does
# get to do is refuse to keep quiet -- the names print every run, and a name that is not
# booked here turns the run red, exactly as an unbooked descent gap does.
#
# *The reasons below say what each file IS. None of them says the file is excused.*
AUSSERHALB_GEBUCHT = {
    "lib": "the shared walker itself -- `unterbloecke` is READ from here, so it is the "
           "subject of the rule rather than a pass under it",
    "alias": "the alias surface, counted and deliberately not analysed (its own head line)",
    "blindstellen": "a register over forms the corpus does not reach",
    "domaene": "the domain bound, one site and two readers",
    "lean": "the body channel, a Gabbro body as a Lean term",
    "opsruf": "the call form of a generated operation",
    "pflichten": "the obligation register, P6",
    "zeremonie": "the ceremony register, stage 2",
}


def absteigende_dateien(arten):
    """Every file under the checker that carries an arm for a block-bearing kind.

    The population `PAESSE` claims to be. Derived from the tree and from `lib.rs`'s own
    list -- neither half is written twice (W7).
    """
    muster = re.compile(r"StmtArt::(?:%s)\b" % "|".join(re.escape(a) for a in arten))
    return sorted(p.stem for p in QUELLE.glob("*.rs") if muster.search(p.read_text()))


def funktionen(s):
    """Zerlegt eine Rust-Datei in Funktionen -- ueber Klammerzaehlung, nicht ueber Regex."""
    aus = []
    for m in re.finditer(r"\n(?:pub )?fn ([a-zA-Z_0-9]+)", s):
        name, i = m.group(1), m.end()
        j = s.find("{", i)
        if j < 0:
            continue
        t, k = 1, j + 1
        while k < len(s) and t:
            if s[k] == "{":
                t += 1
            elif s[k] == "}":
                t -= 1
            k += 1
        aus.append((name, s[j:k]))
    return aus


def klammerspanne(text, ab):
    """`text[ab:e]` bis zur SCHLIESSENDEN Klammer -- `ab` steht hinter der oeffnenden."""
    tiefe, j = 1, ab
    while j < len(text) and tiefe:
        if text[j] == "(":
            tiefe += 1
        elif text[j] == ")":
            tiefe -= 1
        j += 1
    return text[ab:j - 1], j


def wachen(rumpf):
    """Die Arten, die eine **negierte** `!matches!(&s.art, …)`-Wache ausdruecklich ausnimmt.

    **`rustfmt` bricht die Wache um, und bis zum 2026-09-01 las dieser Waechter sie
    ZEILENWEISE.** In `m2::gehe` steht sie vierzeilig --

        if !matches!(
            &s.art,
            StmtArt::Wenn(_) | StmtArt::Match(_) | StmtArt::Narrow(_) | StmtArt::LetSonst(_)
        ) {

    -- und `"!matches!(&s.art," in zeile` traf damit nichts. Die Wache galt als leer, die
    zwei von Hand behandelten Arme als ungeschuetzte Rekursion, und der Waechter meldete
    **`m2::gehe: 2 DOPPELTE ABSTIEGE`** ueber Code, in dem die Absicherung woertlich
    dasteht. *Ein Werkzeug, das Rust zeilenweise liest, misst den Zeilenumbruch.*

    Gelesen wird jetzt ueber die Klammerung, und **nur die negierte Form**: ein positives
    `matches!(&s.art, StmtArt::Schleife(_))` waehlt einen Fall AUS, es nimmt keinen aus.
    """
    aus = set()
    for m in re.finditer(r"!\s*matches!\s*\(", rumpf):
        arg, _ = klammerspanne(rumpf, m.end())
        if not re.match(r"\s*&s\.art\s*,", arg):
            continue
        aus |= set(re.findall(r"StmtArt::([A-Za-z]+)", arg))
    return aus


def ohne_wachen(rumpf):
    """Derselbe Rumpf, aber jedes `matches!( … )` ausgeleert.

    **Eine `matches!`-Frage ist keine Weiche.** Wer wissen will, ob eine Funktion ueberhaupt
    ABSTEIGT, darf ihre Praedikate nicht als Abstieg lesen -- sonst gilt `m2::endet` als
    Absteiger, weil es fuer den leeren `match` einen Sonderfall abfragt.
    """
    aus, i = [], 0
    for m in re.finditer(r"matches!\s*\(", rumpf):
        if m.start() < i:
            continue
        arg, ende = klammerspanne(rumpf, m.end())
        aus.append(rumpf[i:m.start()])
        i = ende
    aus.append(rumpf[i:])
    return "".join(aus)


def doppelt(name, rumpf, arten):
    """Arme, die neben `unterbloecke` noch **ungeschuetzt** selbst rekursieren.

    Zwei Feinheiten, und beide waren beim ersten Lauf falsch:

    * **Nur der Text VOR dem gemeinsamen Abstieg zaehlt.** Sonst laeuft der letzte Arm ueber
      das Ende des `match` hinaus und liest den Abstieg selbst als seine eigene Rekursion.
    * **Eine `!matches!`-Wache ist die Antwort, nicht der Fehler.** Wer `if` und `match`
      oben eigenstaendig behandelt (weil dort abgeglichen und nicht fortgeschrieben wird)
      und den gemeinsamen Abstieg dagegen absichert, laeuft nichts zweimal.
    """
    schnitt = rumpf.find("crate::unterbloecke(")
    kopf = rumpf[:schnitt] if schnitt > 0 else rumpf
    wache = wachen(rumpf)
    aus = []
    teile = re.split(r"(StmtArt::[A-Za-z]+)", kopf)
    for i in range(1, len(teile), 2):
        art = teile[i][len("StmtArt::"):]
        if art not in arten or art in wache:
            continue
        if re.search(r"\b" + re.escape(name) + r"\s*\(", teile[i + 1]):
            aus.append(art)
    return aus


def je_funktion(ganz, arten):
    """Zerlegt eine Quelle in (doppelte, luecken, entschuldigt) -- **je FUNKTION**.

    Die Dateiebene war zu grob: `m2::gehe` fehlte `observes`, waehrend `m2::sammle_forever`
    es nannte, und die Datei galt als gedeckt. *Dieselbe Vergroeberung, die der Waechter an
    den Paessen misst, hatte er selbst.*
    """
    doppelte, luecken, entschuldigt = [], [], []
    for name, rumpf in funktionen(ganz):
        if "StmtArt::" not in rumpf:
            continue
        # **Die Gegenrichtung, und sie hat sofort gebissen** (2026-08-19): wer den
        # gemeinsamen Absteiger nimmt UND daneben noch einen eigenen Arm stehen laesst,
        # laeuft jeden Unterblock ZWEIMAL -- und das ist 2^Tiefe.
        #
        # Gemessen an `m1::sammle_schreibziele`, wo genau das passiert war: 26
        # geschachtelte `if` brauchten **1,88 s**, danach **0,003 s**; bei 50 lief der
        # Pruefer laenger als anderthalb Minuten. *Ein Waechter, der nur eine Richtung
        # prueft, misst die Haelfte* -- und diese Haelfte hat er selbst durchgelassen.
        if "unterbloecke(" in rumpf:
            for arm in doppelt(name, rumpf, arten):
                doppelte.append((name, arm))
            continue
        # Nur Wege, die ueberhaupt absteigen wollen: wer keinen einzigen Unterblock
        # anfasst, ist ein Blattpruefer und keine Luecke.
        #
        # **And a `matches!` does NOT count as touching** (2026-09-01). `m2::endet` asks
        # `matches!(&s.art, StmtArt::Match(m) if m.zweige.is_empty())` for the empty `match`
        # and descends into no block at all -- it reads `b.anweisungen.last()` and hands the
        # question on to `crate::endet_immer`. This guard read the one mention as an intention
        # to descend and reported eight missing kinds.
        #
        # **What triggered it was the REPAIR of an earlier finding.** On 2026-08-30 `endet`
        # got an exhaustive `match` over every kind and this guard went green; on 2026-08-31
        # that very match was recognised as a FOURTH register of `Return|Leave|Next` and
        # folded into `crate::endet_immer` -- and with it went the list of kinds that had
        # satisfied this guard.
        #
        # > **A guard that recognises a descent by the kinds a function NAMES rewards the
        # > fourth copy and punishes the consolidation.** That is the opposite direction to
        # > `W7`, and it stood in the rule for two days.
        #
        # The coarsening is one-sided and therefore safe: `fehlt` below still reads the WHOLE
        # body, so a kind handled only through a `matches!` still counts as covered. *A
        # mention is enough to cover; only DESCENDING needs a switch.*
        if not any(re.search(r"StmtArt::" + a + r"\b", ohne_wachen(rumpf)) for a in arten):
            continue
        fehlt = [a for a in arten if not re.search(r"StmtArt::" + a + r"\b", rumpf)]
        if not fehlt:
            continue
        # **Ein Sammelzweig, der WEIGERT, ist keine Luecke** -- der Erzeuger nennt jede
        # Anweisungsart, die er nicht kann, beim Namen (`C001`).
        #
        # **Und diese Entschuldigung gilt seit dem 2026-08-21 je FUNKTION statt je DATEI.**
        # Bis dahin genuegte EIN `_ => weigere(` irgendwo in `emit.rs`, und damit war die
        # ganze Datei entschuldigt: `emit` stand als *„weigert sich benannt"* da, waehrend
        # drei Sammler darin ihre Unterbloecke nicht erreichten (`sammle_retry` sah kein
        # `if`, `verbundlokale` kein `observes`, `benutzte_namen` kein `breaking`).
        # *Genau die Vergroeberung, die dieser Waechter zwei Tage vorher an den Paessen
        # gemessen und bei sich selbst stehen gelassen hatte* -- dieselbe Klasse, eine Ebene
        # hoeher.
        if "_ => weigere(" in rumpf:
            entschuldigt.append((name, fehlt))
        else:
            luecken.append((name, fehlt))
    return doppelte, luecken, entschuldigt


# **The booked backlog -- and this guard had none until 2026-08-30.**
#
# From at least 2026-08-28 it ended with `rc=1` at every run, over a single entry that had
# stood for days: `m2::endet` without a descent in seven kinds. **A guard whose red exit is
# the normal state cannot tell a new finding from the old one.** It is then not a guard any
# more but a display -- and a collective run over 26 of them reads it as noise.
#
# The form is the one `pruefe-konstrukte.py` carries, the twin this file names in its own
# first paragraph: a table of what is booked, WITH A WRITTEN REASON per entry, and three
# answers instead of two.
#
#   * an entry that is NOT in the table   -> red. A new backlog.
#   * an entry in the table that is GONE  -> red. The table has aged; delete the line.
#   * only booked entries                 -> green, and the count is printed.
#
# > **The reason is half the booking.** An entry without one is a backlog that nobody has to
# > defend again -- and that is the shape this guard was built against, one level up.
#
# The table stands EMPTY today, and that is a measurement and not an oversight: the one
# entry it would have carried was a real defect, and it was repaired the same day
# (`messung/ABSTIEG.md`). *An empty booking is the only honest starting state -- what goes in
# has to be argued for.*
GEBUCHT = {}

# **A DOUBLE descent is never bookable.** It is not a gap in coverage but a run time of
# 2^depth -- measured at 1,88 s for 26 nested `if`, and longer than ninety seconds at 50.
# There is no state of the world in which that is a backlog somebody accepts, so it does not
# get a row in `GEBUCHT` and it does not get a green exit.


def einordne(luecken, tisch):
    """**Three answers over one list of gaps** -- and this is the whole of the decision.

    It stands alone so that the speaking test can run THIS function instead of a copy of it.
    *A guard whose probe re-implements the rule proves that the copy works.*
    """
    neu = [k for k in luecken if k not in tisch]
    gebucht = [k for k in luecken if k in tisch]
    veraltet = [k for k in tisch if k not in luecken]
    return neu, gebucht, veraltet


def messe():
    arten = mit_block()
    zeilen, alle_luecken, doppelte_gesamt = [], [], []
    for p in PAESSE:
        d = QUELLE / f"{p}.rs"
        if not d.exists():
            continue
        ganz = d.read_text()
        if "StmtArt::" not in ganz:
            continue
        doppelte, luecken, entschuldigt = je_funktion(ganz, arten)
        for name, arm in doppelte:
            doppelte_gesamt.append(f"{p}::{name}")
            zeilen.append(f"  {p}::{name:<20} DOPPELTER ABSTIEG in: {arm}")
        if not luecken and not entschuldigt and not doppelte:
            zeilen.append(f"  {p:<14} gedeckt")
        for name, fehlt in entschuldigt:
            zeilen.append(f"  {p}::{name:<20} weigert sich benannt ({len(fehlt)} Arten)")
        for name, fehlt in luecken:
            schluessel = f"{p}::{name}"
            alle_luecken.append(schluessel)
            marke = "GEBUCHT, ohne Abstieg" if schluessel in GEBUCHT else "OHNE ABSTIEG"
            zeilen.append(f"  {schluessel:<22} {marke} in: {', '.join(fehlt)}")
    neu, gebucht, veraltet = einordne(alle_luecken, GEBUCHT)
    return arten, zeilen, neu, gebucht, veraltet, doppelte_gesamt


def buchungs_sprechprobe(arten):
    """**Does the booking tell the three states apart?** (R14, 2026-08-30)

    The table is the risky half of this change. A booking that swallows everything is a green
    display, and that is the same failure as the red one it replaces -- only quieter. So the
    probe runs `einordne`, the function that actually decides, over synthetic input, once for
    each answer it owes.

    It also plants a real gap through `je_funktion`, so the two halves stay connected: a
    decision function that classified nothing would still pass a test made only of literals.
    """
    gift = """
fn sammler(b: &Block) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Wenn(w) => sammler(w),
            _ => {}
        }
    }
}"""
    _, luecken, _ = je_funktion(gift, arten)
    if not any(n == "sammler" for n, _ in luecken):
        return "die Probe erzeugt gar keine Luecke -- dann misst der Rest nichts"
    schluessel = ["probe::sammler"]

    neu, gebucht, veraltet = einordne(schluessel, {})
    if neu != schluessel or gebucht or veraltet:
        return "eine UNGEBUCHTE Luecke faellt nicht als neu auf"

    neu, gebucht, veraltet = einordne(schluessel, {"probe::sammler": "Grund"})
    if neu or gebucht != schluessel or veraltet:
        return "eine GEBUCHTE Luecke wird nicht als gebucht erkannt"

    neu, gebucht, veraltet = einordne([], {"probe::sammler": "Grund"})
    if neu or gebucht or veraltet != ["probe::sammler"]:
        return "eine Buchung OHNE Luecke faellt nicht als veraltet auf"
    return None


def main():
    # **TOOTH 0 -- THE SUBJECT HAS TO BE THERE** (2026-08-31). Over a tree without
    # `crates/` this tool died inside `mit_block()` of a `FileNotFoundError`: return code
    # **1**, a traceback, and in a chain that reads exactly like a pass with a gap. *A
    # crash is not a refusal -- a NAMED refusal is*, and a missing subject says the SETUP
    # has to change, not the tree.
    if not QUELLE.is_dir():
        absage(f"{QUELLE.relative_to(WURZEL)} fehlt -- der Gegenstand dieses Waechters "
               "ist nicht hier")
    fehlend = [d.name for d in (QUELLE / "lib.rs", QUELLE / "m1.rs") if not d.is_file()]
    if fehlend:
        absage("der Gegenstand fehlt: " + ", ".join(fehlend)
               + f" unter {QUELLE.relative_to(WURZEL)}")
    arten, zeilen, neu, gebucht, veraltet, doppelte_gesamt = messe()
    # **And an empty population is a refusal too** (W17): every readable pass appends at
    # least one line, so zero lines means no pass was read at all, and a clean verdict
    # over nothing is a positive verdict about nothing.
    if not arten or not zeilen:
        absage(f"{len(arten)} blocktragende Arten, {len(zeilen)} gemessene Paesse -- "
               "mindestens eine Menge ist LEER")
    print(f"== Abstieg: {len(arten)} blocktragende Anweisungsarten ==")
    print("   " + ", ".join(arten))
    for z in zeilen:
        print(z)
    # **R14: der Waechter beweist zuerst, dass er messen kann.** Nimmt man `Observiert` aus
    # einem Pass heraus, muss er es melden -- sonst misst er nichts.
    probe = (QUELLE / "m1.rs").read_text().replace("StmtArt::Observiert", "StmtArt::XX_weg")
    fehlt_jetzt = [a for a in arten if not re.search(r"StmtArt::" + a + r"\b", probe)]
    if "Observiert" not in fehlt_jetzt:
        absage("SPRECHPROBE GESCHEITERT: der Waechter sieht ein entferntes `Observiert` nicht")
    # **Und die zweite Richtung**, weil genau sie am 2026-08-19 durchgerutscht ist: ein Arm,
    # der neben `unterbloecke` noch selbst rekursiert, laeuft jeden Unterblock zweimal.
    gift = """fn probe(b: &Block) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Sperrt(x) => probe(&x.rumpf),
            _ => {}
        }
        for k in crate::unterbloecke(s) { probe(k); }
    }
}"""
    if "Sperrt" not in doppelt("probe", gift, arten):
        absage("SPRECHPROBE GESCHEITERT: der Waechter sieht einen doppelten Abstieg nicht")
    sauber = gift.replace("StmtArt::Sperrt(x) => probe(&x.rumpf),", "StmtArt::Sperrt(_) => {}")
    if doppelt("probe", sauber, arten):
        absage("SPRECHPROBE GESCHEITERT: falsches Rot am einfachen Abstieg")
    # **Und die dritte Richtung, seit dem 2026-08-21: die ENTSCHULDIGUNG darf nicht ueber
    # die Funktionsgrenze reichen.** Die Probe stellt genau die Lage her, die `emit.rs` bis
    # heute hatte: eine Funktion weigert sich benannt, die daneben hat eine Luecke.
    gift2 = """
fn weigerer(s: &Stmt) {
    match &s.art {
        StmtArt::Wenn(_) => {}
        StmtArt::Match(_) => {}
        _ => weigere(a, s.span, "no lowering"),
    }
}

fn sammler(b: &Block) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Wenn(w) => sammler(w),
            _ => {}
        }
    }
}"""
    _, l2, e2 = je_funktion(gift2, arten)
    if not any(n == "sammler" for n, _ in l2):
        absage("SPRECHPROBE GESCHEITERT: die Entschuldigung des Nachbarn deckt eine Luecke")
    if not any(n == "weigerer" for n, _ in e2):
        absage("SPRECHPROBE GESCHEITERT: eine benannte Weigerung wird nicht mehr entschuldigt")
    print("  (Sprechprobe: fehlender UND doppelter Abstieg werden gemeldet -- ok)")
    print("  (Sprechprobe: die Weigerung entschuldigt NUR ihre eigene Funktion -- ok)")
    # **And the fourth direction, since 2026-08-30: the BOOKING itself.**
    if fehler := buchungs_sprechprobe(arten):
        absage(f"SPRECHPROBE GESCHEITERT: {fehler}")
    print("  (Sprechprobe: neu, gebucht und veraltet werden unterschieden -- ok)")
    # **The fifth and sixth, since 2026-09-01: the two ways this guard READ Rust wrong.**
    # Both of them produced a red exit over code in which the right thing stood written, and
    # both counter-directions are here, because a rule that excuses everything is the same
    # failure as one that excuses nothing -- only quieter.
    umbrochen = """fn probe(b: &Block) {
    for s in &b.anweisungen {
        match &s.art {
            StmtArt::Wenn(w) => probe(w),
            _ => {}
        }
        if !matches!(
            &s.art,
            StmtArt::Wenn(_)
        ) {
            for k in crate::unterbloecke(s) { probe(k); }
        }
    }
}"""
    if doppelt("probe", umbrochen, arten):
        absage("SPRECHPROBE GESCHEITERT: eine UMBROCHENE `!matches!`-Wache wird nicht gelesen")
    if "Wenn" not in doppelt("probe", umbrochen.replace("StmtArt::Wenn(_)\n", "StmtArt::Sperrt(_)\n"),
                             arten):
        absage("SPRECHPROBE GESCHEITERT: eine Wache ueber der FALSCHEN Art entschuldigt trotzdem")
    praedikat = """
fn endet(b: &Block) -> bool {
    if let Some(s) = b.anweisungen.last() {
        if matches!(&s.art, StmtArt::Match(m) if m.zweige.is_empty()) {
            return false;
        }
    }
    crate::endet_immer(b)
}"""
    _, l3, _ = je_funktion(praedikat, arten)
    if any(n == "endet" for n, _ in l3):
        absage("SPRECHPROBE GESCHEITERT: ein `matches!`-Praedikat gilt weiter als Abstieg")
    dispatcher = praedikat.replace("if matches!(&s.art, StmtArt::Match(m) if m.zweige.is_empty()) {",
                                   "if let StmtArt::Match(m) = &s.art {")
    if not any(n == "endet" for n, _ in je_funktion(dispatcher, arten)[1]):
        absage("SPRECHPROBE GESCHEITERT: eine echte Weiche faellt nicht mehr als Luecke auf")
    print("  (Sprechprobe: eine umbrochene `!matches!`-Wache zaehlt, eine fremde nicht -- ok)")
    print("  (Sprechprobe: `matches!` ist eine Frage und keine Weiche -- ok)")

    # **A double descent is never booked.** It is not a hole in the coverage but a run
    # time of 2^depth.
    # **The census of what descends, beside the census of what was looked at.**
    draussen = [d for d in absteigende_dateien(arten) if d not in PAESSE]
    neu_draussen = [d for d in draussen if d not in AUSSERHALB_GEBUCHT]
    tote_buchung = [d for d in AUSSERHALB_GEBUCHT if d not in draussen]
    print(f"\n== Besetzung: {len(PAESSE)} Paesse angesehen, "
          f"{len(draussen)} weitere Dateien steigen ebenfalls ab ==")
    for d in draussen:
        print(f"   {d + '.rs':18s} {AUSSERHALB_GEBUCHT.get(d, '**NICHT GEBUCHT**')}")
    print("   Die Zeile darunter sagt `jeder Pass`, und das ist eine Aussage ueber die")
    print("   Liste oben -- nicht ueber diese hier. Sie stehen da, damit jemand sie")
    print("   verschieben KANN; sie freizusprechen ist etwas anderes (W10).")

    abschnitt.fertig()
    if neu_draussen:
        print(f"== ABSTIEG: {len(neu_draussen)} NEUE Datei(en) ausserhalb der Besetzung ==")
        print("   " + ", ".join(neu_draussen))
        print("   Sie steigen ueber Anweisungen ab und stehen weder in `PAESSE` noch in")
        print("   `AUSSERHALB_GEBUCHT`. Eines von beidem gehoert entschieden -- und die")
        print("   Entscheidung gehoert nicht diesem Waechter, das Aufschreiben schon.")
        return 1
    if tote_buchung:
        print(f"== ABSTIEG: {len(tote_buchung)} BUCHUNG(EN) OHNE GEGENSTAND ==")
        print("   " + ", ".join(tote_buchung))
        print("   Diese Dateien stehen in `AUSSERHALB_GEBUCHT` und steigen nicht mehr ab")
        print("   (oder heissen jetzt anders). *Eine Buchung, die niemand zurueckzieht,")
        print("   waechst zur Erlaubnis.*")
        return 1
    if doppelte_gesamt:
        print(f"== ABSTIEG: {len(doppelte_gesamt)} DOPPELTE ABSTIEGE ==")
        print("   " + ", ".join(doppelte_gesamt))
        print("   Das ist keine Deckungsluecke, sondern 2^Tiefe -- nichts davon ist buchbar.")
        return 1
    if neu:
        print(f"== ABSTIEG: {len(neu)} NEUE Paesse mit Luecke ==")
        print("   " + ", ".join(neu))
        print("   Wer sie buchen will, traegt sie MIT GRUND in `GEBUCHT` ein --")
        print("   ein Rueckstand ohne geschriebenen Grund ist einer, den niemand mehr")
        print("   verteidigen muss.")
        return 1
    if veraltet:
        print("== ABSTIEG: DIE BUCHUNG IST VERALTET ==")
        print("   Diese steigen jetzt ab. Eintrag loeschen: " + ", ".join(veraltet))
        print("   *Eine Buchung, die niemand zurueckzieht, waechst zur Erlaubnis.*")
        return 1
    if gebucht:
        print(f"== ABSTIEG: {len(gebucht)} gebucht, KEINE neue ==")
        print("   " + "\n   ".join(f"{k}: {GEBUCHT[k]}" for k in gebucht))
        print("   Und was das NICHT heisst: gebucht ist nicht geprueft. Der Waechter")
        print("   unterscheidet den alten Rueckstand vom neuen, er spricht ihn nicht frei (W10).")
        return 0
    print("== ABSTIEG: ALL PASS -- jeder Pass erreicht jeden Unterblock ==")
    return 0


sys.exit(abschnitt.fahre(main))
