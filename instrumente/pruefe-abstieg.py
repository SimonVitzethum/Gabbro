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

WURZEL = pathlib.Path(__file__).resolve().parent.parent
QUELLE = WURZEL / "crates/gabbro-check/src"

# Die Arten, die einen Unterblock tragen -- aus `lib.rs::unterbloecke`, und der Waechter
# liest sie DORT, statt sie zweitzuschreiben.
def mit_block():
    s = (QUELLE / "lib.rs").read_text()
    m = re.search(r"pub fn unterbloecke.*?\n}\n", s, re.S)
    if not m:
        sys.exit("lib.rs::unterbloecke nicht gefunden -- der Waechter liest dort seine Liste")
    kopf = m.group(0).split("StmtArt::Let(_)")[0]
    return sorted(set(re.findall(r"StmtArt::([A-Za-z]+)", kopf)))

# Die Paesse, die ueber Anweisungen laufen. `emit` steht dabei: ein Erzeuger, der eine
# Anweisungsart nicht kennt, schreibt sie nicht -- und das ist der stillste Fehler von allen.
PAESSE = ["m1", "m2", "m3", "kosten", "wirkungen", "geteilt", "phasen", "paarung",
          "schleifen", "gruppe", "aufrufgraph", "zeugnis", "namen", "kbedingung", "emit"]


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
    # Die Arten, die die Wache ausdruecklich ausnimmt.
    wache = set()
    for zeile in rumpf.split("\n"):
        if "!matches!(&s.art," in zeile:
            wache |= set(re.findall(r"StmtArt::([A-Za-z]+)", zeile))
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
        if not any(re.search(r"StmtArt::" + a + r"\b", rumpf) for a in arten):
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
    arten, zeilen, neu, gebucht, veraltet, doppelte_gesamt = messe()
    print(f"== Abstieg: {len(arten)} blocktragende Anweisungsarten ==")
    print("   " + ", ".join(arten))
    for z in zeilen:
        print(z)
    # **R14: der Waechter beweist zuerst, dass er messen kann.** Nimmt man `Observiert` aus
    # einem Pass heraus, muss er es melden -- sonst misst er nichts.
    probe = (QUELLE / "m1.rs").read_text().replace("StmtArt::Observiert", "StmtArt::XX_weg")
    fehlt_jetzt = [a for a in arten if not re.search(r"StmtArt::" + a + r"\b", probe)]
    if "Observiert" not in fehlt_jetzt:
        sys.exit("SPRECHPROBE GESCHEITERT: der Waechter sieht ein entferntes `Observiert` nicht")
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
        sys.exit("SPRECHPROBE GESCHEITERT: der Waechter sieht einen doppelten Abstieg nicht")
    sauber = gift.replace("StmtArt::Sperrt(x) => probe(&x.rumpf),", "StmtArt::Sperrt(_) => {}")
    if doppelt("probe", sauber, arten):
        sys.exit("SPRECHPROBE GESCHEITERT: falsches Rot am einfachen Abstieg")
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
        sys.exit("SPRECHPROBE GESCHEITERT: die Entschuldigung des Nachbarn deckt eine Luecke")
    if not any(n == "weigerer" for n, _ in e2):
        sys.exit("SPRECHPROBE GESCHEITERT: eine benannte Weigerung wird nicht mehr entschuldigt")
    print("  (Sprechprobe: fehlender UND doppelter Abstieg werden gemeldet -- ok)")
    print("  (Sprechprobe: die Weigerung entschuldigt NUR ihre eigene Funktion -- ok)")
    # **And the fourth direction, since 2026-08-30: the BOOKING itself.**
    if fehler := buchungs_sprechprobe(arten):
        sys.exit(f"SPRECHPROBE GESCHEITERT: {fehler}")
    print("  (Sprechprobe: neu, gebucht und veraltet werden unterschieden -- ok)")

    # **A double descent is never booked.** It is not a hole in the coverage but a run
    # time of 2^depth.
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


sys.exit(main())
