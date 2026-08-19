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

WURZEL = pathlib.Path(__file__).parent
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


def messe():
    arten = mit_block()
    zeilen, offen = [], 0
    for p in PAESSE:
        d = QUELLE / f"{p}.rs"
        if not d.exists():
            continue
        ganz = d.read_text()
        if "StmtArt::" not in ganz:
            continue
        # **Ein Sammelzweig, der WEIGERT, ist keine Luecke.** Der Erzeuger nennt jede
        # Anweisungsart, die er nicht kann, beim Namen (`C001`) -- gemessen an
        # `beispiele/31-rcu.gab`: *no lowering: statement kind*. Das ist der Unterschied
        # zwischen einem Vorbehalt und einer stillen Zusage.
        weigert = "_ => weigere(" in ganz
        # **Je FUNKTION, nicht je Datei** -- die Dateiebene war zu grob: `m2::gehe` fehlte
        # `observes`, waehrend `m2::sammle_forever` es nannte, und die Datei galt als gedeckt.
        # *Dieselbe Vergroeberung, die der Waechter an den Paessen misst, hatte er selbst.*
        luecken = []
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
                    offen += 1
                    zeilen.append(f"  {p}::{name:<20} DOPPELTER ABSTIEG in: {arm}")
                continue
            # Nur Wege, die ueberhaupt absteigen wollen: wer keinen einzigen Unterblock
            # anfasst, ist ein Blattpruefer und keine Luecke.
            if not any(re.search(r"StmtArt::" + a + r"\b", rumpf) for a in arten):
                continue
            fehlt = [a for a in arten if not re.search(r"StmtArt::" + a + r"\b", rumpf)]
            if fehlt:
                luecken.append((name, fehlt))
        if not luecken:
            zeilen.append(f"  {p:<14} gedeckt")
        elif weigert:
            zeilen.append(f"  {p:<14} weigert sich benannt")
        else:
            offen += len(luecken)
            for name, fehlt in luecken:
                zeilen.append(f"  {p}::{name:<20} OHNE ABSTIEG in: {', '.join(fehlt)}")
    return arten, zeilen, offen


def main():
    arten, zeilen, offen = messe()
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
    print("  (Sprechprobe: fehlender UND doppelter Abstieg werden gemeldet -- ok)")
    if offen:
        print(f"== ABSTIEG: {offen} Paesse mit Luecke ==")
        return 1
    print("== ABSTIEG: ALL PASS -- jeder Pass erreicht jeden Unterblock ==")
    return 0


sys.exit(main())
