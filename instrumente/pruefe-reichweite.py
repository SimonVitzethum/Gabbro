#!/usr/bin/env python3
"""**Die zweite Klasse von Null: ein Rumpf, den ein Pass nicht LIEST.**

`gabbro blindstellen` zaehlt Form mal Stellung ueber dem KORPUS und findet, was niemand
geschrieben hat. Es faengt damit ausdruecklich nicht, was jemand sehr wohl geschrieben hat
und *kein Pass liest* -- und genau das war Befund 2 vom 2026-08-20:

    Ein `check` ist der ORT, an dem eine falsifizierbare Aussage steht, und er war der
    einzige Rumpf, den kein Typpass gelesen hat.

M1 meldete ueber `beispiele/06` woertlich *„this file has no function body"*, waehrend im
`can_fail` drei Groessen verrechnet wurden, die nirgends erklaert waren. Der Paarungspass fiel
am selben Tag auf dieselbe Weise, und aus demselben Grund: **beide laufen ueber
`ItemArt::Funktion` und sonst nichts.**

## Was hier gemessen wird

Fuer jeden Pass: **welche Item-Arten mit einem RUMPF nennt sein Quelltext?** Ein Pass, der
eine Art nirgends nennt, kann sie nicht eigens behandeln -- und wo er auch keinen
Sammellaeufer benutzt, sieht er sie ueberhaupt nicht.

    Was 0 Mutationen hat, ist nicht gedeckt, sondern unbeschaedigbar.
    Was 0 Fundstellen hat, ist nicht geprueft, sondern unerreichbar.
    Was 0 Paesse liest, ist nicht in Ordnung, sondern UNGELESEN.

## Und was das NICHT sagt

**Eine besetzte Zelle heisst nur, dass der Quelltext den Namen nennt** -- nicht, dass er den
Rumpf betritt, und schon gar nicht, dass er ihn richtig behandelt. Die Messung ist eine
TEXTZAEHLUNG wie in `pruefe-konstrukte.py`, und sie ist eine **untere Schranke auf die
Blindheit**: was nicht dasteht, wird sicher nicht eigens behandelt; was dasteht, kann alles
Moegliche sein.

*Auch das ist eine Zahl mit ihrer Grenze daneben.*
"""
import pathlib
import re
import sys

WURZEL = pathlib.Path(__file__).resolve().parent.parent
CHECK = WURZEL / "crates" / "gabbro-check" / "src"

# Die Paesse in der Reihenfolge, in der `lib.rs::pruefe` sie faehrt.
#
# **AND THAT SENTENCE IS NOW TRUE BECAUSE THE LIST IS READ THERE** (2026-09-02). It used to
# be a hand-written transcription that said it mirrored `lib.rs::pruefe` while nothing
# compared the two. Measured on `a2cd217`: `pruefe` really calls fifteen passes and twelve
# names stood here -- **`bindung`, `gatter` and `kontexte` were missing.**
#
# The verdict below reports an item kind as READ BY NO PASS, and that quantifier ranged over
# a list rather than over the checker. Three passes could have named a kind and the table
# would still have called it unread. *A blind spot reported as a measurement of blind spots.*
#
# `pruefe-abstieg.py:mit_block()` already reads its list out of `lib.rs` for this reason
# (W7: the rule is READ, never written twice). This does the same thing to the other half.
def paesse_aus_lib():
    """The passes `lib.rs::pruefe` really runs, in call order, deduplicated."""
    s = (CHECK / "lib.rs").read_text(encoding="utf-8")
    m = re.search(r"pub fn pruefe\(.*?\n\}\n", s, re.S)
    if not m:
        print("ABBRUCH: `lib.rs::pruefe` nicht gefunden -- die Besetzung dieses Waechters",
              file=sys.stderr)
        print("         waere dann eine leere Liste, und jede Zelle darunter UNGELESEN.",
              file=sys.stderr)
        sys.exit(2)
    aus = []
    for n in re.findall(r"\b([a-z_0-9]+)::pass\(", m.group(0)):
        if n not in aus:
            aus.append(n)
    if not aus:
        print("ABBRUCH: `lib.rs::pruefe` nennt keinen einzigen `::pass(` -- es wurde NICHTS "
              "gemessen.", file=sys.stderr)
        sys.exit(2)
    return aus


PAESSE = paesse_aus_lib()

# **Item-Arten, die einen RUMPF tragen** -- also etwas, das gelesen werden MUSS.
# Was keinen Rumpf hat (`assume`, `use`, `lock`), steht hier nicht: dort gibt es nichts zu
# uebersehen.
RUEMPFE = {
    "Funktion":    "fn-Rumpf, Praedikat oder asm",
    "Check":       "der `can_fail`-Rumpf",
    "Tabelle":     "die Invarianten",
    "Format":      "die `where`-Klauseln",
    "Device":      "die `transition`-Vorbedingungen",
    "Gruppe":      "die Verbindungsinvariante",
    "Walk":        "die Invarianten ueber `mappings of`",
    "Boot":        "die Schritte",
    "State":       "die Uebergaenge",
    "Konst":       "der Anfangswert",
    "Statisch":    "der Anfangswert",
    "Accumulates": "der Typ und `per cpu`",
}


def quelle(pass_: str) -> str:
    p = CHECK / f"{pass_}.rs"
    return p.read_text(encoding="utf-8") if p.exists() else ""


def gelesen(text: str, art: str) -> bool:
    return re.search(rf"ItemArt::{art}\b", text) is not None


def haupt() -> int:
    print("== Reichweite: welcher Pass liest welchen RUMPF ==")
    print("-- Was 0 Paesse liest, ist nicht in Ordnung, sondern UNGELESEN.")
    print()
    arten = list(RUEMPFE)
    breite = max(len(p) for p in PAESSE)
    kopf = " " * (breite + 3)
    for a in arten:
        kopf += f"{a[:6]:>7}"
    print(kopf)
    tafel = {}
    for pa in PAESSE:
        t = quelle(pa)
        zeile = f"   {pa:{breite}}"
        for a in arten:
            ja = gelesen(t, a)
            tafel[(pa, a)] = ja
            zeile += f"{'  x' if ja else '  .':>7}"
        print(zeile)

    print()
    befunde = []
    for a in arten:
        leser = [p for p in PAESSE if tafel[(p, a)]]
        if not leser:
            befunde.append(f"   UNGELESEN  `{a}` ({RUEMPFE[a]}) -- KEIN Pass nennt es")
        elif len(leser) == 1:
            befunde.append(
                f"   DUENN      `{a}` ({RUEMPFE[a]}) -- nur `{leser[0]}`"
            )
    for b in befunde:
        print(b)
    print()
    ungelesen = sum(1 for b in befunde if "UNGELESEN" in b)
    duenn = sum(1 for b in befunde if "DUENN" in b)
    print(f"== {ungelesen} ungelesen, {duenn} von genau einem Pass gelesen ==")

    # **Die Sprechprobe: der Waechter muss den Fall von heute frueh nennen koennen.**
    #
    # Vor dem 2026-08-20 nannten weder `m1.rs` noch `paarung.rs` das Wort `ItemArt::Check`.
    # Ein Waechter, der das nicht faende, misst nichts -- also wird es hier geprueft, indem
    # der Text kuenstlich um die beiden Vorkommen gekuerzt wird.
    # speech_test: begin
    print("== Sprechprobe: findet der Waechter den Fall vom 2026-08-20? ==")
    ohne = {p: re.sub(r"ItemArt::Check", "ItemArt::XXX", quelle(p)) for p in ("m1", "paarung")}
    leser_ohne = [
        p for p in PAESSE if gelesen(ohne.get(p, quelle(p)), "Check")
    ]
    heute = [p for p in PAESSE if tafel[(p, "Check")]]
    if len(leser_ohne) < len(heute):
        print(f"   ok -- ohne die zwei Stellen faellt `Check` von {len(heute)} auf {len(leser_ohne)} Leser")
    else:
        print("   GESCHEITERT -- der Waechter merkt den Unterschied nicht")
        print("   Die Tafel darueber ist damit keine Messung. ABBRUCH.")
        # 2, not 1: the table printed above says nothing once the probe has fallen.
        return 2

    print()
    # speech_test: end
    print("== Und was das NICHT heisst ==")
    print("  Eine besetzte Zelle sagt nur, dass der QUELLTEXT den Namen nennt -- nicht, dass")
    print("  er den Rumpf betritt, und schon gar nicht, dass er ihn richtig behandelt. Die")
    print("  Messung ist eine Textzaehlung und damit eine UNTERE SCHRANKE auf die Blindheit:")
    print("  was nicht dasteht, wird sicher nicht eigens behandelt.")
    return 0


if __name__ == "__main__":
    sys.exit(haupt())
