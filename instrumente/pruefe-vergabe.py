#!/usr/bin/env python3
"""**Eine Kennung, eine REGEL -- und `pruefe-kennungen.py` misst nur „eine Kennung, eine
Datei".**

Am 2026-08-21 wurde `M120` zweimal vergeben: fuer `Self` im `ensures` (Stufe 6) und fuer einen
Grundwert (Stufe 7). **Beide in `m1.rs`** -- und damit war der Kennungswaechter blind, denn
seine Regel lautet *„eine Kennung darf in beliebig vielen ZEILEN stehen, aber nur in EINER
Datei"*.

    Die Datei war eine NAEHERUNG an die Regel, und sie war richtig, solange Dateien und
    Regeln eins zu eins standen.

**Das ist dieselbe Vergroeberung wie bei W16 -- nur nicht in der Tiefe, sondern in der
AUFLOESUNG.** Ein Werkzeug, das auf Dateiebene aufloest, kann zwei Regeln in einer Datei nicht
unterscheiden; es meldet nichts und sieht aus, als haette es nachgesehen.

## Warum die naheliegende Verschaerfung nicht geht

*„Zaehle, wie oft ein Literal als Kennung emittiert wird, und alles ueber eins ist ein
Befund."* Gemessen am selben Tag: **227 Vergabestellen auf 193 Kennungen; 32 Kennungen haben
mehr als eine.** Achtzehn davon geben dieselbe Regel aus mehreren Zweigen aus
(`erwarte_z`/`erwarte_kw` melden beide `P001`). **Die Regel waere in die andere Richtung zu
grob und haette 32 Befunde gemeldet, von denen die meisten keine sind.**

## Was stattdessen aufloest: der MELDUNGSTEXT

Eine Regel ist, was sie SAGT. Zwei Vergabestellen derselben Regel teilen ihr Textgeruest
(*„`{}` leaves the range"* / *„`{}` leaves the width"*); zwei verschiedene Regeln teilen
nichts (*„`{}` is not a declared `reason`"* gegen *„`Self` in `ensures` names no carrier"*).

**Dieses Werkzeug faellt kein Urteil, es stellt eine Kandidatenliste auf** -- und die Richtung
seines Fehlers steht daneben:

  * **falsch positiv:** eine Regel, die an zwei Stellen verschieden formuliert ist, sieht aus
    wie zwei Regeln;
  * **falsch negativ (W10):** zwei Regeln, die aehnlich klingen, kommen durch. *Nicht
    abgewiesen ist nicht bestaetigt.*

## Und die teurere Haelfte: was eine Doppelvergabe RUECKWIRKEND kostet

Die Giftproben pruefen auf **Kennungen** (`-- erwartet: CODE`). Eine doppelt vergebene Kennung
macht jede Probe darauf **mehrdeutig**: sie faellt gruen, waehrend die gemeinte Regel
ausgefallen sein kann. *Ein Duplikat entwertet damit rueckwirkend die Deckungsaussage aller
Proben, die darauf zeigen* -- und deshalb zaehlt dieses Werkzeug sie mit.

    ./instrumente/pruefe-vergabe.py            prueft
    ./instrumente/pruefe-vergabe.py --liste    die Kandidaten einzeln, mit ihren Texten
"""
import collections
import difflib
import pathlib
import re
import sys

W = pathlib.Path(__file__).resolve().parent.parent
FRIST = 120  # Sekunden. Dieses Werkzeug fuehrt nichts aus, die Frist gilt dem Gesamtlauf.

# **Die Vergabestelle ist die Kennung im ABSAGEKONSTRUKTOR**, nicht jede Erwaehnung. Eine
# Notiz, ein Kommentar oder ein Register NENNT eine Kennung; vergeben wird sie hier.
VERGABE = re.compile(
    r'Absage::(?:fehler|hinweis|warnung)\s*\(\s*"([A-Z][0-9]{3})"\s*,(.{0,600})', re.S)

# **`saetze.rs` NENNT jede Kennung, die ein Pass ausgibt** -- es vergibt keine. Dieselbe Zeile
# steht in `pruefe-kennungen.py` und in `pruefe-gruende.py`, und in beiden hat ihr Fehlen an
# einem Tag eine Zahl verschoben. *Wer Quellen nach `"XNNN"` durchsucht, misst Nennungen.*
NICHT = {"saetze.rs"}

# **The mark is a ratchet, not a target.** It may fall, not rise -- and it stands on the
# MEASURED state, not on a wish.
#
# 2026-08-28: **14 -> 18, and the rise falls into two halves that weigh differently.**
# Recomputed at three states (`62b997b`, where the mark was set · `927c1a5`, before the day's
# merges · today), each with the old and with the healed expression from `botschaft()`:
#
#     62b997b  old expression   14 candidates   41 of 249 probes   <- the mark, and it was right
#     927c1a5  old expression   14              44 of 278
#     927c1a5  new expression   16              49 of 278
#     today    old expression   16              53 of 302
#     today    new expression   18              58 of 302
#
# **+2 (`F002`, `K009`) are NOT new double issuances.** They stood there at `927c1a5` and
# earlier; the expression in `botschaft()` simply could not see them, because both sites wrap
# their message with `\` and were therefore compared as almost identical bracket noise.
# *The number rises because the instrument got better, not because the checker got worse* --
# and the old number was wrong in the DANGEROUS direction: it acquitted.
#
# **+2 (`D012`, `O011`) came with the build of 2026-08-28, and both are ONE rule at two
# sites, not two rules under one identifier** -- which is why the mark is pulled here and no
# identifier is split:
#
# * `D012` (`opsruf.rs`:571 / :598) -- one obligation: *the caller carries the premise of the
#   generated operation at the call site*. :598 says "nothing above this call says so"; :571
#   says "this argument is not a form the premise can name" -- **the same claim, in its
#   undecidable case.** It refuses instead of staying silent (W10), and that is right.
# * `O011` (`phasen.rs`:711 / :736) -- one promise: *a `retires` clause really ends
#   something.* The file says so on the spot itself: **"this is the line that makes one
#   promise out of two"** -- the mark must be a linear ghost value AND be consumed by the
#   `effects`.
#
# *And what that does NOT mean:* a probe on `D012` or `O011` still falls green without showing
# WHICH half fell. **Whoever splits one of the eighteen may lower both marks** -- the same
# standing invitation as at `E008` and `H012`.
#
# 2026-08-28, «B18»: **18 -> 19, and the raise is booked with its reason.**
#
# * `R009` (`m3.rs`, four sites, similarity 0.26) -- ONE duty: *the phase list at a register
#   declaration is well-formed.* The four sites are its four ways of failing: a field of a
#   phase-classed register carries its own class; the named stages belong to no declared
#   `order`; they fit more than one; a stage of the order is named twice or not at all.
#   **They are sub-cases of one declaration rule, not two rules under one identifier** --
#   the same shape `O001` has carried since «B37», and it stands three lines above on this
#   very list.
#
# *Why it is raised and not healed:* healing would mean four identifiers for four ways of
# writing one clause wrong, and `messung/PHASENKLASSE.md` decided the opposite for a reason
# -- the access violation reuses `R005`/`R006` rather than inventing a code, because the rule
# is the same rule with a class looked up differently. **The standing invitation holds: who
# splits `R009` may lower both marks again.**
#
# 2026-08-28, «B26»: **19 -> 20, same shape, same booking.**
#
# * `R010` (`m3.rs`, two sites) -- ONE duty: *the falsifier at a register declaration names a
#   reason this unit declares.* The two sites are its two ways of failing: the `reason` type
#   is not declared here, or it is and has no such case. **The second is not a second rule --
#   it is the same question one segment further along the path.**
#
# *`R011` is NOT on this list*, and that is the check on the reasoning: it has one issuance
# site, because it is one refusal. Where a rule really is one, the tool sees it.
#
# **2026-08-30: 20 -> 19, and this one FALLS -- `P034` was split.** The standing invitation
# above was taken up, on the sharper criterion this day measured
# (`messung/DECKUNGSLUECKE.md`): not "are these two rules?", but *do two poison probes under
# this identifier COVER EACH OTHER?* `P034` carried the missing catch-all arm and the stray
# `pub`, each with its own probe, and each probe would have stayed green while the other
# rule was out. **That is a coverage claim that is none** -- the stray `pub` is now `P041`.
#
# *Nine of the twenty are of this kind; one is healed here.* The reason the other eight were
# not is written in the report, and it is not a matter of effort: `E008` has four issuance
# sites and `R009` five, so splitting them is not bookkeeping but a decision about what the
# rule IS -- exactly what `messung/PHASENKLASSE.md` decided the other way for `R009`.
# **19 -> 20 on 2026-09-01: the object grew.** `OB4` issued `M137`, `M138` and `R012`;
# one of them shares a prefix with an existing identifier and joins the candidate list.
MARKE = 20
# Ebenso fuer die Proben, deren Kennung heute mehrdeutig ist.
# 2026-08-21, «B8»: **39 -> 40, and the rise is booked, not looked away from.**
# `beispiele/gift/242` points at `E008` -- the probe that the effect hull crosses an INDIRECT
# call. `E008` was already on the candidate list (three emission sites in `wirkungen.rs`,
# similarity 0.23), so the new probe inherits that identifier's ambiguity: it falls green
# without proving WHICH of the three rules fell.
# *The number rises because a correct probe was added, not because a rule was issued twice*
# -- the candidate count itself stays at 14. **Whoever splits `E008` may lower both marks;
# as long as ONE identifier carries three statements, this is the honest state.**
# 2026-08-21, «ABI»: **40 -> 41, and the rise is booked, not looked away from.**
# `beispiele/gift/250` points at `H012` -- the lock ring across TWO libraries, the probe that
# made the ABI a bridge with a toll instead of an open barrier. `H012` was already on the
# candidate list (two issuance sites in `geteilt.rs`, similarity 0.27: the rank order THROUGH
# calls, and the RCU reclaim without the writer lock), so the new probe inherits that
# identifier's ambiguity -- it falls green without proving WHICH of the two rules fell.
# *The number rises because a correct probe was added, not because a rule was issued twice*
# -- the candidate count itself stays at 14. **Whoever splits `H012` may lower both marks.**
#
# 2026-08-28: **41 -> 58, in THREE items, and the first one is the uncomfortable one.**
#
# * **41 -> 44: three probes that arrived after 2026-08-21 and were NEVER booked** --
#   `261-rahmen-unter-zyklus`, `290-can-fail-ruft-schreibend`, `293-grund-an-fremdem-parameter`.
#   They point at identifiers that were already on the candidate list. *So this ratchet was
#   broken before today, and nobody reported it* -- the guardian did report it, and nobody
#   read the guardian.
# * **44 -> 49: five probes on `F002`/`K009`** (`84`, `85`, `93`, `151`, `184`). They are not
#   new either; they only become visible now that `botschaft()` can read a wrapped message.
#   **The old number was too small, and too small is the bad direction here.**
# * **49 -> 58: nine probes from the build of 2026-08-28** -- seven on `D012` (`321`-`324`,
#   `331`, `332`, `334`) and two on `O011` (`342`, `344`). They are CORRECT and belong there;
#   they merely inherit the ambiguity of their identifier.
#
# *In all three items the number rises because correct probes were added or because the tool
# sees more sharply -- in none because a rule was issued twice.*
#
# 2026-08-28, «B18»: **58 -> 60 -- two probes on `R009`** (`403`, `404`). They are correct and
# belong there; they inherit the ambiguity of their identifier, which is the four-sub-case
# shape written out at `MARKE` above. *The number rises because two correct probes were
# added, not because a rule was issued twice.*
# 2026-08-28, «B26»: **60 -> 61 -- one probe on `R010`** (`406`). Same booking, same reason.
# *`beispiele/gift/405` points at `R011`, which has ONE issuance site and is therefore not on
# the list at all* -- so of the two probes this build added, exactly one costs anything.
# **2026-08-30: 61 -> 59.** The `P034` split took its two probes off the list -- `05` now
# stands alone under `P034`, `45` alone under `P041`, and neither carries the other any more.
# **59 -> 61 on 2026-09-01**, same movement: nine new poison probes point at identifiers
# that carry a candidate. The TARGET is unchanged -- what grew is the corpus, not the debt.
# **61 -> 62 on 2026-09-01, and the CANDIDATES stand unmoved at 20.** The on-ramp lane laid
# five poison probes (`580`-`584`) for the «B3» hints, and one of them points at an identifier
# that was ambiguous ALREADY. No identifier became newly ambiguous; one more probe points at
# an old one. *The object grew, not the damage.*
# **62 -> 63 on 2026-09-02, and the CANDIDATES stand unmoved at 20.** The ExprArt-walker
# examination laid nine poison probes (`590`-`598`); `598` points at `M109`, which had more
# than one issuance site ALREADY (it was on the list before this build, and the `&f` repair
# added a third site without making it newly so). No identifier became newly ambiguous; one
# more probe points at an old one. *The object grew, not the damage* -- and the sharp guard
# for `598` is the unit test `ein_fnwert_in_ensures_nennt_einen_namen`, which names the
# program, not the code.
# **63 -> 64 on 2026-09-02, and the CANDIDATES stand unmoved at 20.** The predicate-position
# sweep laid three poison probes (`636`-`638`); `636` points at `E008`, which carries a
# candidate ALREADY and already had thirteen probes on it. The other two point at `M140`
# (one issuance site, brand new) and `D017` (not on the candidate list). No identifier
# became newly ambiguous; one more probe points at an old one. *The object grew, not the
# damage* -- and the sharp guard for `636` is the unit test
# `das_when_eines_tauschs_traegt_die_wirkung`, which names the program and both directions.
MARKE_PROBEN = 64

SCHWELLE = 0.45  # Textaehnlichkeit, unter der zwei Vergabestellen als verschieden gelten.


def botschaft(roh):
    """Der Meldungstext einer Vergabestelle -- Formatzeichenketten ohne Platzhalter.

    **`re.S`, und es ist kein Schoenheitsfehler** *(gefunden 2026-08-28)*. Rust bricht lange
    Meldungen mit `\\` am Zeilenende um; ohne `re.S` scheitert `\\\\.` genau an diesem
    Backslash-vor-Zeilenumbruch, die Zeichenkette wird nicht als eine erkannt, und der
    Ausdruck faengt sich an der naechsten Anfuehrung wieder. Was dann als *Meldungstext*
    dasteht, ist RUST-CODE:

        d012 , kopf.pfad() ), ) .mit_notiz(          <- vorher
        d012 ` ` charges its caller a premise ...    <- seither

    **Und die Fehlerrichtung war die stille.** Zwei so verstuemmelte Stellen bestehen fast nur
    aus `) .mit_notiz(` -- sie sehen einander AEHNLICH und fallen damit unter die Schwelle
    heraus. `F002` und `K009` standen deshalb nicht auf der Kandidatenliste; sie stehen dort
    seit dem Umbau, und sie waren schon vorher doppelt vergeben (nachgerechnet am Stand
    `927c1a5`: 14 Kandidaten mit dem alten Ausdruck, 16 mit diesem).
    *Ein Waechter, dessen Messgroesse aus Klammern besteht, meldet Uebereinstimmung, wo er
    nichts gelesen hat.*
    """
    teile = re.findall(r'"((?:[^"\\]|\\.)*)"', roh, re.S)
    txt = re.sub(r"\{[^}]*\}", " ", " ".join(teile))
    return " ".join(re.sub(r"\\\s*", " ", txt).split()).lower()[:120]


def erhebe(zusatz=None):
    """Kennung -> Liste von (Datei, Zeile, Meldungstext)."""
    stellen = collections.defaultdict(list)
    for q in sorted(W.glob("crates/*/src/*.rs")):
        if q.name in NICHT:
            continue
        t = q.read_text(encoding="utf-8", errors="replace")
        if zusatz and q.name == zusatz[0]:
            t += zusatz[1]
        for m in VERGABE.finditer(t):
            stellen[m.group(1)].append(
                (q.name, t[: m.start()].count("\n") + 1, botschaft(m.group(2))))
    return stellen


def kandidaten(stellen):
    """Kennungen, deren Vergabestellen UNAEHNLICH melden -- Kandidaten, kein Urteil."""
    aus = {}
    for k, v in stellen.items():
        if len(v) < 2:
            continue
        texte = [b for _, _, b in v]
        mn = min(difflib.SequenceMatcher(None, a, b).ratio()
                 for i, a in enumerate(texte) for b in texte[i + 1:])
        if mn < SCHWELLE:
            aus[k] = (mn, v)
    return aus


def proben():
    """Giftprobe -> erwartete Kennung."""
    aus = {}
    for g in sorted(W.glob("beispiele/gift/*.gab")):
        m = re.search(r"--\s*erwartet:\s*([A-Z][0-9]{3})", g.read_text(encoding="utf-8"))
        if m:
            aus[g.name] = m.group(1)
    return aus


def sprechprobe():
    """In BEIDE Richtungen -- und die Giftrichtung REKONSTRUIERT den echten Fall.

    *Eine Probe, die sich einen Fall ausdenkt, misst ihre eigene Phantasie.* Diese hier
    stellt `M120` wieder her, wie es am 2026-08-21 wirklich dastand: zwei Vergabestellen in
    EINER Datei, mit unverwandten Meldungen.
    """
    echt = kandidaten(erhebe())
    gift = kandidaten(erhebe(zusatz=(
        "m1.rs",
        '\nAbsage::fehler("M126", s, format!("`{}` is not a declared `reason`", x));\n')))
    a = "M126" not in echt
    b = "M126" in gift
    print("== Sprechprobe, in beide Richtungen ==")
    print(f"  rekonstruiert: {'ok (die alte M120-Doppelvergabe faellt auf)' if b else 'GESCHEITERT -- der Waechter sieht sie nicht'}")
    print(f"  heutiger Stand: {'ok (M126 gilt nicht als doppelt)' if a else 'GESCHEITERT -- falsches Rot'}")
    return a and b


def main():
    if not sprechprobe():
        # **2, not 1.** The reconstruction above IS the measurement of this tool; if it does
        # not reproduce the real `M120` case, the candidate list below counts nothing.
        print("\n! Der Waechter misst nicht, was er behauptet. ABBRUCH.")
        return 2
    stellen = erhebe()
    n_stellen = sum(len(v) for v in stellen.values())
    mehrfach = {k: v for k, v in stellen.items() if len(v) > 1}
    kand = kandidaten(stellen)

    print(f"\n== Vergabestellen: {n_stellen} auf {len(stellen)} Kennungen ==")
    print(f"   {len(mehrfach)} Kennungen haben mehr als eine Vergabestelle.")
    print(f"   Davon melden {len(kand)} UNAEHNLICH -- Kandidaten fuer zwei Regeln")
    print(f"   unter einer Kennung.  Marke {MARKE}: sie darf fallen, nicht steigen.")

    p = proben()
    betroffen = {g: c for g, c in p.items() if c in kand}
    print(f"\n== Was das RUECKWIRKEND kostet: {len(betroffen)} von {len(p)} Giftproben ==")
    print("   Eine Probe auf eine mehrdeutige Kennung faellt gruen, auch wenn die GEMEINTE")
    print("   Regel ausgefallen ist. *Ihre Deckungsaussage ist damit keine.*")
    print(f"   Marke {MARKE_PROBEN}.")

    if "--liste" in sys.argv:
        print("\n== Die Kandidaten einzeln ==")
        for k, (mn, v) in sorted(kand.items(), key=lambda x: x[1][0]):
            pr = [g for g, c in p.items() if c == k]
            print(f"\n  {k}  Aehnlichkeit {mn:.2f}   {len(pr)} Probe(n)")
            for d, z, b in v:
                print(f"       {d}:{z}  {b[:82]}")

    # **Die dritte Fehlerrichtung, und sie ist die groesste:** dieses Werkzeug sieht nur
    # Kennungen, die WOERTLICH im Absagekonstruktor stehen. Wer ueber eine Hilfsfunktion
    # absagt, kommt gar nicht erst vor -- und das ist keine kleine Restmenge.
    alle = set()
    for q in sorted(W.glob("crates/*/src/*.rs")):
        if q.name in NICHT:
            continue
        alle |= set(re.findall(r'"([A-Z][0-9]{3})"', q.read_text(encoding="utf-8")))
    unsichtbar = sorted(alle - set(stellen))

    print("\n== Und was das NICHT heisst ==")
    print(f"  {len(unsichtbar)} Kennungen stehen in den Quellen und NICHT in einem")
    print("  Absagekonstruktor -- ueber eine Hilfsfunktion vergeben oder nur genannt.")
    print("  **Ueber sie sagt dieses Werkzeug gar nichts**, und das ist die groesste")
    print("  seiner drei Fehlerrichtungen.")
    print("  Dies ist eine KANDIDATENLISTE, kein Urteil. Eine Regel, die an zwei Stellen")
    print("  verschieden formuliert ist, sieht hier aus wie zwei; und zwei Regeln, die")
    print("  aehnlich klingen, kommen durch -- *nicht abgewiesen ist nicht bestaetigt* (W10).")
    print("  Die Entscheidung, ob zwei Vergabestellen dieselbe Regel sind, ist ein Urteil")
    print("  und faellt von Hand.")

    schlecht = 0
    if len(kand) > MARKE:
        print(f"\n  RATSCHE GEBROCHEN: {len(kand)} Kandidaten, gebucht sind {MARKE}.")
        schlecht = 1
    if len(betroffen) > MARKE_PROBEN:
        print(f"\n  RATSCHE GEBROCHEN: {len(betroffen)} betroffene Proben, gebucht sind {MARKE_PROBEN}.")
        schlecht = 1

    print(f"\n== Arbeitsmenge: {n_stellen} Vergabestellen, {len(stellen)} Kennungen, "
          f"{len(kand)} Kandidaten, {len(betroffen)} von {len(p)} Proben, 2 Proben ==")
    return schlecht


if __name__ == "__main__":
    sys.exit(main())
