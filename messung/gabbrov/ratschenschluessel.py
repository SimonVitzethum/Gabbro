#!/usr/bin/env python3
"""**What may §15's ratchet be keyed on? -- measured, not argued.**

`SPRACHE.md` §15 says *"The ratchet runs over names; exchange is visible."* The second
half does not follow from the first. `OFFEN.md` `O3` measured the counter-example: swap
two `ensures` conjuncts and the manifest's **name, class, anchor and state** are all
unchanged, and only the text column moves. A ratchet over names would carry `closed`
from the old obligation to the new one without a word.

This tool exists because the decision underneath -- *which fields make up the key* --
must not be taken from a sentence. It measures four things:

    REACH     how many obligation lines can lose their identity at all, and how
    KEY       whether (name, class, text) actually identifies a line inside its unit
    PRICE     which edits move that key and which leave it alone
    ANCHOR    what the anchor field is worth as part of a key

*It is a MEASUREMENT beside a report, not a guardian.* It lives here and not in
`instrumente/` on purpose: a new `pruefe-*` moves three shared figures at once (the
README's `59 of 59`, the acceptance station count, and the guardian register), and this
lane was told to move none of them. Promoting it is a `git mv` whose price is those
three numbers, and that price belongs to whoever decides to pay it.

    ./messung/gabbrov/ratschenschluessel.py                the four measurements
    ./messung/gabbrov/ratschenschluessel.py --sprechprobe   the probes only

Return codes follow the sixth requirement, as `zaehle-p6.py` states it: **`1` means the
TREE has to change, `2` means the SETUP does.** A key collision in the corpus, or a probe
whose answer contradicts the decision, is a `1`; a missing binary or an empty corpus is a
`2`, and every one of those says NOTHING WAS MEASURED.
"""
import pathlib
import re
import subprocess
import sys
import tempfile

W = pathlib.Path(__file__).resolve().parent.parent.parent
GABBRO = W / "target" / "debug" / "gabbro"
FRIST = 60  # seconds per unit; a hang is not a finding.

# The poison probes are not part of the population: they exist to be refused, and a unit
# that carries a checker error carries no register at all.
AUSGESCHLOSSEN = ("target", ".git", ".claude", "beispiele/gift")

ZEILE = re.compile(r"^obligation\t")
ORDINAL = re.compile(r"#(\d+)$")


class Aufbaufehler(Exception):
    """The setup, not the tree. Nothing may be counted after one of these."""


def register(pfad):
    """The obligation lines of one unit as `(name, class, anchor, state, text)`.

    `None` where the unit carries checker errors -- that is not an empty register, it is
    the absence of one, and the two must not be added up.
    """
    try:
        run = subprocess.run(
            [str(GABBRO), "pflichten", str(pfad)], cwd=W,
            capture_output=True, text=True, timeout=FRIST,
        )
    except subprocess.TimeoutExpired:
        raise Aufbaufehler(f"{pfad}: deadline of {FRIST} s exceeded; a hang is not a finding")
    if run.returncode != 0:
        return None
    aus = []
    for z in run.stdout.splitlines():
        if ZEILE.match(z):
            f = z.split("\t")[1:]
            f += ["--"] * (5 - len(f))
            aus.append(tuple(f[:5]))
    return aus


def korpus():
    return sorted(
        p for p in W.rglob("*.gab")
        if not any(str(p.relative_to(W)).startswith(a) for a in AUSGESCHLOSSEN)
    )


def familie(name):
    """`aushaengen :: ensures #2` -> `aushaengen :: ensures #`, its SIBLING group."""
    return ORDINAL.sub("#", name)


# --------------------------------------------------------------------------------------
# The four measurements
# --------------------------------------------------------------------------------------

def reichweite(lagen):
    """How many lines can lose their identity, and by which of the three edits."""
    zeilen = [(d, *z) for d, zs in lagen for z in zs]
    mit_zahl = [z for z in zeilen if ORDINAL.search(z[1])]
    gruppe = {}
    for z in mit_zahl:
        gruppe.setdefault((z[0], familie(z[1])), []).append(z)
    vertauschbar = [z for z in mit_zahl if len(gruppe[(z[0], familie(z[1]))]) > 1]
    n = len(zeilen)
    print("== REACH -- what can lose its identity, and how ==")
    print(f"  obligation lines in the population                    {n:>4}")
    print(f"  a SWAP of two siblings can move it                    {len(vertauschbar):>4}"
          f"   ({sum(1 for v in gruppe.values() if len(v) > 1)} sibling groups"
          f" over {len({k[0] for k, v in gruppe.items() if len(v) > 1})} files)")
    print(f"  an INSERTION among the siblings can move it           {len(mit_zahl):>4}"
          "   -- every line whose name carries a number, the lone `#1`s included")
    print(f"  an EDIT of the text under an unchanged name can       {n:>4}"
          "   -- the NAMED kinds too: a `spec fn` body is edited, `maintains I` is not")
    print("  **Three severities, and they must not be reported as one number.** The first")
    print("  needs a sibling; the second needs only a neighbour written later; the third")
    print("  needs nothing at all.")
    return zeilen, vertauschbar, gruppe


def schluessel(lagen):
    """Is (name, class, text) a key inside its unit? -- the property option (b) needs."""
    print()
    print("== KEY -- does (name, class, text) identify a line inside its unit? ==")
    stoss = {}
    leer = 0
    n = 0
    for d, zs in lagen:
        for name, klasse, _anker, _zustand, text in zs:
            n += 1
            if text == "--":
                leer += 1
            stoss.setdefault((d, name, klasse, text), []).append(_anker)
    doppelt = {k: v for k, v in stoss.items() if len(v) > 1}
    print(f"  lines examined                                        {n:>4}")
    print(f"  lines with NO text (the key would fall back to the name)  {leer:>4}")
    print(f"  triples that occur more than once inside one unit     {len(doppelt):>4}")
    for (d, name, klasse, text), anker in sorted(doppelt.items()):
        print(f"     {d}  {name}  {klasse}  {text!r}  at {', '.join(anker)}")
    if not doppelt and not leer:
        print("  **The triple is a key over every unit of the population.** Where it stops")
        print("  being one -- two calls to one callee with one precondition -- the only")
        print("  field left is the anchor, and the ANCHOR measurement below prices that.")
    return len(doppelt), leer


def preis(tmp):
    """PRICE -- which edits move the key, and which leave it alone.

    Each case is an edit a person plausibly makes. `erwartet` says what the DECISION
    predicts; a case that comes out the other way is a finding, not a surprise.
    """
    quelle = W / "beispiele" / "01-tabelle.gab"
    if not quelle.exists():
        raise Aufbaufehler(f"{quelle} is missing; the price cannot be measured")
    roh = quelle.read_text(encoding="utf-8")
    alt = ("ensures   c.slots[s].elter == None,\n"
           "              c.slots[s].vorheriges == None,\n"
           "              c.slots[s].naechstes == None")
    if alt not in roh:
        raise Aufbaufehler(
            "the clause this probe cuts at has moved in `beispiele/01-tabelle.gab`; "
            "NOTHING was measured -- a probe against a text that is not there is not one"
        )

    faelle = [
        ("the swap `O3` describes -- conjunct 1 against conjunct 3", "MOVES",
         alt, "ensures   c.slots[s].naechstes == None,\n"
              "              c.slots[s].vorheriges == None,\n"
              "              c.slots[s].elter == None"),
        ("re-indent, one conjunct per line, deeper", "STAYS",
         alt, "ensures\n        c.slots[s].elter == None,\n"
              "        c.slots[s].vorheriges == None,\n"
              "        c.slots[s].naechstes == None"),
        ("wrap ONE conjunct across two lines", "STAYS",
         alt, "ensures   c.slots[s].elter\n                  == None,\n"
              "              c.slots[s].vorheriges == None,\n"
              "              c.slots[s].naechstes == None"),
        ("a comment beside the first conjunct", "STAYS",
         alt, "ensures   c.slots[s].elter == None,      -- the parent link\n"
              "              c.slots[s].vorheriges == None,\n"
              "              c.slots[s].naechstes == None"),
        ("redundant parentheses around one conjunct", "MOVES",
         alt, "ensures   (c.slots[s].elter == None),\n"
              "              c.slots[s].vorheriges == None,\n"
              "              c.slots[s].naechstes == None"),
    ]

    print()
    print("== PRICE -- which edits move the key (name, class, text)? ==")
    basis = {(z[0], z[1], z[4]) for z in register(quelle)}
    schlecht = 0
    for titel, will, a, b in faelle:
        ziel = tmp / "preis.gab"
        ziel.write_text(roh.replace(a, b), encoding="utf-8")
        jetzt = register(ziel)
        if jetzt is None:
            print(f"  ABORT: the edited unit no longer checks -- {titel}")
            raise Aufbaufehler("an edit made the probe unit unusable; NOTHING was measured")
        beweg = len(basis - {(z[0], z[1], z[4]) for z in jetzt})
        ist = "MOVES" if beweg else "STAYS"
        marke = "ok  " if ist == will else "!!  "
        if ist != will:
            schlecht += 1
        print(f"  {marke}{ist:<6} ({beweg:>2} of {len(basis)} keys)  {titel}")
    print("  **Layout is free and the predicate is not.** `zeremonie::schnitt_bis` collapses")
    print("  every whitespace run to one space, so indentation, wrapping and a trailing")
    print("  comment leave the key alone; parentheses and any rewording move it -- and a")
    print("  moved key loses `closed`, which is the SAFE direction (W10: it may oblige, it")
    print("  may not acquit).")
    return schlecht


def anker(tmp):
    """ANCHOR -- what is the anchor worth as part of a key?"""
    quelle = W / "beispiele" / "01-tabelle.gab"
    roh = quelle.read_text(encoding="utf-8")
    vor = register(quelle)
    ziel = tmp / "anker.gab"
    ziel.write_text("-- one new comment line at the very top.\n" + roh, encoding="utf-8")
    nach = register(ziel)
    if nach is None or len(vor) != len(nach):
        raise Aufbaufehler("the anchor probe did not produce a comparable register")
    a = sum(1 for x, y in zip(vor, nach) if x[2].split(":")[-1] != y[2].split(":")[-1])
    t = sum(1 for x, y in zip(vor, nach) if x[4] != y[4])
    print()
    print("== ANCHOR -- one comment line at the top of a file ==")
    print(f"  anchors moved                                         {a:>4} of {len(vor)}")
    print(f"  texts moved                                           {t:>4} of {len(vor)}")
    print("  **So the anchor stays OUT of the key.** It is the least stable field of the")
    print("  record: it moves for every line below any edit, including edits that touch no")
    print("  contract at all. It is kept for READING, and as the last resort where two")
    print("  lines of one unit agree in name, class and text.")
    return 0 if (a == len(vor) and t == 0) else 1


# --------------------------------------------------------------------------------------

DOPPELRUF = """module probe {

impl fn eng(k : u32)
    requires k < 64
    effects  { pure }
    costs    <= 2 ops
{ return; }

impl fn zweimal()
    effects { pure }
    costs   <= 8 ops
{
    eng(3);
    eng(3);
    return;
}

}
"""


def sprechprobe():
    """**Three directions, because this tool has three ways to be wrong quietly.**"""
    if not GABBRO.exists():
        print(f"ABBRUCH: {GABBRO} fehlt -- gebaut wird auf ki-pc-fisch-101 (CLAUDE.md).")
        print("  NICHTS wurde gemessen; das ist kein Bericht ueber einen sauberen Baum.")
        return 2
    erg = 0
    with tempfile.TemporaryDirectory() as td:
        tmp = pathlib.Path(td)

        # ONE -- the degenerate case is REAL and reachable in seventeen lines. Two calls to
        # one callee produce two lines agreeing in name, class, state AND text.
        ziel = tmp / "doppelruf.gab"
        ziel.write_text(DOPPELRUF, encoding="utf-8")
        z = register(ziel)
        if z is None:
            print("SPRECHPROBE GESCHEITERT: die Doppelrufprobe checkt nicht.", file=sys.stderr)
            return 2
        dreier = {(x[0], x[1], x[4]) for x in z}
        if len(z) != 2 or len(dreier) != 1:
            print(f"SPRECHPROBE GESCHEITERT: zwei Rufe ergeben {len(z)} Zeilen und "
                  f"{len(dreier)} Tripel -- erwartet 2 und 1.", file=sys.stderr)
            erg = 2
        elif z[0][2] == z[1][2]:
            print("SPRECHPROBE GESCHEITERT: die beiden Zeilen teilen sogar den Anker; "
                  "dann trennt sie NICHTS.", file=sys.stderr)
            erg = 2
        else:
            print("  Doppelruf: ok (zwei Zeilen, EIN Tripel, zwei Anker -- die Entartung "
                  "ist erreichbar)")

        # TWO -- the key MOVES on the swap. Without this direction the whole recommendation
        # would rest on a field nobody watched change.
        quelle = W / "beispiele" / "01-tabelle.gab"
        roh = quelle.read_text(encoding="utf-8")
        alt = ("ensures   c.slots[s].elter == None,\n"
               "              c.slots[s].vorheriges == None,\n"
               "              c.slots[s].naechstes == None")
        if alt not in roh:
            print("SPRECHPROBE GESCHEITERT: die Klausel, an der geschnitten wird, steht "
                  "nicht mehr so in `beispiele/01-tabelle.gab`.", file=sys.stderr)
            return 2
        ziel = tmp / "tausch.gab"
        ziel.write_text(roh.replace(
            alt, "ensures   c.slots[s].naechstes == None,\n"
                 "              c.slots[s].vorheriges == None,\n"
                 "              c.slots[s].elter == None"), encoding="utf-8")
        vor, nach = register(quelle), register(ziel)
        # **The anchor carries the FILE NAME**, and the probe file has a different one.
        # Comparing the whole field would report a difference this probe did not make --
        # the same shape as `W16`, in the measuring apparatus.
        def kern(z):
            return (z[0], z[1], z[2].split(":")[-1], z[3])
        namen_gleich = [kern(x) for x in vor] == [kern(y) for y in nach]
        text_anders = sum(1 for x, y in zip(vor, nach) if x[4] != y[4])
        if not namen_gleich:
            print("SPRECHPROBE GESCHEITERT: der Tausch bewegt schon Name/Klasse/Anker -- "
                  "dann misst diese Probe nicht, was `O3` beschreibt.", file=sys.stderr)
            erg = 2
        elif text_anders != 2:
            print(f"SPRECHPROBE GESCHEITERT: der Tausch bewegt {text_anders} Texte, "
                  "erwartet 2.", file=sys.stderr)
            erg = 2
        else:
            print("  Tausch:    ok (Name, Klasse, Anker und Zustand unveraendert; "
                  "GENAU zwei Texte anders)")

        # THREE -- and it does NOT move on a reformat. A key that moves on everything is a
        # ratchet that punishes editing, and that is the objection option (a) has to answer.
        ziel = tmp / "format.gab"
        ziel.write_text(roh.replace(
            alt, "ensures\n        c.slots[s].elter == None,\n"
                 "        c.slots[s].vorheriges == None,\n"
                 "        c.slots[s].naechstes == None"), encoding="utf-8")
        nach = register(ziel)
        if {(x[0], x[1], x[4]) for x in vor} != {(y[0], y[1], y[4]) for y in nach}:
            print("SPRECHPROBE GESCHEITERT: eine blosse Umformatierung bewegt den "
                  "Schluessel -- dann ist der Preis nicht der gemessene.", file=sys.stderr)
            erg = 2
        else:
            print("  Umbruch:   ok (eine Umformatierung laesst jeden Schluessel stehen)")

    # FOUR -- and the JUDGEMENT falls when the tree is wrong. The three above drive the
    # binary; this one drives the two counting functions, because a verdict that has never
    # been made to fall is not one. Both are printed into a swallowed stream: what is being
    # measured is the return value, not the wording.
    import io
    import contextlib
    schmutzig = [("a.gab", [("f :: g requires #1", "V", "a.gab:10", "open", "k < 64"),
                            ("f :: g requires #1", "V", "a.gab:20", "open", "k < 64")]),
                 ("b.gab", [("h :: maintains I", "E", "b.gab:3", "open", "--")])]
    sauber = [("a.gab", [("f :: ensures #1", "N", "a.gab:10", "open", "x == 1"),
                         ("f :: ensures #2", "N", "a.gab:11", "open", "y == 2")])]
    with contextlib.redirect_stdout(io.StringIO()):
        schlecht = schluessel(schmutzig)
        gut = schluessel(sauber)
        _, vertauschbar, _ = reichweite(sauber)
    if schlecht != (1, 1):
        print(f"SPRECHPROBE GESCHEITERT: ein doppeltes Tripel und eine Zeile ohne Text "
              f"ergeben {schlecht}, erwartet (1, 1).", file=sys.stderr)
        erg = 2
    elif gut != (0, 0):
        print(f"SPRECHPROBE GESCHEITERT: ein sauberes Register meldet {gut}.", file=sys.stderr)
        erg = 2
    elif len(vertauschbar) != 2:
        print(f"SPRECHPROBE GESCHEITERT: zwei Geschwister ergeben {len(vertauschbar)} "
              "vertauschbare Zeilen, erwartet 2.", file=sys.stderr)
        erg = 2
    else:
        print("  Urteil:    ok (ein doppeltes Tripel und eine Zeile ohne Text FALLEN, "
              "ein sauberes Register nicht)")
    return erg


def lauf():
    if not GABBRO.exists():
        print(f"ABBRUCH: {GABBRO} fehlt -- gebaut wird auf ki-pc-fisch-101 (CLAUDE.md).")
        print("  NICHTS wurde gemessen.")
        return 2
    dateien = korpus()
    if not dateien:
        print("ABBRUCH: kein `.gab` ausserhalb der Giftproben. NICHTS wurde gemessen.")
        return 2
    lagen = []
    ohne = 0
    for p in dateien:
        z = register(p)
        if z is None:
            ohne += 1
            continue
        if z:
            lagen.append((str(p.relative_to(W)), z))
    print(f"  units read                                            {len(dateien):>4}"
          "   (`*.gab`, poison probes excluded)")
    print(f"  of these WITHOUT a register (checker errors)          {ohne:>4}")
    print(f"  of these carrying at least one obligation line        {len(lagen):>4}")
    print()
    if not lagen:
        print("ABBRUCH: keine einzige Pflichtzeile. Ohne Zaehler ist das keine Messung.")
        return 2
    reichweite(lagen)
    stoss, leer = schluessel(lagen)
    with tempfile.TemporaryDirectory() as td:
        p = preis(pathlib.Path(td))
        a = anker(pathlib.Path(td))
    print()
    if stoss or leer:
        print(f"RATSCHENSCHLUESSEL GEFALLEN: {stoss} Tripel doppelt, {leer} ohne Text.")
        print("  Dann ist (Name, Klasse, Text) kein Schluessel mehr, und die Empfehlung")
        print("  von `OFFEN.md` `O3` braucht ihren letzten Ausweg: den Anker.")
        return 1
    if p or a:
        print(f"RATSCHENSCHLUESSEL GEFALLEN: {p} Preisfall(e) und {a} Ankerfall gegen die")
        print("  Vorhersage. Eine Entscheidung, deren Messung anders ausfaellt als sie,")
        print("  ist eine Meinung.")
        return 1
    print("== RATSCHENSCHLUESSEL: ALL PASS -- (Name, Klasse, Text) traegt ueber der")
    print("   ganzen Grundgesamtheit, und der Preis ist der gemessene ==")
    return 0


def main():
    print("== Sprechprobe des Werkzeugs ==")
    s = sprechprobe()
    if s:
        return s
    print()
    return lauf()


if __name__ == "__main__":
    if "--sprechprobe" in sys.argv:
        print("== Sprechprobe des Werkzeugs ==")
        sys.exit(sprechprobe())
    sys.exit(main())
