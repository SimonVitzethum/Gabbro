#!/usr/bin/env python3
"""**A qualified map queried directly -- the same trap for the third time.**

The maps of `Umgebung` are keyed QUALIFIED: `a::b::f`, not `f`. Whoever queries one of them
with a BARE name gets **`None` every time** inside a `module` block -- and that does not look
like an error, it looks like a rule that simply does not bite.

    self.u.funktionen.get(name)            -> None, always
    self.u.globale.contains_key(basis)     -> false, always

THREE TIMES THE SAME TRAP, EACH TIME DISCOVERED DIFFERENTLY
-----------------------------------------------------------
    2026-08-??  `M103`     `globale.get("Kappenraum")` never hit; the index bound said nothing.
    2026-08-25  `M108`     the refinement of `aufruf_toetet_fakten` was there and did NOTHING.
    2026-08-25  the same   `ist_weltname` over `globale.contains_key` -- again in the same run.

> **An error disguised as „no finding" is not caught by a note.** The second time a comment
> is enough; the third time a check belongs here.

WHAT THIS INSTRUMENT DOES NOT DO
---------------------------------
It does **not** say a site is wrong. Whether a bare name is wrong depends on whether the
caller already qualified -- that is not in the line. It sorts into three trays and carries a
RATCHET over the first:

    Tray 0  the `u` here is NOT an `Umgebung` -- a map of the same name in another struct
    Tray 1  a bare name on a qualified map            <- the ratchet
    Tray 2  a computed key -- not decidable from the line
    Tray 3  a module-aware resolver (`u.funktion`, `suche_global`, `ist_weltname`)

*The number in tray 1 may fall, not rise.* Moving a site to tray 3 lowers it; writing a new
one raises it and falls here.

TRAY 0, AND WHY IT EXISTS -- THE INSTRUMENT MEASURED THE WRONG OBJECT
----------------------------------------------------------------------
Until 2026-08-30 there was no tray 0, and the ratchet stood at 27 with **26 of its 28 sites
in `emit.rs`**. Those 26 were never queries on an `Umgebung` at all.

`emit.rs` has its own namespace struct, `Namen`, and **every one of its 61 signatures takes
`u: &Namen`, not one takes an `Umgebung`.** `Namen` happens to carry three fields with the
same names as `Umgebung` -- `funktionen`, `geraete`, `formate` -- and it fills all three with
a **BARE** key:

    umgebung.rs:654   self.geraete.insert(q(&d.name.text), felder);      QUALIFIED
    emit.rs:652       namen.geraete.insert(d.name.text.clone(), ...);    BARE

A bare name on a bare-keyed map is **correct**. The old regex matched on the FIELD NAME alone
and could not see which struct `u` was, so it read every one of them as the trap.

> **Measured over the whole history** (`messung/AUFLOESUNG-BEZUGSGROESSE.md`): the raw number
> grew 2 -> 28 between 2026-08-14 and 2026-08-30, and **every single step of that growth is in
> `emit.rs`**. The corrected number has been **2** the entire time -- 38 commits, 17 days,
> while `emit.rs` grew from nothing to 8 239 lines. *The ratchet was not measuring a surface
> that grows; it was measuring `emit.rs`.*
>
> And the founding cases settle it: all three times the trap actually bit -- `M103`
> (`globale`), `M108` (`aufruf_toetet_fakten`), `ist_weltname` -- it bit in code where `u` IS
> an `Umgebung`. **Not one of them was in `emit.rs`.**

**The exclusion needs BOTH criteria, and that is the safe direction.** A site drops to tray 0
only when the file declares no `u: &Umgebung` **and** fills that very map itself with a bare
key. One alone would be enough for `emit.rs` -- both agree across all 38 commits -- but a file
that queries a real `Umgebung` without ever writing the type down would then fall silently out
of the count. *An instrument that goes quiet is the failure it is here to catch.* Requiring
both means the doubtful case stays in tray 1 and someone has to look at it.
"""
import collections
import pathlib
import re
import sys

W = pathlib.Path(__file__).resolve().parent.parent
QUELLEN = sorted((W / "crates" / "gabbro-check" / "src").glob("*.rs"))
UMGEBUNG = W / "crates" / "gabbro-check" / "src" / "umgebung.rs"

# **The ratchet.** Measured 2026-08-30, after tray 0 separated the emitter's own `Namen` from
# the `Umgebung`: **2 sites, both in `m1.rs`** -- and those two are the ones that are a
# CHECKER. The mark fell from 27 to 2 not because anything was repaired but because 25 of
# those 27 were never on this map. *A ratchet may fall; this one fell by 25 in one step, and
# the step is a correction, not work* (`PLAN-AUTONOM.md` §1.8).
#
# The old value stood at 27 from 2026-08-25 with the note *„25 of them in the emitter"*. That
# sentence was the finding, written down and read as background for five days.
RATSCHE = 2

# A computed key: a variable one can see was built.
BERECHNET = re.compile(r"^&?(schluessel|schl|k|q|key|pfad|voll|qual)\b")
# A resolver instead of a map.
AUFLOESER = re.compile(r"\bu\.(funktion|suche_global|verbundfelder|ist_weltname|typ_von_ort)\(")
# `u: &Umgebung`, `u: &'a Umgebung`, `u: &mut Umgebung` -- the annotation that says this file's
# `u` really is the qualified environment.
IST_UMGEBUNG = re.compile(r"\bu:\s*&(?:'[a-z_]+\s+)?(?:mut\s+)?Umgebung\b")
# `namen.geraete.insert(x, ...)` with a key that is NOT `q(...)` -- the file keeps a map of
# that name itself, and keeps it BARE.
def eigene_blanke_karten(text):
    """Maps this file fills with a bare key -- its own namespace, not the `Umgebung`."""
    return set(re.findall(r"\b[a-z_]+\.([a-z_]+)\.insert\((?!q\(|qualifiziere\()", text))


def qualifizierte_karten(text):
    """Which maps are filled with `q(...)`/`qualifiziere(...)`?"""
    return sorted(set(re.findall(r"(?:self\.)?([a-z_]+)\.insert\((?:q|qualifiziere)\(", text)))


def stellen(karten, quellen):
    """(tray0, tray1, tray2, tray3) -- one list of (file, line, text) each."""
    muster = re.compile(
        r"\bu\.(" + "|".join(karten) + r")\.(?:get|contains_key)\(([^)]*)\)"
    )
    f0, f1, f2, f3 = [], [], [], []
    for p in quellen:
        if p.name == "umgebung.rs":
            continue
        text = p.read_text(encoding="utf-8")
        # **Both criteria, and only both together.** No `u: &Umgebung` anywhere in the file
        # AND the file fills this very map itself with a bare key -- then `u.KARTE` is that
        # file's own namespace and not the qualified environment. See the header.
        fremdes_u = not IST_UMGEBUNG.search(text)
        blanke = eigene_blanke_karten(text)
        for i, z in enumerate(text.splitlines(), 1):
            for m in muster.finditer(z):
                arg = m.group(2).strip()
                eintrag = (p.name, i, m.group(0))
                if fremdes_u and m.group(1) in blanke:
                    f0.append(eintrag)
                elif BERECHNET.match(arg):
                    f2.append(eintrag)
                else:
                    f1.append(eintrag)
            for m in AUFLOESER.finditer(z):
                f3.append((p.name, i, m.group(0)))
    return f0, f1, f2, f3


def sprechprobe():
    """**In both directions, on invented sources.** An instrument that reads only its own
    files measures how well they fit it."""
    import tempfile

    umg = 'fn s(&mut self) { self.funktionen.insert(q(&f.name.text), sig); }\n'
    schlecht = "fn a(u: &Umgebung) { let x = u.funktionen.get(&n.text); }\n"
    gut_berechnet = "fn a(u: &Umgebung) { let x = u.funktionen.get(&schluessel); }\n"
    gut_aufloeser = "fn a(u: &Umgebung) { let x = u.funktion(&self.modul, pf); }\n"
    # **A foreign `u` with a map of the same name, filled BARE.** Without tray 0 this line
    # lands in tray 1 and looks exactly like `a.rs` -- that is the error this instrument made
    # 26 times over. *The probe has to be able to tell them apart, or it proves nothing.*
    fremd = ("fn f(namen: &mut Namen) { namen.funktionen.insert(f.name.text.clone(), sig); }\n"
             "fn g(u: &Namen) { let x = u.funktionen.get(&n.text); }\n")
    # And the safe direction: a file with NO bare insert of its own stays in tray 1 even
    # without a `u: &Umgebung` annotation. An instrument that goes quiet is the failure.
    unklar = "fn a(u: &Irgendwas) { let x = u.funktionen.get(&n.text); }\n"
    with tempfile.TemporaryDirectory() as d:
        dp = pathlib.Path(d)
        (dp / "umgebung.rs").write_text(umg, encoding="utf-8")
        (dp / "a.rs").write_text(schlecht, encoding="utf-8")
        (dp / "b.rs").write_text(gut_berechnet, encoding="utf-8")
        (dp / "c.rs").write_text(gut_aufloeser, encoding="utf-8")
        (dp / "d.rs").write_text(fremd, encoding="utf-8")
        (dp / "e.rs").write_text(unklar, encoding="utf-8")
        karten = qualifizierte_karten(umg)
        quellen = sorted(dp.glob("*.rs"))
        f0, f1, f2, f3 = stellen(karten, quellen)
    dateien1 = sorted(x[0] for x in f1)
    return (
        karten == ["funktionen"],
        dateien1 == ["a.rs", "e.rs"],
        len(f2) == 1 and f2[0][0] == "b.rs",
        len(f3) == 1 and f3[0][0] == "c.rs",
        len(f0) == 1 and f0[0][0] == "d.rs",
    )


def main():
    # **TOOTH 0 -- THE SUBJECT HAS TO BE THERE** (2026-08-31). Over a tree without
    # `crates/` this tool died at `UMGEBUNG.read_text()` with a `FileNotFoundError`:
    # return code **1**, a traceback, and in a chain that reads like an unread call site.
    # *A crash is not a refusal -- a NAMED refusal is*, and a missing subject says the
    # SETUP has to change, not the tree.
    if not UMGEBUNG.is_file() or not QUELLEN:
        print(f"ABBRUCH: {UMGEBUNG.relative_to(W)} "
              f"{'da' if UMGEBUNG.is_file() else 'FEHLT'}, {len(QUELLEN)} Quelldateien im "
              "Zugriff -- es wurde NICHTS gemessen.", file=sys.stderr)
        print("  Ohne die Umgebung gibt es keine qualifizierte Karte, und `keine Luecke`"
              " waere\n  ein Urteil ueber nichts (W1, W17).", file=sys.stderr)
        return 2
    k_ok, f1_ok, f2_ok, f3_ok, f0_ok = sprechprobe()
    print("== Sprechprobe ==")
    print(f"  qualifizierte Karte erkannt:  {'ok' if k_ok else 'GESCHEITERT'}")
    print(f"  bloss uebergebener Name:      {'ok (Fach 1)' if f1_ok else 'GESCHEITERT'}")
    print(f"  berechneter Schluessel:       {'ok (Fach 2)' if f2_ok else 'GESCHEITERT'}")
    print(f"  modulbewusster Aufloeser:     {'ok (Fach 3)' if f3_ok else 'GESCHEITERT'}")
    print(f"  fremdes `u`, blanke Karte:    {'ok (Fach 0)' if f0_ok else 'GESCHEITERT'}")
    if not (k_ok and f1_ok and f2_ok and f3_ok and f0_ok):
        print("\n! Das Instrument misst nicht, was es behauptet. ABBRUCH.")
        return 2

    karten = qualifizierte_karten(UMGEBUNG.read_text(encoding="utf-8"))
    f0, f1, f2, f3 = stellen(karten, QUELLEN)

    print()
    print(f"== {len(karten)} qualifizierte Karten ==")
    print("   " + ", ".join(karten))
    print()
    print(f"== Fach 1 -- bloss uebergebener Name auf qualifizierter Karte: {len(f1)} ==")
    for datei, zeile, text in f1:
        print(f"   {datei}:{zeile}  {text}")
    print()
    je_datei = collections.Counter(d for d, _, _ in f1)
    print("   je Datei: " + ", ".join(f"{d} {n}" for d, n in je_datei.most_common()))
    print()
    print(f"== Fach 2 -- berechneter Schluessel, nicht aus der Zeile zu entscheiden: {len(f2)} ==")
    print(f"== Fach 3 -- modulbewusster Aufloeser: {len(f3)} ==")
    print()
    je_datei0 = collections.Counter(d for d, _, _ in f0)
    print(f"== Fach 0 -- das `u` ist KEINE `Umgebung`, die Karte gehoert der Datei: {len(f0)} ==")
    print("   je Datei: " + (", ".join(f"{d} {n}" for d, n in je_datei0.most_common())
                             or "(keine)"))
    print("   Diese Stellen fragen eine BLANK gefuellte Karte mit einem blanken Namen --")
    print("   das ist richtig, nicht die Falle. Bis zum 2026-08-30 standen sie in Fach 1")
    print("   und haben die Ratsche von 2 auf 28 getrieben, ohne dass je eine Falle")
    print("   zuschlug. *Ein Zaehler, der den Erzeuger misst statt seinen Gegenstand.*")

    print()
    print("== Und was das NICHT heisst ==")
    print("  Fach 1 ist kein Fehlerbefund. Ob ein bloss uebergebener Name falsch ist,")
    print("  haengt am Aufrufer -- das steht nicht in der Zeile. Was hier steht, ist eine")
    print("  FLAECHE, auf der dieselbe Falle dreimal zugeschlagen hat.")
    print("  Und Fach 0 ist kein Freispruch: es sagt, dass die Karte eine andere ist,")
    print("  nicht dass der Zugriff stimmt. Wer `Namen` qualifiziert fuellt, muss die")
    print("  Trennung hier nachziehen -- der Waechter merkt es nicht von selbst (W10).")

    print()
    print(f"== Arbeitsmenge: {len(QUELLEN)} Dateien, {len(karten)} Karten, "
          f"{len(f0) + len(f1) + len(f2) + len(f3)} Stellen, 5 Proben ==")

    if len(f1) > RATSCHE:
        print(f"\n! RATSCHE: {len(f1)} in Fach 1, erlaubt sind {RATSCHE}.")
        print("  Eine neue Stelle mit blossem Namen auf einer qualifizierten Karte.")
        return 1
    if len(f1) < RATSCHE:
        print(f"\n  Die Ratsche darf fallen: {len(f1)} statt {RATSCHE} -- "
              f"setze RATSCHE auf {len(f1)}.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
