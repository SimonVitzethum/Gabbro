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

    Tray 1  a bare name on a qualified map            <- the ratchet
    Tray 2  a computed key -- not decidable from the line
    Tray 3  a module-aware resolver (`u.funktion`, `suche_global`, `ist_weltname`)

*The number in tray 1 may fall, not rise.* Moving a site to tray 3 lowers it; writing a new
one raises it and falls here.
"""
import collections
import pathlib
import re
import sys

W = pathlib.Path(__file__).resolve().parent.parent
QUELLEN = sorted((W / "crates" / "gabbro-check" / "src").glob("*.rs"))
UMGEBUNG = W / "crates" / "gabbro-check" / "src" / "umgebung.rs"

# **The ratchet.** Measured 2026-08-25, after the `M108` repair: 27 sites, **25 of them in
# the emitter**. That is neither an accident nor an all-clear -- `emit.rs` runs after every
# check and works in places on already resolved names. *The two in `m1.rs` are the ones that
# are a CHECKER.*
RATSCHE = 27

# A computed key: a variable one can see was built.
BERECHNET = re.compile(r"^&?(schluessel|schl|k|q|key|pfad|voll|qual)\b")
# A resolver instead of a map.
AUFLOESER = re.compile(r"\bu\.(funktion|suche_global|verbundfelder|ist_weltname|typ_von_ort)\(")


def qualifizierte_karten(text):
    """Which maps are filled with `q(...)`/`qualifiziere(...)`?"""
    return sorted(set(re.findall(r"(?:self\.)?([a-z_]+)\.insert\((?:q|qualifiziere)\(", text)))


def stellen(karten, quellen):
    """(tray1, tray2, tray3) -- one list of (file, line, text) each."""
    muster = re.compile(
        r"\bu\.(" + "|".join(karten) + r")\.(?:get|contains_key)\(([^)]*)\)"
    )
    f1, f2, f3 = [], [], []
    for p in quellen:
        if p.name == "umgebung.rs":
            continue
        for i, z in enumerate(p.read_text(encoding="utf-8").splitlines(), 1):
            for m in muster.finditer(z):
                arg = m.group(2).strip()
                eintrag = (p.name, i, m.group(0))
                if BERECHNET.match(arg):
                    f2.append(eintrag)
                else:
                    f1.append(eintrag)
        for i, z in enumerate(p.read_text(encoding="utf-8").splitlines(), 1):
            for m in AUFLOESER.finditer(z):
                f3.append((p.name, i, m.group(0)))
    return f1, f2, f3


def sprechprobe():
    """**In both directions, on invented sources.** An instrument that reads only its own
    files measures how well they fit it."""
    import tempfile

    umg = 'fn s(&mut self) { self.funktionen.insert(q(&f.name.text), sig); }\n'
    schlecht = "fn a() { let x = u.funktionen.get(&n.text); }\n"
    gut_berechnet = "fn a() { let x = u.funktionen.get(&schluessel); }\n"
    gut_aufloeser = "fn a() { let x = u.funktion(&self.modul, pf); }\n"
    with tempfile.TemporaryDirectory() as d:
        dp = pathlib.Path(d)
        (dp / "umgebung.rs").write_text(umg, encoding="utf-8")
        (dp / "a.rs").write_text(schlecht, encoding="utf-8")
        (dp / "b.rs").write_text(gut_berechnet, encoding="utf-8")
        (dp / "c.rs").write_text(gut_aufloeser, encoding="utf-8")
        karten = qualifizierte_karten(umg)
        quellen = sorted(dp.glob("*.rs"))
        f1, f2, f3 = stellen(karten, quellen)
    return (
        karten == ["funktionen"],
        len(f1) == 1 and f1[0][0] == "a.rs",
        len(f2) == 1 and f2[0][0] == "b.rs",
        len(f3) == 1 and f3[0][0] == "c.rs",
    )


def main():
    k_ok, f1_ok, f2_ok, f3_ok = sprechprobe()
    print("== Sprechprobe ==")
    print(f"  qualifizierte Karte erkannt:  {'ok' if k_ok else 'GESCHEITERT'}")
    print(f"  bloss uebergebener Name:      {'ok (Fach 1)' if f1_ok else 'GESCHEITERT'}")
    print(f"  berechneter Schluessel:       {'ok (Fach 2)' if f2_ok else 'GESCHEITERT'}")
    print(f"  modulbewusster Aufloeser:     {'ok (Fach 3)' if f3_ok else 'GESCHEITERT'}")
    if not (k_ok and f1_ok and f2_ok and f3_ok):
        print("\n! Das Instrument misst nicht, was es behauptet. ABBRUCH.")
        return 2

    karten = qualifizierte_karten(UMGEBUNG.read_text(encoding="utf-8"))
    f1, f2, f3 = stellen(karten, QUELLEN)

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
    print("== Und was das NICHT heisst ==")
    print("  Fach 1 ist kein Fehlerbefund. Ob ein bloss uebergebener Name falsch ist,")
    print("  haengt am Aufrufer -- das steht nicht in der Zeile. Was hier steht, ist eine")
    print("  FLAECHE, auf der dieselbe Falle dreimal zugeschlagen hat.")

    print()
    print(f"== Arbeitsmenge: {len(QUELLEN)} Dateien, {len(karten)} Karten, "
          f"{len(f1) + len(f2) + len(f3)} Stellen, 4 Proben ==")

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
