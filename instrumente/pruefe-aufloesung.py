#!/usr/bin/env python3
"""**Die qualifizierte Karte, direkt befragt -- dieselbe Falle zum dritten Mal.**

Die Karten der `Umgebung` sind QUALIFIZIERT verschluesselt: `a::b::f`, nicht `f`. Wer eine
davon mit einem BLOSSEN Namen befragt, bekommt in einem `module`-Block **immer `None`** --
und das sieht nicht wie ein Fehler aus, sondern wie eine Regel, die eben nicht greift.

    self.u.funktionen.get(name)            -> None, immer
    self.u.globale.contains_key(basis)     -> false, immer

DREIMAL DIESELBE FALLE, UND JEDES MAL ANDERS ENTDECKT
------------------------------------------------------
    2026-08-?? `M103`      `globale.get("Kappenraum")` traf nie; die Indexschranke sagte nichts.
    2026-08-25 `M108`      die Verfeinerung von `aufruf_toetet_fakten` war da und tat NICHTS.
    2026-08-25 dieselbe    `ist_weltname` ueber `globale.contains_key` -- im selben Zug nochmal.

> **Ein Fehler, der sich als „kein Befund" tarnt, wird nicht durch eine Notiz gefunden.**
> Beim zweiten Mal reicht ein Kommentar; beim dritten gehoert eine Pruefung her.

WAS DIESES INSTRUMENT NICHT TUT
--------------------------------
Es sagt **nicht**, dass eine Stelle falsch ist. Ob ein bloss uebergebener Name falsch ist,
haengt daran, ob der Aufrufer schon qualifiziert hat -- das steht nicht in der Zeile. Es
sortiert in drei Faecher und fuehrt eine RATSCHE ueber dem ersten:

    Fach 1  ein bloss uebergebener Name auf einer qualifizierten Karte   <- die Ratsche
    Fach 2  ein berechneter Schluessel -- nicht aus der Zeile zu entscheiden
    Fach 3  ein modulbewusster Aufloeser (`u.funktion`, `suche_global`, `ist_weltname`)

*Die Zahl in Fach 1 darf fallen, nicht steigen.* Wer eine Stelle nach Fach 3 zieht, senkt
sie; wer eine neue schreibt, hebt sie und faellt hier.
"""
import collections
import pathlib
import re
import sys

W = pathlib.Path(__file__).resolve().parent.parent
QUELLEN = sorted((W / "crates" / "gabbro-check" / "src").glob("*.rs"))
UMGEBUNG = W / "crates" / "gabbro-check" / "src" / "umgebung.rs"

# **Die Ratsche.** Gemessen am 2026-08-25, nach der `M108`-Reparatur: 27 Stellen, davon
# **25 im Erzeuger**. Das ist kein Zufall und auch keine Entwarnung -- `emit.rs` laeuft nach
# allen Pruefungen und arbeitet stellenweise auf schon aufgeloesten Namen. *Die zwei in
# `m1.rs` sind die, die ein Pruefer sind.*
RATSCHE = 27

# Ein berechneter Schluessel: eine Variable, der man ansieht, dass sie gebaut wurde.
BERECHNET = re.compile(r"^&?(schluessel|schl|k|q|key|pfad|voll|qual)\b")
# Ein Aufloeser statt einer Karte.
AUFLOESER = re.compile(r"\bu\.(funktion|suche_global|verbundfelder|ist_weltname|typ_von_ort)\(")


def qualifizierte_karten(text):
    """Welche Karten werden mit `q(...)`/`qualifiziere(...)` gefuellt?"""
    return sorted(set(re.findall(r"(?:self\.)?([a-z_]+)\.insert\((?:q|qualifiziere)\(", text)))


def stellen(karten, quellen):
    """(fach1, fach2, fach3) -- je eine Liste von (datei, zeile, text)."""
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
    """**In beide Richtungen, an erfundenen Quellen.** Ein Instrument, das nur die eigenen
    Dateien liest, misst, wie gut sie zu ihm passen."""
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
