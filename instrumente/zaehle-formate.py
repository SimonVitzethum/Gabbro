#!/usr/bin/env python3
"""**`@version`: die Zahl hinter der ABSAGE an die Formatentwicklung -- als Befehl.**

    ./instrumente/zaehle-formate.py [--stellen]

WOZU
----
Am 2026-08-21 ist Entscheidung 12 gefallen: **ein `@version 3`-Leser liest KEIN v2.** Der
Grund war eine Messung und keine Abwaegung --

    14 `@version`-Angaben in Korpus + FRAGMENTE:  12 x „1“, 2 x „17“
     0 Formate mit einer zweiten Fassung

-- und diese Zahlen waren **von Hand genommen** (`grep -o "@version [0-9]*"`). Eine Zahl ohne
Werkzeug ist ein Rueckstand, kein Ergebnis. Hier steht der Befehl, der sie nachrechnet -- und
der rot wird, wenn die Voraussetzung der Entscheidung stirbt.

**Der Ruecklaufwert ist 1, sobald ein Format eine zweite Fassung hat.** Das ist kein
Schoenheitsfehler, sondern der Sinn: die Absage ruht auf „null gemessene
Formatentwicklungen“. Taucht die erste auf, ist die Entscheidung neu zu fuehren, und dann
muss es jemand ERFAHREN, statt es in einer Ausgabe zu ueberlesen.

DIE DEFINITION IST DIE MESSUNG
------------------------------
**Ein „Format mit einer zweiten Fassung“ ist ein Formatname, der in der gemessenen Menge mit
ZWEI VERSCHIEDENEN `@version`-Werten auftritt.**

*Warum diese und nicht eine andere:*

* **Nicht** „derselbe Name zweimal in EINER Uebersetzungseinheit“. Das faellt schon heute als
  `N001` (*„`Kopf` is declared twice in this scope (format)“*, gemessen 2026-08-21 an einer
  Handprobe) -- und zwar unveraendert, ob sich die `@version` unterscheidet oder nicht. Eine
  Zaehlung darueber koennte nie etwas finden und misst damit nichts (R14).
* **Nicht** „derselbe Name mehr als einmal irgendwo“. Im Korpus heisst fuenfmal ein Format
  `Pte`, dreimal `Kopf`, zweimal `IpKopf` -- in verschiedenen, voneinander unabhaengigen
  Programmen. Das misst, wie beliebt ein Name ist, nicht ob ein Format sich entwickelt hat.
  *Die Zahl steht trotzdem unten, als OBERE Schranke einer weiteren Lesart.*
* **Die `@version` ist das einzige Stueck Sprache, das eine Fassung BENENNT.** Das Paar
  (Name, Version) ist deshalb, was eine Fassung ist -- alles andere waere eine Vermutung
  ueber die Absicht des Schreibers.

RICHTUNG DES FEHLERS (W10)
--------------------------
**Die 0 ist eine UNTERE Schranke.** Was diese Zaehlung NICHT sehen kann:

* eine Entwicklung, die einen NEUEN NAMEN bekam (`Kopf` -> `KopfV2`) statt einer neuen
  Nummer. Dagegen laeuft unten eine Namensheuristik, und sie sagt ihre eigene Zahl.
* eine Entwicklung, die IN DERSELBEN Deklaration passierte -- Felder geaendert, Nummer
  stehengelassen. Das steht in der `git`-Geschichte und nicht im Text; hier wird es nicht
  gemessen und deshalb hier gesagt.

**Und die 14 selbst ist nicht das, wonach sie aussieht.** `messung/fragmente/*.gab` ist nach
dem eigenen README *byteidentisch* mit `dokumente/FRAGMENTE.md`; die 14 zaehlt also
**siebenmal dasselbe zweimal**. Beide Zahlen stehen unten -- die 14 als Textstellen, die 7
als verschiedene Deklarationen -- weil die Buchung im TODO die 14 nennt und eine Zaehlung,
die eine Zahl stillschweigend ersetzt, ihre eigene Buchfuehrung unlesbar macht.

WAS DIESE ZAEHLUNG NICHT IST
----------------------------
Sie sagt **nichts** darueber, ob `@version` einen LESER hat. Der ist getrennt gemessen und
das Ergebnis steht in der Uebergabe: `pub version: Option<u128>` (`ast.rs:1223`) wird vom
Erzeuger geschrieben und in den ganzen `crates/` **von keiner einzigen Stelle gelesen**
(`grep -rn "\\.version" --include=*.rs crates/` findet nichts).
"""
import pathlib
import re
import sys

W = pathlib.Path(__file__).resolve().parent.parent
FRAGMENTE = W / "dokumente" / "FRAGMENTE.md"
# Die Sprachbeschreibung ist KEIN Korpus -- ihre Beispiele werden nie geprueft. Sie wird
# getrennt gezaehlt, weil der Handgriff im TODO sie uebersehen hat und dort ausgerechnet die
# `@version 3` steht, von der die Entscheidung ihren Namen hat.
SPRACHE = W / "dokumente" / "SPRACHE.md"

# `format` ganz am Zeilenanfang: so steht es im Korpus und in beiden Dokumenten. Ein
# eingerueckter `format` waere in Gabbro nicht falsch -- dass die Zaehlung ihn nicht saehe,
# ist die zweite Stelle, an der sie zu WENIG findet (W10).
FORMAT = re.compile(r"^format\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?:@version\s+(\d+))?", re.M)
# Ein Name, der auf eine Fassungsnummer endet: `KopfV2`, `Kopf_v2`, `Kopf2`. **Nicht** `Lo`
# und `Hi` -- `FaultRecordLo`/`FaultRecordHi` sind die zwei HAELFTEN eines Satzes, nicht zwei
# Fassungen, und eine Heuristik, die das verwechselt, meldet zwei Funde ohne einen einzigen.
FASSUNGSNAME = re.compile(r"^(.*?)[_]?[vV]?(\d+)$")


def formate(text):
    """Alle Formatdeklarationen eines Textes als `(name, version_oder_None)`."""
    return [(m.group(1), int(m.group(2)) if m.group(2) else None)
            for m in FORMAT.finditer(text)]


def zweite_fassungen(funde):
    """Namen, die mit ZWEI VERSCHIEDENEN `@version`-Werten auftreten.

    `funde` ist eine Liste `(name, version_oder_None)`. Ein Name ohne `@version` zaehlt
    NICHT als eigene Fassung -- „keine Nummer“ ist keine Nummer, und ein Format ohne
    `@version` neben einem mit ist genau der Fall, in dem niemand eine Entwicklung erklaert
    hat.
    """
    je_name = {}
    for name, v in funde:
        if v is not None:
            je_name.setdefault(name, set()).add(v)
    return {n: sorted(vs) for n, vs in je_name.items() if len(vs) > 1}


def fassungspaare(namen):
    """Namen, die sich nur um eine angehaengte Fassungsnummer unterscheiden.

    Die OBERE Schranke gegen den blinden Fleck der `@version`-Zaehlung: wer statt einer
    neuen Nummer einen neuen Namen vergibt, wird von `zweite_fassungen` nicht gesehen.
    """
    stamm = {}
    for n in namen:
        m = FASSUNGSNAME.match(n)
        s = m.group(1) if m and m.group(1) else n
        stamm.setdefault(s, set()).add(n)
    return {s: sorted(ns) for s, ns in stamm.items() if len(ns) > 1}


def sprechprobe():
    """**In beide Richtungen, an erfundenen Quellen.** Eine Zaehlung, die nur die eigenen
    Dateien liest, misst, wie gut sie zu ihr passen -- und eine, die nie etwas finden kann,
    misst gar nichts (R14).
    """
    mit = ("format Kopf @version 1 endian big {\n}\n"
           "format Kopf @version 2 endian big {\n}\n")
    ohne = ("format Kopf @version 1 endian big {\n}\n"
            "format Rumpf @version 1 endian big {\n}\n"
            "format Kopf @version 1 endian little {\n}\n")
    a = zweite_fassungen(formate(mit))
    b = zweite_fassungen(formate(ohne))
    # Die Namensheuristik, ebenfalls in beide Richtungen: ein Paar MUSS auffallen, zwei
    # Haelften eines Satzes duerfen es NICHT.
    p_ja = fassungspaare(["Kopf", "KopfV2"])
    p_nein = fassungspaare(["FaultRecordLo", "FaultRecordHi"])
    return [
        ("zwei Fassungen werden gefunden", a == {"Kopf": [1, 2]}),
        ("dieselbe Fassung zweimal faellt NICHT", b == {}),
        ("`Kopf`/`KopfV2` faellt der Namensheuristik auf", len(p_ja) == 1),
        ("`...Lo`/`...Hi` faellt ihr NICHT auf", p_nein == {}),
        ("ein Format ohne `@version` erzeugt keine Fassung",
         zweite_fassungen(formate("format Kopf endian big {\n}\n"
                                  "format Kopf @version 2 endian big {\n}\n")) == {}),
    ]


def main():
    proben = sprechprobe()
    print("== Sprechprobe, in beide Richtungen ==")
    for was, gut in proben:
        print(f"  {'ok ' if gut else 'ROT'}  {was}")
    if not all(g for _, g in proben):
        print("SPRECHPROBE GESCHEITERT -- es wurde NICHTS gemessen.", file=sys.stderr)
        # **Every refusal in this file ends with 2, not 1** (2026-08-31). This counter joined
        # `abnahme.py` that day, so its return code is now read as a VERDICT -- and the sixth
        # requirement applies: `1` means the TREE has to change, `2` means the SETUP does.
        # Every site below says NOTHING WAS MEASURED, so every one of them is a `2`.
        return 2
    print()

    if not FRAGMENTE.is_file():
        print(f"ABBRUCH: {FRAGMENTE} fehlt -- es wird NICHT null gemessen.", file=sys.stderr)
        return 2

    korpus = sorted(W.glob("beispiele/**/*.gab")) + sorted(W.glob("messung/**/*.gab")) \
        + sorted(W.glob("messungen/**/*.gab"))
    if not korpus:
        print("ABBRUCH: kein einziges `.gab` gefunden -- der Gegenstand fehlt.",
              file=sys.stderr)
        return 2

    # (a) Textstellen -- was der Handgriff im TODO gezaehlt hat.
    stellen = []          # (datei, zeile, name, version)
    for p in korpus + [FRAGMENTE]:
        text = p.read_text(encoding="utf-8", errors="replace")
        for m in FORMAT.finditer(text):
            zeile = text[:m.start()].count("\n") + 1
            stellen.append((p.relative_to(W), zeile, m.group(1),
                            int(m.group(2)) if m.group(2) else None))
    versioniert = [s for s in stellen if s[3] is not None]

    # (b) Verschiedene Deklarationen -- `messung/fragmente/` ist byteidentisch mit
    #     FRAGMENTE.md, die Textstellen dort sind DIESELBE Deklaration ein zweites Mal.
    aus_md = {(n, v) for d, _, n, v in stellen if d == FRAGMENTE.relative_to(W)}
    doppelt = [s for s in stellen
               if s[0] != FRAGMENTE.relative_to(W) and (s[2], s[3]) in aus_md
               and s[3] is not None]
    verschieden = len(versioniert) - len(doppelt)
    # **Und ab hier wird OHNE die Doppelten gerechnet.** Sonst meldet jede weitere Lesart
    # die Byteidentitaet noch einmal als Befund -- `ContextEntryHi: 2 x` waere dann ein
    # Name, der zweimal vorkommt, und ist doch dieselbe Zeile in zwei Dateien.
    einmal = [s for s in stellen if s not in doppelt]

    print("== `@version` in Korpus und FRAGMENTE ==")
    print(f"  {len(versioniert)} @version-Textstellen in Korpus + FRAGMENTE")
    verteilung = {}
    for _, _, _, v in versioniert:
        verteilung[v] = verteilung.get(v, 0) + 1
    for v in sorted(verteilung):
        print(f"    {verteilung[v]} x @version {v}")
    print(f"  {verschieden} verschiedene @version-Deklarationen")
    print(f"    {len(doppelt)} Textstellen sind dieselbe Deklaration ein zweites Mal --")
    print("    `messung/fragmente/*.gab` ist byteidentisch mit `dokumente/FRAGMENTE.md`")
    print()

    # (c) Die Sprachbeschreibung -- getrennt, weil sie kein Korpus ist.
    ausserhalb = []
    if SPRACHE.is_file():
        ausserhalb = [(SPRACHE.relative_to(W), n, v)
                      for n, v in formate(SPRACHE.read_text(encoding="utf-8",
                                                            errors="replace"))
                      if v is not None]
    print("== Ausserhalb der gemessenen Menge ==")
    print(f"  {len(ausserhalb)} @version-Angaben in der Sprachbeschreibung")
    for d, n, v in ausserhalb:
        print(f"    {d}: format {n} @version {v}")
    print("    Kein Korpus: diese Beispiele werden von keinem Lauf geprueft. Sie stehen")
    print("    hier, weil der Handgriff im TODO sie nicht sah -- und weil ausgerechnet")
    print("    dort die `@version 3` steht, von der die Entscheidung ihren Namen hat.")
    print()

    # (d) Die Zahl, auf der die Entscheidung ruht.
    zweite = zweite_fassungen([(n, v) for _, _, n, v in einmal])
    mehrfach = {}
    for _, _, n, _ in einmal:
        mehrfach[n] = mehrfach.get(n, 0) + 1
    mehrfach = {n: k for n, k in mehrfach.items() if k > 1}
    paare = fassungspaare({n for _, _, n, _ in einmal})

    print("== Die Zahl, auf der Entscheidung 12 ruht ==")
    print(f"  {len(zweite)} Formate mit einer zweiten Fassung")
    for n, vs in sorted(zweite.items()):
        print(f"    {n}: @version " + ", ".join(str(v) for v in vs))
    print(f"  {len(paare)} Namenspaare sehen wie eine zweite Fassung aus (`Kopf`/`KopfV2`)")
    for s, ns in sorted(paare.items()):
        print(f"    {s}: " + ", ".join(ns))
    print(f"  {len(mehrfach)} Namen kommen mehrfach vor -- OBERE Schranke einer weiteren")
    print("    Lesart (ohne die byteidentischen Doppel), und keiner davon mit einem")
    print("    `@version`-Unterschied; es sind unabhaengige Programme mit gleichem Namen:")
    for n, k in sorted(mehrfach.items(), key=lambda x: (-x[1], x[0])):
        print(f"      {n}: {k} x")
    print()

    if "--stellen" in sys.argv:
        print("== Jede Textstelle ==")
        for d, z, n, v in stellen:
            print(f"  {d}:{z}  format {n}"
                  + (f" @version {v}" if v is not None else "   (ohne @version)"))
        print()

    print("== Und was das NICHT heisst ==")
    print("  Die 0 ist eine UNTERE Schranke. Eine Entwicklung, die einen neuen NAMEN statt")
    print("  einer neuen Nummer bekam, sieht nur die Namensheuristik; eine, die in DERSELBEN")
    print("  Deklaration passierte, sieht keine der beiden -- die steht in der")
    print("  `git`-Geschichte und nicht im Text.")
    print("  Und diese Zaehlung sagt NICHTS darueber, ob `@version` einen LESER hat.")
    print("  (Er hat keinen: `ast.rs:1223` schreibt das Feld, `crates/` liest es nirgends.)")
    print()
    print(f"== Arbeitsmenge: {len(korpus)} Dateien im Korpus, {len(stellen)} "
          f"format-Deklarationen, {len(versioniert)} davon mit `@version` ==")
    print(f"  {len(stellen) - len(versioniert)} Formate tragen gar keine Fassungsnummer.")

    if zweite:
        print()
        print(f"== ROT: {len(zweite)} Formate mit einer zweiten Fassung ==")
        print("   Entscheidung 12 ruht auf „null gemessene Formatentwicklungen“.")
        print("   Diese Voraussetzung ist gefallen -- die Entscheidung ist neu zu fuehren.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
