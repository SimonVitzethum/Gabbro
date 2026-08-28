#!/usr/bin/env python3
"""**Der Klauselwaechter. Die Klasse heisst: DEKLARIERT, GETRAGEN, NIE GELESEN.**

Dreimal in zwei Wochen dasselbe Muster, und jedes Mal von Hand gefunden:

    `rank`      deklariert, im Zeugnis, von keinem Pass gegen die Sperrordnung gehalten
    `opaque`    deklariert, ein VERBOT -- und es biss an keiner Rechenstelle
    `ensures`   deklariert, im Zeugnis GEZAEHLT, gegen keinen Rumpf gehalten

**Der erste Aufstieg, 2026-08-18:** `progress` hatte keinen Leser -- gefunden von diesem
Werkzeug, nicht von Hand. `schleifen.rs` liest ihn jetzt (`S003`/`S004`), und die Ratsche hat
die Zeile beim naechsten Lauf als VERALTET gemeldet. *Genau dafuer klemmt sie in beide
Richtungen.*

**Der zweite, am selben Tag: `ensures`** -- der Fall, der der Klasse ihren Namen gab.
`M109`/`M110`/`M111` pruefen die WOHLGEFORMTHEIT, nicht den Beweis: aufloesende Namen,
`result` nur wo es eins gibt, und keine Zusage ohne einen Ort, an dem die Funktion sie
herstellen koennte. *Beim ersten Lauf fiel ein Fund im Korpus an -- `ensures unberuehrt <=
s.len` nannte den FUNKTIONSNAMEN statt `result`, und die Zeile stand seit dem Schnitt da.*

Ein Muster, das dreimal von Hand gefunden wird, ist kein Zufall, sondern ein fehlendes
Werkzeug. **Und die vierte Fundstelle ist teurer als die dritte**, weil auf ihr dann schon
etwas steht: wertgetragene Indextypen bauen auf `opaque`, die Bibliotheks-ABI baut auf
`ensures`. *Den Boden reparieren, bevor das Stockwerk kommt, ist billiger als danach.*

    ./instrumente/pruefe-klauseln.py            -- Bericht, Ausgang 1 bei einer NEUEN Fundstelle

DAS MASS
--------
Quelle ist mechanisch: **jedes `pub`-Feld jeder `pub struct` in `ast.rs`** -- die ganze
Flaeche, die der Leser fuellt. Keine Auswahl, keine Kuratierung; wer eine Klausel
hinzufuegt, kann sie nicht aus der Liste heraushalten.

Leser sind die Dateien des Pruefers. Sie zerfallen in zwei Lager, und die Trennung IST die
Aussage:

    PASS      alles unter gabbro-check/src ausser den beiden unten -- hier wird GEPRUEFT
    TRAGEND   emit.rs, zeugnis.rs, gabbro-cli -- hier wird nur ABGESENKT und BERICHTET

Daraus drei Stufen:

    gelesen        mindestens ein Pass greift zu               -- in Ordnung
    nur getragen   nur emit/zeugnis/cli                        -- **die Klasse**
    ungelesen      niemand ausserhalb des Lesers               -- die Klasse, schaerfer

**Die Vergroeberung geht in die sichere Richtung.** Gemessen wird je NAME, nicht je
Struktur: heisst ein Feld in zwei Strukturen gleich und liest ein Pass nur das eine, gilt
der Name als gelesen. Der Bericht ist damit eine UNTERE Schranke der Klasse -- was er nennt,
ist echt; was er nicht nennt, kann trotzdem da sein (W10). *Er darf darum verpflichten und
nicht freisprechen.*

**Und dieses Argument deckte einen Fall NICHT ab -- gefunden 2026-08-28 an `kosten`.** Es
spricht von zwei Strukturen in `ast.rs`. Der teure Fall ist ein Feldname, den eine
PRUEFERINTERNE Struktur traegt, die in `ast.rs` gar nicht vorkommt: `opsruf::Kopf.kosten`
ist die gezaehlte Kostenzahl einer erzeugten Ops-Operation (`i128`), `Invariante.kosten` ein
`Expr`. `felder()` liest nur `ast.rs` und weiss von `Kopf` nichts -- der Textzugriff
`.kosten` in `opsruf.rs` und `umgebung.rs` galt darum als Pass, der die INVARIANTENKLAUSEL
liest, und die Ratsche meldete sie als GESTIEGEN. **Sie war es nicht.**

> *Die Vergroeberung geht in die sichere Richtung, solange sie nur BUCHT. Die Ratsche
> ent-bucht* -- und in dieser Richtung ist derselbe Fehler nicht sicher, sondern still: eine
> Klausel, die kein Pass liest, faellt aus der Buchhaltung, weil anderswo ein Feld gleich
> heisst. Genau die Bewegung, gegen die dieses Werkzeug gebaut ist (W16).

Darum zaehlt es seit heute die **Homonyme** -- Feldnamen, die auch eine prueferinterne
Struktur traegt -- und fuehrt die entschiedenen davon in `HOMONYME`, je Eintrag mit dem
Grund. Was dort nicht steht, wird weiter grob gemessen; die Zahl sagt, wie gross diese
Flaeche ist.
"""
import re
import subprocess
import sys
from pathlib import Path

W = Path(__file__).resolve().parent.parent
AST = W / "crates/gabbro-syntax/src/ast.rs"
PRUEFER = W / "crates/gabbro-check/src"
# **`zeremonie.rs` gehoert hierher und nicht zu den Paessen** (2026-08-20). Es BERICHTET
# ueber Klauseln, es prueft keine -- stuende es im anderen Lager, waere jede Klausel, die nur
# das Zeremonieregister anfasst, als „von einem Pass gelesen" gebucht. *Genau die Bewegung,
# gegen die dieser Waechter gebaut ist.*
TRAGEND_DATEIEN = {"emit.rs", "zeugnis.rs", "zeremonie.rs"}

# **Die bekannten Fundstellen -- und jede mit dem Satz, warum sie offen ist.**
#
# Ein Eintrag hier ist kein Freispruch, sondern eine Buchung: er steht in `TODO.md` und
# faellt dort. Eine Zeile, die STEIGT (der Pass liest sie jetzt), laesst dieses Werkzeug
# ebenfalls anschlagen -- *eine Tabelle, die nur waechst, ist eine Ausnahmeliste; eine, die
# in beide Richtungen klemmt, ist eine Ratsche.*
ERWARTET = {
    # **`abstieg` ist am 2026-08-19 AUFGESTIEGEN und darum hier geloescht** -- achter Aufstieg,
    # dritter Posten von «NL.2», und die schaerfste der Liste: an ihm hing die TERMINIERUNG.
    # `S005` prueft die NOTWENDIGE Bedingung -- ein Mass, das weder die Traversierungsvariable
    # noch einen vom Rumpf geschriebenen Namen nennt, ist konstant und faellt nie. *DASS es
    # faellt, bleibt Beweisersache (`consuming.ordnung`).* Korpuspreis: null.
    # **`touches` ist am 2026-08-19 AUFGESTIEGEN und darum hier geloescht** -- siebter
    # Aufstieg, zweiter Posten von «NL.2». `E011` haelt den Rumpf der Traversierung gegen die
    # genannten Orte, mit derselben `deckt`-Funktion wie `E005`/`E010`. *`touches` ist die
    # ENGERE Zusage neben `effects`, und eine engere, die niemand haelt, ist schlimmer als
    # keine.* Korpuspreis: null.
    # **`verlaesst` ist am 2026-08-19 AUFGESTIEGEN -- und der Satz, der hier stand, war
    # FALSCH.** Er lautete: *„welche Wege die Schleife verlassen darf"*. `SPRACHE.md`:730 sagt
    # etwas anderes: `leave`/`return` aus einem Bereich, der LINEARE Werte haelt, verlangt,
    # dass sie genannt werden. **`leaves` nennt die Werte, nicht die Ausgaenge** -- die nennt
    # `leave <schleife>`, eine Schleifenmarke.
    #
    # > *Der erste Anlauf baute die Regel nach DIESER Zeile und meldete zwei Befunde an einem
    # > richtigen Korpus.* **Eine Klauselbeschreibung in dieser Tabelle ist keine Quelle.**
    # `L106` prueft jetzt die Wohlgeformtheit: der Name ist eine Bindung, und sie ist linear.

    # -- FREMD: die Klausel beschreibt etwas AUSSERHALB dieser Uebersetzungseinheit -------
    #
    # **Und die Klasse ist nur zulaessig, wenn das ZEUGNIS die Klausel druckt.** Sonst waere
    # sie eine Ausnahmeliste: „kann man nicht pruefen" ist keine Buchung. Wer nicht pruefen
    # kann, EXPORTIERT -- und genau das tut die `entrust`-Zeile in Abschnitt E.
    "regs_gast":    ("FREMD", "Welche Register der GAST beim Eintritt hat. Der Gast steht nicht im Baum; das Zeugnis druckt den Vertrag."),
    "stapel":       ("FREMD", "Auf welchem Stapel der Gast laeuft. Wie `regs_gast` -- gedruckt statt geprueft. OFFEN: ob der Stapel wie der Raum an eine Deklaration gebunden werden sollte (`N006`)."),

    # -- ABSENKUNG: der Erzeuger ist ihr richtiger und einziger Leser ---------------------
    "endian":       ("ABSENKUNG", "Die Byteordnung ist eine Absenkungsaussage; emit ist ihr richtiger Leser."),
    "section":      ("ABSENKUNG", "Platzierung -- eine Aussage an den Binder, nicht an den Pruefer."),
    # **`reserviert` ROSE on 2026-08-28 and is therefore deleted here.** Its sentence booked
    # it as ABSENKUNG -- reserved bits, «B24» leaves the tiling to the generator -- and that
    # held as long as only `emit.rs` and `zeremonie.rs` touched the field. `lean.rs`:1011 reads
    # the clause LOAD-BEARINGLY: a reserved field gets NO shape (`None` instead of
    # `shape_of`), and every place naming it is refused rather than served. *That is not a
    # report any more, it is a refusal* -- and it stands on the pass surface, not at the
    # generator.
    "merge":        ("ABSENKUNG", "Die Verknuepfung ist durch den geschlossenen Wortschatz eingegrenzt; `Accumulates_Monoid.thy` deckt die Menge."),
    # **`bei_ueberschreitung` ist am 2026-08-19 AUFGESTIEGEN, und der Satz war FALSCH.**
    # Er lautete *„der Zweig ist Code, keine Zusage"* -- es IST eine Zusage: `on_exceeded`
    # muss eine Funktion nennen, die `never` liefert, und `emit.rs`:2310 hielt sie. Der
    # PRUEFER tat es nicht. `S006` seit heute. *Dieselbe Klasse wie «B24»: eine Regel, die
    # nur auf der Erzeugerflaeche stand.*
    "claim":        ("ABSENKUNG", "Der Anspruchstext eines `check` -- Prosa, die kein Pass widerlegen kann."),

    # -- TOT: das Bauteil ist gelesen und sonst nirgends ----------------------------------
    #
    # FUENF sind am 2026-08-19 AUFGESTIEGEN und darum hier geloescht: regs_in, regs_out,
    # preserves, clobbers, dispatch. Sie standen mit dem Satz *keine Datei ausserhalb des
    # Lesers nennt EntryDecl -- zwoelf Felder, ein Bauteil*. `N001` haelt jetzt die
    # Bindungen, `N017` preserves gegen clobbers, `N018` den dispatch.
    #
    # *Ausgeloest hat es `pruefe-konstrukte.py`, nicht die Hand -- `entry` war eines der
    # sieben Konstrukte ohne Giftprobe, und die Felder fielen als Nebenwirkung.*
    "by":           ("TOT", "Der Induktionshinweis. Nichts liest ihn -- und `Table_Induktion.thy` fuehrt genau ihn als Praemisse OHNE Erzeuger (`je Verkettungsfeld eine Kantenpraemisse`). Die beiden gehoeren zusammen."),
    "stack":        ("TOT", "siehe `regs_in` -- `EntryDecl`."),
    "vektor":       ("TOT", "siehe `regs_in` -- `EntryDecl`."),
    "ist":          ("TOT", "siehe `regs_in` -- `EntryDecl`."),
    "ab":           ("TOT", "`walk` ist gelesen und sonst nichts: kein Pass, kein Erzeuger kennt `WalkDecl`."),
    "ab_wenn":      ("TOT", "siehe `ab` -- `WalkDecl`."),
    "blatt":        ("TOT", "siehe `ab` -- `WalkDecl`."),
    # **`kosten` LOOKED risen on 2026-08-28 and was not** -- see `HOMONYME`.
    "kosten":       ("TOT", "Feld der `invariant`; ungelesen. (Nicht zu verwechseln mit `opsruf::Kopf.kosten` -- siehe HOMONYME.)"),
    "laeuft":       ("TOT", "Feld der `invariant`; ungelesen."),
    # **`erschoepfend` und `fehlername` sind am 2026-08-21 GESTIEGEN** (Stufe 7) -- und
    # dieser Waechter hat es gemeldet, bevor jemand daran gedacht hat, die Tabelle
    # nachzufuehren. *Das ist genau die Richtung, fuer die er gebaut wurde.*
    #
    # * `fehlername` -- der Binder eines `let … else` stand bis dahin in EINER Datei des
    #   Pruefers, naemlich im ERZEUGER: `HolFehler e; (void)e;`. Kein Pass wusste, dass der
    #   Name existiert, und `match e { … }` fiel mit `M119`. Jetzt traegt `e` den `reason`
    #   des Gerufenen (M1), und `M123` haelt die Fallunterscheidung darueber geschlossen.
    # * `erschoepfend` -- `SPRACHE.md`:531 sagt seit langem, was `exhaustive` heisst
    #   (*„der `switch` hat kein `default`, ein neuer Wert bricht die Uebersetzung"*), und
    #   keine Zeile tat es. `M125` und der `default`-lose `switch` sind zusammen sein
    #   erster Leser.
    "rueckgabe":    ("TOT", "Der Ergebnistyp eines `axiom` (G2); ungelesen."),
    "scale":        ("TOT", "`scale` an `embeds`; ungelesen."),
    "version":      ("TOT", "Die Formatversion; ungelesen."),
}

# **The DECIDED homonyms: a field name from `ast.rs` that a CHECKER-INTERNAL struct carries
# as well -- and the files in which the textual access belongs to the INTERNAL one.**
#
# Per entry: the files whose `.field` does NOT mean the AST clause · the internal struct · the
# reason. **Decided by hand, like the classes above** -- an attribution by type cannot be read
# off the text, and a tool that guessed it would be worse than one that lets it be booked.
#
# *The booking goes in the dangerous direction* -- it takes a reader away -- and therefore
# carries a ratchet of its own: the self-test below falls as soon as a booked file has no such
# access left. **An exception nobody needs any more looks exactly like one that reaches too
# far.**
HOMONYME = {
    "kosten": (
        {"opsruf.rs", "umgebung.rs"},
        "opsruf::Kopf",
        "`Kopf.kosten` ist die GEZAEHLTE Kostenzahl einer erzeugten Ops-Operation (`i128`, "
        "eine Op je Speicherung, die der Erzeuger schreibt); `Invariante.kosten` ist der "
        "`Expr` der `invariant`-Klausel. `opsruf.rs`:382 baut daraus die `deklariert`-Karte "
        "fuer `kosten.rs`, `umgebung.rs`:549 setzt `cost_bound` einer Signatur -- beide auf "
        "`opsruf::koepfe(t)`, keiner auf einer `Invariante`. **Keine der beiden Dateien nennt "
        "`Invariante` ueberhaupt.**",
    ),
}


def interne_felder():
    """**Feldnamen, die eine Struktur des PRUEFERS traegt** -- Name -> `datei::Struktur`.

    Der Textzugriff `.feld` kann sie nicht von einer Klausel unterscheiden. Gezaehlt werden
    sie, damit die Flaeche dieser Unschaerfe eine Zahl hat und nicht bloss einen Satz.
    """
    aus = {}
    dateien = sorted(PRUEFER.glob("*.rs")) + sorted((W / "crates/gabbro-cli/src").glob("*.rs"))
    for p in dateien:
        struktur = None
        for zeile in p.read_text(encoding="utf-8").splitlines():
            m = re.match(r"(?:pub(?:\([^)]*\))? )?struct (\w+)", zeile.strip())
            if m:
                struktur = m.group(1)
                continue
            if zeile.startswith("}"):
                struktur = None
                continue
            m = re.match(r"    (?:pub(?:\([^)]*\))? )?(\w+):", zeile)
            if m and struktur:
                aus.setdefault(m.group(1), set()).add(f"{p.name}::{struktur}")
    return aus


def stripp(zeile: str) -> str:
    """Kommentar und Zeichenkette weg -- ein Wort im Fliesstext ist kein Zugriff."""
    zeile = re.sub(r'"(?:[^"\\]|\\.)*"', '""', zeile)
    i = zeile.find("//")
    return zeile[:i] if i >= 0 else zeile


def felder():
    """Jedes `pub`-Feld jeder `pub struct` -- Name -> Strukturen."""
    aus = {}
    struktur = None
    for zeile in AST.read_text(encoding="utf-8").splitlines():
        m = re.match(r"pub struct (\w+)", zeile)
        if m:
            struktur = m.group(1)
            continue
        if zeile.startswith("}"):
            struktur = None
            continue
        m = re.match(r"    pub (\w+):", zeile)
        if m and struktur:
            aus.setdefault(m.group(1), []).append(struktur)
    return aus


def leser():
    """Datei -> Zeilen ohne Kommentar. Getrennt nach Lager."""
    aus = {}
    for p in sorted(PRUEFER.glob("*.rs")):
        aus[p.name] = [stripp(z) for z in p.read_text(encoding="utf-8").splitlines()]
    for p in sorted((W / "crates/gabbro-cli/src").glob("*.rs")):
        aus["cli/" + p.name] = [stripp(z) for z in p.read_text(encoding="utf-8").splitlines()]
    return aus


def ist_tragend(datei: str) -> bool:
    return datei.startswith("cli/") or datei in TRAGEND_DATEIEN


def zugriffe(feld: str, quellen):
    """Punktzugriffe je Datei -- `x.feld`. Die Paesse destrukturieren nicht (geprueft)."""
    muster = re.compile(r"\.%s\b" % re.escape(feld))
    aus = {}
    for datei, zeilen in quellen.items():
        treffer = [i + 1 for i, z in enumerate(zeilen) if muster.search(z)]
        if treffer:
            aus[datei] = treffer
    return aus


def ohne_homonyme(feld, z):
    """Die Zugriffe des Feldes, ohne die, die einer gleichnamigen INTERNEN Struktur gelten."""
    fremd = HOMONYME.get(feld, (frozenset(),))[0]
    return {d: s for d, s in z.items() if d not in fremd}


def selbsttest(quellen):
    """**R14: ein Messwerkzeug weist nach, dass es messen kann.**

    Drei Proben mit bekannter Antwort. Faellt eine, misst das Werkzeug nicht mehr, was es
    zu messen behauptet -- und dann ist Schweigen die falsche Ausgabe.
    """
    fehler = []
    span = zugriffe("span", quellen)
    if not any(not ist_tragend(d) for d in span):
        fehler.append("`span` muesste von einem Pass gelesen werden -- wird es nicht.")
    sect = zugriffe("section", quellen)
    if any(not ist_tragend(d) for d in sect):
        fehler.append("`section` gilt als von einem Pass gelesen -- die Probe ist stumpf.")
    # **And the third, since 2026-08-28: the homonym booking must BITE.**
    #
    # An exception that takes nothing away any more is indistinguishable from a missing one --
    # and it takes a reader away, hence the dangerous direction. So it is checked per booked
    # file that the access exists at all: once it is gone, the booking is blunt and belongs
    # deleted, not forgotten.
    for feld, (dateien, struktur, _grund) in sorted(HOMONYME.items()):
        z = zugriffe(feld, quellen)
        for d in sorted(dateien):
            if d not in z:
                fehler.append(
                    f"HOMONYM `{feld}` bucht `{d}` gegen `{struktur}` -- dort steht heute "
                    f"kein `.{feld}` mehr. Die Ausnahme ist stumpf und gehoert geloescht."
                )
        if not any(not ist_tragend(d) for d in dateien):
            fehler.append(
                f"HOMONYM `{feld}`: keine der gebuchten Dateien ist ein Pass -- die "
                f"Ausnahme aendert nichts und verschleiert nur."
            )
    return fehler


def main():
    quellen = leser()
    if fehler := selbsttest(quellen):
        print("ABBRUCH: der Selbsttest faellt -- es wurde NICHTS gemessen.")
        for f in fehler:
            print("  " + f)
        return 1

    alle = felder()
    getragen, ungelesen = {}, {}
    for feld, strukturen in sorted(alle.items()):
        z = ohne_homonyme(feld, zugriffe(feld, quellen))
        if any(not ist_tragend(d) for d in z):
            continue
        (getragen if z else ungelesen)[feld] = (strukturen, z)

    intern = interne_felder()
    doppelt = sorted(set(alle) & set(intern))

    print("== Klauselwaechter ==")
    print(f"   Quelle: {len(alle)} Feldnamen aus {AST.name}")
    print(f"   Leser:  {len(quellen)} Dateien, davon {sum(ist_tragend(d) for d in quellen)} tragend")
    print(f"   Davon MEHRDEUTIG: {len(doppelt)} Namen traegt auch eine prueferinterne")
    print(f"   Struktur -- ein `.feld` im Text ist dort nicht zuzuordnen. {len(HOMONYME)} "
          f"entschieden:")
    for feld, (dateien, struktur, _grund) in sorted(HOMONYME.items()):
        print(f"   {feld:<18} {struktur:<24} {', '.join(sorted(dateien))}")
    print()

    def zeige(titel, satz, menge):
        print(f"-- {titel}: {len(menge)} --")
        print(f"   {satz}")
        for feld, (strukturen, z) in sorted(menge.items()):
            wo = ", ".join(f"{d}:{','.join(map(str, s[:3]))}" for d, s in z.items())
            print(f"   {feld:<18} {'/'.join(strukturen):<34} {wo}")
        print()

    zeige("NUR GETRAGEN", "abgesenkt oder berichtet, von keinem Pass geprueft.", getragen)
    zeige("UNGELESEN", "der Leser fuellt sie, niemand sieht hin.", ungelesen)

    gefunden = set(getragen) | set(ungelesen)
    neu = sorted(gefunden - set(ERWARTET))
    weg = sorted(set(ERWARTET) - gefunden)
    if neu:
        print("== KLAUSELN: NEUE FUNDSTELLE ==")
        print("   Eine Klausel steht in der Grammatik und wird von keinem Pass gelesen,")
        print("   und sie steht in keiner Buchung. **Buchen oder lesen -- nicht schweigen.**")
        for f in neu:
            print(f"   {f}")
        return 1
    if weg:
        print("== KLAUSELN: DIE TABELLE IST VERALTET ==")
        print("   Diese Zeilen sind GESTIEGEN -- ein Pass liest sie jetzt. Eintrag loeschen.")
        for f in weg:
            print(f"   {f}")
        return 1
    klassen = {}
    for f in gefunden:
        klassen.setdefault(ERWARTET[f][0], []).append(f)
    print("-- Die Klassen. Die STUFE oben ist gemessen, die Klasse hier ist ein URTEIL. --")
    for k, satz in (
        ("ZUSAGE", "eine Aussage ueber Verhalten, die kein Pass haelt -- **die Klasse**"),
        ("FREMD", "beschreibt etwas AUSSERHALB der Einheit -- gedruckt statt geprueft"),
        ("ABSENKUNG", "der Erzeuger ist ihr richtiger und einziger Leser"),
        ("TOT", "das Bauteil ist gelesen und sonst nirgends"),
    ):
        print(f"   {k:<10} {len(klassen.get(k, [])):>3}   {satz}")
    print()
    print("-- Die ZUSAGEN einzeln, denn nur sie versprechen etwas --")
    for f in sorted(klassen.get("ZUSAGE", [])):
        print(f"   {f:<16} {ERWARTET[f][1]}")
    print()
    print(f"== KLAUSELN: {len(gefunden)} gebucht, keine neue ==")
    print("   Und was das NICHT heisst: gebucht ist nicht geprueft. Jede ZUSAGE-Zeile ist")
    print("   etwas, das die Grammatik zu sagen erlaubt und heute niemand nachhaelt.")
    # **The remaining blur, counted instead of claimed.** It only becomes expensive once the
    # REAL reader of an ambiguous clause disappears: the homonym would stay, and the case
    # would look like „read". *A sentence nobody counts is none.*
    unentschieden = sorted(set(doppelt) - set(HOMONYME))
    gilt_gelesen = [f for f in unentschieden if f not in gefunden]
    print(f"   **Und {len(unentschieden)} mehrdeutige Namen sind NICHT entschieden**, davon")
    print(f"   gelten {len(gilt_gelesen)} als von einem Pass gelesen. OB ZU RECHT, sagt dieses")
    print("   Werkzeug nicht (W10) -- es sieht den Text, nicht den Typ des Empfaengers.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
