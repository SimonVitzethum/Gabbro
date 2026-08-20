#!/usr/bin/env python3
"""**Die Klasse eine Ebene hoeher: ein KONSTRUKT ohne Erzeuger.**

`pruefe-klauseln.py` haelt jedes `pub`-Feld gegen seine Leser und hat damit die Klasse
*deklariert, exportiert, nie gelesen* gefunden -- 48 Fundstellen statt der erwarteten vier.

**Dasselbe Muster gibt es eine Ebene darueber, und es ist teurer:** nicht ein Feld ohne Leser,
sondern ein **Item der Grammatik ohne Wirkung**. Zwei Fundstellen standen am 2026-08-19 fest:

    ops     Grammatik vollstaendig, Wortmenge im Lexer, KEIN Erzeuger
            -- und traegt die K-Spalte: 28 von 73 Pflichten
    check   Grammatik vollstaendig, vier Uebersetzungsfehler versprochen, KEINER existiert
            -- die `linear ghost Duty(check)` wird nirgends erzeugt

*Beide tragen Zusagen, die anderswo bereits als getragen gebucht sind.* Das ist die fuenfte und
sechste Instanz derselben Klasse -- und wie beim Feldskript ist zu erwarten, dass die
mechanische Zaehlung mehr findet als die Hand.

**`check` ist am 2026-08-19 gefallen, und der Weg war ein anderer als hier angenommen.** Der
Eintrag sagte *„eine Probe waere sinnlos, solange die Ursache steht: sie fiele an nichts --
erst der Erzeuger, dann die Probe."* Die `Duty` wird weiterhin nirgends erzeugt. Was fiel, sind
die vier versprochenen Fehler auf einem ANDEREN Weg: zwei stehen laengst im Parser (die
Grammatik macht `gates` und `can_fail` pflichtig), die anderen zwei sind `N021`/`N022`, und
`N020` fragt, ob `gates` ueberhaupt jemanden nennt. *Die Ursache war nicht die Bedingung fuer
die Wirkung, fuer die ich sie gehalten habe.*

DAS MASS
--------
Quelle ist mechanisch: **jede Variante von `ItemArt` in `ast.rs`** -- die ganze Menge dessen,
was ein Programm sein kann. Dagegen gehalten: greift irgendein Pass oder der Erzeuger sie an?

    gelesen        ein Pass ODER der Erzeuger nennt `ItemArt::X`
    nur getragen   nur `emit.rs`/`zeugnis.rs` -- abgesenkt, nicht geprueft
    ungelesen      niemand                                        -- **die Klasse**

> **Die Vergroeberung geht in die sichere Richtung.** *Genannt* heisst nicht *geprueft*: `ops`
> steht in `kbedingung.rs` (`D001` verbietet Handmutation daneben) und faellt hier trotzdem
> nicht auf, weil ein Pass es anfasst. **Der Waechter verpflichtet, er spricht nicht frei** --
> was er nennt, ist echt; was er nicht nennt, kann trotzdem wirkungslos sein (W10).

    ./instrumente/pruefe-konstrukte.py
"""
import pathlib
import re
import sys

W = pathlib.Path(__file__).resolve().parent.parent
AST = W / "crates/gabbro-syntax/src/ast.rs"
PRUEFER = W / "crates/gabbro-check/src"
TRAGEND = {"emit.rs", "zeugnis.rs"}

# **Die bekannten Fundstellen, je mit dem Satz, warum sie offen sind.** Wie beim Feldwaechter
# ist ein Eintrag keine Ausnahme, sondern eine Buchung -- und die Ratsche klemmt in beide
# Richtungen: eine Zeile, die STEIGT, laesst dieses Werkzeug ebenfalls anschlagen.
OHNE_PROBE = {
    # **Sechs sind am 2026-08-19 gefallen** -- `axiom`, `boot`, `entry`, `reason`, `state`,
    # `walk` -- und vier davon durch eine Regel, die am ZWILLING schon stand: `walk` gegen
    # `table` (doppelte Invariante), `state` gegen `device` (doppelter Uebergang), `entry`
    # gegen beide (doppelte Bindung), `dispatch` gegen gar nichts.
    #
    # *Dieselbe Regel an einem Konstrukt und am Zwilling nicht -- das ist die Form, die Mass 2
    # sichtbar macht und Mass 1 nicht.*
}

# Nur getragen: von emit/zeugnis angefasst, von keinem Pass.
NUR_GETRAGEN = {
    "Entry": "nur im Zeugnis",
    "Boot": "nur im Zeugnis",
}


def varianten():
    t = AST.read_text()
    m = re.search(r"pub enum ItemArt \{(.*?)\n\}", t, re.S)
    return [x for x in re.findall(r"^\s*([A-Z]\w*)\(", m.group(1), re.M)]


def schluesselwoerter():
    """Variante -> Schluesselwort, aus `ast.rs` selbst und nicht von Hand."""
    t = AST.read_text()
    return dict(re.findall(r'ItemArt::(\w+)\(_\) => "([a-z]+)"', t))


def leser():
    pass_, tragend = {}, {}
    for f in sorted(PRUEFER.glob("*.rs")):
        t = f.read_text()
        ziel = tragend if f.name in TRAGEND else pass_
        for v in re.findall(r"ItemArt::(\w+)", t):
            ziel.setdefault(v, set()).add(f.name)
    return pass_, tragend


def proben(wort):
    """Wieviele Giftproben DEKLARIEREN dieses Konstrukt?"""
    n = 0
    for f in (W / "beispiele" / "gift").glob("*.gab"):
        if re.search(r"^\s*%s\s" % re.escape(wort), f.read_text(), re.M):
            n += 1
    return n


def sprechprobe():
    """**R14: ein Messwerkzeug weist nach, dass es messen kann** -- in beide Richtungen.

    Bis zum 2026-08-20 hatte dieser Waechter keine; gefunden von `pruefe-waechter.py` beim
    ersten Lauf. Das ist doppelt bitter, weil er selbst Mass 2 nur zaehlt und im eigenen
    Schlusssatz sagt, dass eine Probe zu haben nicht heisst, geprueft zu sein.
    """
    fehler = []
    if proben("zzsprechprobe") != 0:
        fehler.append("ein erfundenes Konstrukt hat angeblich Giftproben -- die Suche trifft "
                      "irgendetwas, nicht das Wort")
    if proben("module") == 0:
        fehler.append("`module` hat angeblich keine Giftprobe -- die Suche findet nichts mehr, "
                      "und dann sagt jede Null hier nichts")
    vs = varianten()
    if not vs:
        fehler.append("`ast.rs` liefert null Item-Arten -- es wurde NICHTS gemessen")
    return fehler


def main():
    if fehler := sprechprobe():
        print("ABBRUCH: die Sprechprobe faellt -- es wurde NICHTS gemessen.")
        for f in fehler:
            print("  " + f)
        return 1
    print("== Sprechprobe: ok (ein erfundenes Konstrukt hat 0 Proben, `module` hat welche) ==\n")

    vs = varianten()
    woerter = schluesselwoerter()
    pass_, tragend = leser()

    # -- Mass 1: greift ein Pass die Item-Art an? ---------------------------------------
    getragen = [v for v in vs if v not in pass_ and v in tragend]
    ungelesen = [v for v in vs if v not in pass_ and v not in tragend]
    print("== Konstrukte: %d Item-Arten in `ast.rs` ==" % len(vs))
    print("\n-- Mass 1: greift ein PASS die Item-Art an? --")
    print("   gelesen        %2d" % (len(vs) - len(getragen) - len(ungelesen)))
    print("   nur getragen   %2d   nur emit/zeugnis" % len(getragen))
    print("   ungelesen      %2d" % len(ungelesen))
    for v in getragen:
        print("     getragen  %-10s %s" % (v, ", ".join(sorted(tragend[v]))))

    # -- Mass 2: hat je eine GIFTPROBE an diesem Konstrukt etwas fallen lassen? ----------
    #
    # **Mass 1 ist zu grob, und das ist selbst der Befund.** `ItemArt::Check` wird von
    # `schleifen.rs` angefasst -- aber nur, um in `can_fail` hineinzulaufen; keine der vier
    # versprochenen Zusagen wird geprueft. `ops` steht als `!t.ops.is_empty()` da, also als
    # BOOLESCHE Frage, nie als Menge. *Ein Konstrukt kann beruehrt werden, ohne dass eine
    # einzige seiner Zusagen faellt.*
    #
    # Das schaerfere Mass fragt nicht, wer es liest, sondern **ob je etwas daran gefallen
    # ist**: gibt es eine Giftprobe, die dieses Konstrukt deklariert?
    print("\n-- Mass 2: gibt es eine GIFTPROBE, die das Konstrukt deklariert? --")
    ohne = []
    for v in vs:
        w = woerter.get(v)
        if not w:
            continue
        if proben(w) == 0:
            ohne.append(w)
    for w in sorted(ohne):
        print("     OHNE PROBE  %-12s %s" % (w, OHNE_PROBE.get(w, "")))
    print("   %d von %d Konstrukten haben KEINE Giftprobe" % (len(ohne), len(woerter)))

    neu = [w for w in ohne if w not in OHNE_PROBE]
    weg = [w for w in OHNE_PROBE if w not in ohne]
    if neu:
        print("\n== KONSTRUKTE: %d NEUE ohne Probe ==" % len(neu))
        print("   " + ", ".join(sorted(neu)))
        return 1
    if weg:
        print("\n== KONSTRUKTE: DIE TABELLE IST VERALTET ==")
        print("   Diese haben jetzt eine Probe. Eintrag loeschen: " + ", ".join(sorted(weg)))
        return 1
    print("\n== KONSTRUKTE: %d ohne Probe gebucht, keine neue ==" % len(OHNE_PROBE))
    print("   Und was das NICHT heisst: eine Probe zu haben ist nicht, geprueft zu sein.")
    print("   `ops` hat drei und trotzdem keinen Erzeuger -- die Proben fallen an `D001`,")
    print("   nicht an der Erhaltung. Der Waechter verpflichtet, er spricht nicht frei (W10).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
