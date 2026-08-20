#!/usr/bin/env python3
"""**Die Notationsluecken gegen die HEUTIGE Grammatik, nicht gegen den eingefrorenen Text.**

`PFLICHTEN.md` fuehrte am 2026-08-17 sieben Notationsluecken als haengende
Klempnereipflichten. Sie stammten aus `FRAGMENTE.md`, und diese Datei traegt ihren eigenen
Einfriersatz: *„ein Bericht vom 2026-08-14, und er bleibt unangetastet."*

**Fuenf der sieben waren zu diesem Zeitpunkt bereits geschlossen.** Die Grammatik ist
weitergegangen, der Befundtext nicht -- und die Messung hat den Befundtext gelesen.

> *Das ist dieselbe Klasse wie die 89 Verschluesse ohne Suchweg:* eine Zahl, die aus einem
> Dokument stammt statt aus dem Gegenstand. **Der Unterschied ist, dass sie diesmal zu GROSS
> war** -- der Ordner hat sich schlechter gerechnet, als er ist.

Dieses Werkzeug liest den Gegenstand. Es schreibt je Luecke ein winziges Programm und fragt
den Pruefer, ob es durchgeht.

    ./pruefe-notation.py
"""
import pathlib
import subprocess
import sys
import tempfile

W = pathlib.Path(__file__).resolve().parent

# **Jede Ausfuehrung mit Frist.** Ein Haenger sieht aus wie „laeuft noch", nicht wie
# ein Befund -- am 2026-08-20 standen deswegen einundzwanzig Laeufe von
# `pruefe-emission.sh` nebeneinander, der aelteste seit dreieinhalb Stunden.
FRIST = 600

# Je Luecke: (Kennung, was fehlte, das kleinste Programm, das es braucht)
LUECKEN = [
    ("B3", "`Held(Lock)` -- eine Typliste in den Klammern eines `typedecl`",
     "module t { linear ghost type Held(Lock); }"),
    ("B6", "eine Bindung fuer den Rueckgabewert in `ensures`",
     "module t { impl fn f(s : u32) -> u32 ensures result <= s effects { pure } "
     "costs <= 2 ops { return s; } }"),
    ("B7", "ein Verbundwert -- eine Funktion kann einen `structty` HERSTELLEN",
     "module t { type P = { a : u32, b : bool, }; impl fn f() -> P effects { pure } "
     "costs <= 4 ops { return P(a: 1, b: true); } }"),
    ("B14a", "`option` in `typeexpr`, nicht nur in `slottype`",
     "module t { type A = option index into T; table T count 8 { slot { a : bool, } } }"),
    ("B14b", "`let … else` auf einem `place` (ein Atomic ist ein `place`)",
     "module t { atomic g : u32 publishes nothing relaxed;\n"
     "impl fn f() -> bool effects { reads g } costs <= 4 ops "
     "{ let x = g else (e) { return false; } return true; } }"),
    ("B21", "`accumulates max/min/+` -- die Wasserstandsmarke",
     "module t { accumulates hoch : u64 merge max; }"),
    ("B22", "ein mehrzeiliges `claim`",
     "module t { extern fn e() -> u32 effects { pure } costs <= 2 ops;\n"
     "check c { claim \"erste\" \"zweite\" measures n gates e\n"
     "  can_fail { if e() != 0 { return false; } return true; } floor n >= 1 } }"),
    ("B25", "eine Wertemenge statt eines Intervalls",
     "module t { type G = u8 in 0x01 .. 0x0c; }"),
]

# **Die andere Haelfte, und ohne sie waere die erste wertlos.**
#
# Eine Luecke laesst sich immer schliessen, indem man die Form einfach zulaesst. Was «B7»
# gekostet hat, war die ENTSCHEIDUNG dagegen: kein geschweiftes Verbundliteral, weil es die
# erste Ausdrucksform waere, die mit `{` weitergeht -- und weil der Fehlerfall eines
# Kontextschalters STILL ist (76 Korpusstellen, die weiter parsen, nur anders).
#
# > *Eine Entscheidung, die kein Waechter kennt, ist eine Meinung.* Deshalb steht hier je
# > Form der Absagecode, den sie ausloesen MUSS. Wer die Form spaeter doch einbaut, faellt
# > hier auf -- und nicht erst daran, dass 76 Stellen anders gelesen werden.
#
# Je Eintrag: (Kennung, die Form, der geforderte Code, was der Code sagt)
ABSAGEN = [
    ("B7", "`P { a: 1 }` -- das geschweifte Verbundliteral", "P037",
     "module t { type P = { a : u32, }; impl fn f() -> P effects { pure } costs <= 2 ops "
     "{ return P { a: 1 }; } }"),
    ("B7", "`P(1)` -- der Verbund ohne seine Feldnamen", "M107",
     "module t { type P = { a : u32, b : u32, }; impl fn f() -> P effects { pure } "
     "costs <= 4 ops { return P(1, 2); } }"),
    ("B7", "`P(b: …, a: …)` -- die Felder in der falschen Reihenfolge", "M106",
     "module t { type P = { a : u32, b : bool, }; impl fn f() -> P effects { pure } "
     "costs <= 4 ops { return P(b: true, a: 1); } }"),
    ("B7", "`P(a: 1)` -- ein Feld ausgelassen", "M106",
     "module t { type P = { a : u32, b : bool, }; impl fn f() -> P effects { pure } "
     "costs <= 4 ops { return P(a: 1); } }"),
    ("B7", "`f(x: 1)` -- eine Marke an einer gewoehnlichen Funktion", "M107",
     "module t { impl fn g(x : u32) -> u32 effects { pure } costs <= 2 ops { return x; } "
     "impl fn f() -> u32 effects { pure } costs <= 4 ops { return g(x: 1); } }"),
    ("B7", "`P(a: 1, 2)` -- halb markiert", "P036",
     "module t { type P = { a : u32, b : u32, }; impl fn f() -> P effects { pure } "
     "costs <= 4 ops { return P(a: 1, 2); } }"),
]


def lauf(pfad, quelle):
    """Ein Programm durch den Pruefer, mit dem Bauabbruch als ABBRUCH statt als Ergebnis."""
    pfad.write_text(quelle, encoding="utf-8")
    r = subprocess.run(
        ["cargo", "run", "-q", "--manifest-path", str(W / "Cargo.toml"),
         "--bin", "gabbro", "--", "pruefe", str(pfad)],
        capture_output=True, text=True, timeout=FRIST)
    # **Ein Bauabbruch ist kein geschlossener Befund.** Ohne diese Zeile zaehlte ein
    # kaputter Baum jede Luecke als zu -- und der Waechter meldete Erfolg (W1).
    if "error[E" in r.stderr or "could not compile" in r.stderr:
        print("ABBRUCH: der Pruefer baut nicht -- es wurde NICHTS gemessen.", file=sys.stderr)
        sys.exit(1)
    return [z for z in r.stdout.splitlines() if z.startswith("Fehler")]


def main():
    offen, zu, stumm = [], [], []
    with tempfile.TemporaryDirectory() as d:
        pfad = pathlib.Path(d) / "probe.gab"
        for kennung, was, quelle in LUECKEN:
            fehler = lauf(pfad, quelle)
            (zu if not fehler else offen).append((kennung, was, fehler[:1]))
        # **Die Gegenprobe: hier ist eine Absage das Bestehen.**
        for kennung, was, code, quelle in ABSAGEN:
            fehler = lauf(pfad, quelle)
            getroffen = any(f"[{code}]" in z for z in fehler)
            if not getroffen:
                stumm.append((kennung, was, code, fehler[:1]))

    print("== Notationsluecken gegen die HEUTIGE Grammatik ==")
    for k, was, _ in zu:
        print(f"  ZU     {k:<5} {was}")
    for k, was, f in offen:
        print(f"  OFFEN  {k:<5} {was}")
        for z in f:
            print(f"           {z[:96]}")
    print(f"\n== {len(zu)} von {len(LUECKEN)} geschlossen ==")
    if offen:
        print("  Die offenen sind BAUARBEIT. Die geschlossenen standen in `FRAGMENTE.md`")
        print("  weiterhin als Befund -- die Datei ist eingefroren, die Grammatik nicht.")
        print("  **Eine Messung, die den Befundtext liest statt den Gegenstand, misst das")
        print("  Dokument.** Genau darum laeuft dieses Werkzeug gegen den Pruefer.")

    print(f"\n== Gegenprobe: {len(ABSAGEN) - len(stumm)} von {len(ABSAGEN)} Formen "
          f"abgesagt, wie entschieden ==")
    if stumm:
        print("  **STILL DURCHGELASSEN -- und still ist hier der ganze Punkt:**")
        for k, was, code, f in stumm:
            print(f"  FEHLT  {k:<5} {was}  (erwartet {code})")
            for z in f:
                print(f"           statt dessen: {z[:88]}")
        print("  Eine Form, die die Entscheidung verbietet und die trotzdem durchgeht,")
        print("  faellt in keinem anderen Tor auf. Genau dafuer steht dieser Abschnitt.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
