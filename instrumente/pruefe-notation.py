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

    ./instrumente/pruefe-notation.py
"""
import pathlib
import re
import subprocess
import sys
import tempfile

W = pathlib.Path(__file__).resolve().parent.parent

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


# **The blind spot of this tool, and it hid the largest gap of all** (2026-09-04).
# ------------------------------------------------------------------------------
# Everything above asks `gabbro pruefe`. That finds only the gaps the CHECKER refuses --
# and a notation gap can sit one stage further on: the form parses, every pass accepts it,
# and the EMITTER refuses it by name because what it would emit is a different program.
#
# **«B10» is exactly that, and it was invisible here.** Measured:
#
#     gabbro pruefe p-queue.gab   ->  5 items, 0 errors, 0 hints
#     gabbro emit   p-queue.gab   ->  [C001] no lowering: `queue` -- «B10»: `traverse`
#                                     yields no value and knows no `break` …
#
# A register that only asks the checker reports such a gap as CLOSED. *That is the same
# class as the finding this file was built for* -- a measurement that reads the wrong
# organ -- one stage downstream.
#
# **And the entry is what makes `H` derivable.** `zaehle-pflichten.py::absenkungsklasse`
# splits the lowering column into plumbing and notation on the rule *"does `gabbro pruefe`
# accept the text?"*; `F03`'s share lands in notation, and **this** is where the gap it
# lands in is held against the object rather than against a frozen finding text.
#
# The entry is two-sided by construction:
#
#   * the probe must CHECK CLEAN -- otherwise it is not a notation gap of this kind at all,
#     and the run refuses rather than booking it;
#   * the emitter must refuse it with the NAMED text. Build the arm and the entry moves to
#     `ZU` by itself; change the text and this guard says so.
#
# Per entry: (mark, the form, the program, the text the refusal MUST carry)
ABSENKUNGSLUECKEN = [
    ("B10", "the value-yielding, leavable search loop -- `traverse … over queue … "
            "by consuming` drains the WHOLE queue",
     "module t {\n"
     "type Ring = { buf : [u32; 32], kopf : u32, zahl : u32, };\n"
     "impl fn leeren(r : ptr<normal, rw> Ring) effects { reads r, writes r, consumes r } "
     "costs <= 200 ops {\n"
     "  traverse j over queue r by consuming touches consumes r, reads r, writes r "
     "{ r.buf[j] = 0; }\n"
     "} }",
     "no lowering: `queue`"),
]


SPRACH = re.compile(r"\b\d+ items, \d+ errors, \d+ hints\b")


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
        sys.exit(2)
    # **And the same trap one step to the side, measured 2026-08-31.** The two strings above
    # catch a COMPILE error and nothing else. Over a tree without a `Cargo.toml`, `cargo`
    # says `error: manifest path ... does not exist` -- neither string matches, `r.stdout` is
    # empty, every gap counts as CLOSED and every refusal as SILENT. *The guardian then
    # reported findings out of a run that never happened.*
    #
    # So the latch does not enumerate failures any more, it demands a POSITIVE sign of life:
    # `gabbro pruefe` always prints `N items, M errors, K hints`, with errors and without.
    # **A checker that did not say that sentence did not check.**
    if not SPRACH.search(r.stdout):
        print("ABBRUCH: der Pruefer hat nicht geantwortet -- keine Zeile "
              "`N items, M errors, K hints`.", file=sys.stderr)
        print("  Es wurde NICHTS gemessen; ohne den Lauf zaehlt jede Luecke als zu.",
              file=sys.stderr)
        print((r.stderr or r.stdout or "").strip()[:400], file=sys.stderr)
        sys.exit(2)
    return [z for z in r.stdout.splitlines() if z.startswith("error")]


def lauf_emit(pfad, quelle):
    """Dasselbe Programm durch den ERZEUGER -- fuer Luecken, die der Pruefer durchlaesst.

    Gibt die Fehlerzeilen von `gabbro emit` zurueck. Derselbe Riegel wie oben: ein Baumfehler
    ist kein Befund, und ein Lauf ohne Lebenszeichen zaehlt nicht als Erfolg.
    """
    pfad.write_text(quelle, encoding="utf-8")
    r = subprocess.run(
        ["cargo", "run", "-q", "--manifest-path", str(W / "Cargo.toml"),
         "--bin", "gabbro", "--", "emit", str(pfad)],
        capture_output=True, text=True, timeout=FRIST)
    if "error[E" in r.stderr or "could not compile" in r.stderr:
        print("ABBRUCH: der Erzeuger baut nicht -- es wurde NICHTS gemessen.", file=sys.stderr)
        sys.exit(2)
    zeilen = [z for z in (r.stdout + r.stderr).splitlines() if z.startswith("error")]
    # On success `emit` writes C to stdout; on failure it says `has errors`. If
    # neither arrives, nothing ran -- and then an empty error list is not a
    # closed finding but an unmeasured one.
    if not zeilen and "Generated by Gabbro" not in r.stdout:
        print("ABBRUCH: der Erzeuger hat weder C noch eine Absage geliefert -- es wurde "
              "NICHTS gemessen.", file=sys.stderr)
        print((r.stderr or r.stdout or "").strip()[:400], file=sys.stderr)
        sys.exit(2)
    return zeilen


def main():
    offen, zu, stumm, absenkung = [], [], [], []
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
        # **The gaps ONE STAGE FURTHER ON: the checker accepts, the emitter refuses.**
        for kennung, was, quelle, text in ABSENKUNGSLUECKEN:
            vorlauf = lauf(pfad, quelle)
            if vorlauf:
                # **The entry's precondition is gone, and that is a `2`.** What the
                # checker refuses is not a lowering gap -- then this probe has not
                # measured its subject, neither yes nor no. *A `1` would be a finding
                # about the tree; here the YARDSTICK is broken and not the tree.*
                print(f"ABBRUCH: die Absenkungsprobe «{kennung}» wird schon vom PRUEFER "
                      f"abgewiesen -- {vorlauf[0][:90]}", file=sys.stderr)
                print("  Damit misst sie keine Absenkungsluecke mehr, sondern eine "
                      "gewoehnliche. Es wurde NICHTS gemessen.", file=sys.stderr)
                sys.exit(2)
            fehler = lauf_emit(pfad, quelle)
            absenkung.append((kennung, was, any(text in z for z in fehler), fehler[:1]))

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

    # **And the finding no longer sits AT THE EXIT** (2026-09-04). Until today the
    # counterprobe ended with `return 1`, and while it was the last table that cost
    # nothing. With the third table below it, it costs exactly what this folder has a
    # rule against: *a measurement that stops at the first hit measures the wrong
    # question.* A silent counterprobe would have left the lowering gaps unprinted --
    # **a finding hiding behind another one** -- and `pruefe-waechter.py` reported the
    # place as an open partial measurement before anyone read it.
    #
    # The third table: gaps the CHECKER does not see.
    #
    # They are the reason `H` is counted split since today: a lowering the emitter
    # refuses by name is not missing generator work if what it WOULD emit is a
    # different program. *Then there is no arm to write.*
    offen_ab = [e for e in absenkung if e[2]]
    print(f"\n== Absenkungsluecken: {len(offen_ab)} von {len(ABSENKUNGSLUECKEN)} stehen "
          f"noch -- der Pruefer nimmt an, der Erzeuger sagt ab ==")
    for k, was, getroffen, f in absenkung:
        if getroffen:
            print(f"  OFFEN  {k:<5} {was}")
            for z in f:
                print(f"           {z[:96]}")
        else:
            print(f"  ZU     {k:<5} {was}")
            print(f"           der Erzeuger fuehrt die genannte Absage NICHT mehr -- "
                  f"entweder ist der Zweig gebaut")
            print(f"           oder der Text hat sich bewegt. **Beides gehoert gebucht, "
                  f"und `zaehle-pflichten.py`")
            print(f"           zaehlt die Datei dann wieder in `H`.**")
    return 1 if stumm else 0


if __name__ == "__main__":
    sys.exit(main())
