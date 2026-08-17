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

# Je Luecke: (Kennung, was fehlte, das kleinste Programm, das es braucht)
LUECKEN = [
    ("B3", "`Held(Lock)` -- eine Typliste in den Klammern eines `typedecl`",
     "module t { linear ghost type Held(Lock); }"),
    ("B6", "eine Bindung fuer den Rueckgabewert in `ensures`",
     "module t { impl fn f(s : u32) -> u32 ensures result <= s effects { pure } "
     "costs <= 2 ops { return s; } }"),
    ("B7", "ein Verbundliteral -- eine Funktion kann einen `structty` HERSTELLEN",
     "module t { type P = { a : u32, }; impl fn f() -> P effects { pure } costs <= 2 ops "
     "{ return P { a: 1 }; } }"),
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
     "check c { claim \"erste\" \"zweite\" measures n gates g\n"
     "  can_fail { if e() != 0 { return false; } return true; } floor n >= 1 } }"),
    ("B25", "eine Wertemenge statt eines Intervalls",
     "module t { type G = u8 in 0x01 .. 0x0c; }"),
]


def main():
    offen, zu = [], []
    with tempfile.TemporaryDirectory() as d:
        pfad = pathlib.Path(d) / "probe.gab"
        for kennung, was, quelle in LUECKEN:
            pfad.write_text(quelle, encoding="utf-8")
            r = subprocess.run(
                ["cargo", "run", "-q", "--manifest-path", str(W / "Cargo.toml"),
                 "--bin", "gabbro", "--", "pruefe", str(pfad)],
                capture_output=True, text=True,
            )
            # **Ein Bauabbruch ist kein geschlossener Befund.** Ohne diese Zeile zaehlte ein
            # kaputter Baum jede Luecke als zu -- und der Waechter meldete Erfolg (W1).
            if "error[E" in r.stderr or "could not compile" in r.stderr:
                print("ABBRUCH: der Pruefer baut nicht -- es wurde NICHTS gemessen.",
                      file=sys.stderr)
                sys.exit(1)
            fehler = [z for z in r.stdout.splitlines() if z.startswith("Fehler")]
            (zu if not fehler else offen).append((kennung, was, fehler[:1]))

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
    return 0


if __name__ == "__main__":
    sys.exit(main())
