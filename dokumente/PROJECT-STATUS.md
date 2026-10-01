# Project status — provenance behind the README snapshot

The README front page is a measured snapshot, not a ledger: compact guarded
figures with their commands, dated on the day they were taken. This page holds
what does not fit there — what counts as evidence, where the records live, and
what is known to be open. It carries no second copy of the live numeric
ledger; where numbers appear below they are stable identifiers (tags, dates,
section references), never re-typed measurements.

## What counts as evidence

- **Proved in Lean** means a machine-checked theorem with standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`), a non-degenerate witness
  where the rules require one, and no `sorry`, `admit`, `axiom` or
  `native_decide`. The goal theorem `gabbro_ziel` meets this; six review rounds
  are recorded in `dokumente/SATZKARTE.md` §§22–§25 under the milestone tags
  `milestone-2026-09-15-gabbro-ziel` (proved) and
  `milestone-2026-09-15-zielsatz-bestaetigt` (confirmed).
- **Measured** means an instrument ran and printed the figure beside its
  verdict — guardian count, corpus files, grammar rules, template register,
  blind-spot pairs, ceremony sites. Every README figure names its command;
  re-run it to check.
- **Argued / conjectured** are labels of the pass register itself
  (`messung/PASSREGISTER.md`, held by `instrumente/pruefe-saetze.py`): a
  written sentence is not a proved one. Poison probes and caught mutations
  measure the implementation on checked cases, never the rule.
- **Open** means stated as work with an owner and a gate: `TODO.md` (open
  items only), `dokumente/OFFEN.md` (known absences), and the direct-compiler
  record below.

## Registers and records

- Goal statement and its one assumption / NOT-CLAIMED list:
  `grammatik/Grammatik/Zielsatz/Spec.lean` (proof `Zielsatz/BeweisAtomar.lean`,
  single-concurrency statement derived in `Zielsatz/Beweis.lean`).
- Certificate register: `grammatik/Grammatik/Zertifikat/REGISTER.txt` — every
  accepted program is either certified or listed by name as not claimed.
- Direct x86-64 compiler, the central progress record:
  `DIRECT-COMPILER.md`, with `DIRECT-COMPILER-DESIGN.md`,
  `grammatik/OPTIMIZER.md` and `dokumente/x86/TARGET-PORTABILITY.md` as the
  design companions. Proved, running, refused and planned work are kept
  distinct there; Lean X86 helper modules live under
  `grammatik/Grammatik/X86/`.
- Duty bridge: `bruecke/Bruecke/Quelle.lean`, `messung/GABBROV-BRUECKE-REPORT.md`.
- Guardians: `instrumente/abnahme.py` runs every guardian; each carries a
  deadline, a two-way speech test, a red abort and a pinned locale.
- History of measurements: `dokumente/MESSUNGEN.md`. Build and test timings
  are recorded there with their dates; the front page carries none, so a
  cold-cache number cannot pose as a property of the project.

## Translation chain

The C-backend evidence the front page does not print: one generic closing
theorem (`schlusssatz`, source text → model → emitted C) with Lean-checked
instances for five programs — 104 and 108 by hand, 130, 69 and 73 through the
generic chain — plus a concurrent stage-b instance for one program (124) under
its named premises. Scope is instrument-measured, not claimed:
`instrumente/zaehle-kette.py --lean` prints the closed count beside each
program's sieve verdict (5 of 157 CLOSED on 2026-10-01; the `Spec.lean`
header records earlier counts with their dates). None of this certifies x86
binaries; the direct-backend chain is open (see `DIRECT-COMPILER.md`).

## Known limits, as pointers

- The checker inside the goal theorem is the Lean Bool `Akzeptiert`, not the
  Rust checker; the Rust-to-Lean and Lean-to-binary bridges are translation
  validation, and the x86 leg is open
  (`dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md` §§0–5).
- The three standard axioms validate the proof, not the statement; the
  theorem's premises (checked program, user logic, named hardware assumptions,
  runtime) are owed every time and listed in the `Spec.lean` header.
- Linking of separately compiled units has its own second statement
  (`GabbroZielVerbund`); probabilistic statements and unbounded regions stay
  outside the statement (`dokumente/OFFEN.md` O28, O29).
- Caprock fragments, with origin and verdict: `dokumente/FRAGMENTE.md`.
