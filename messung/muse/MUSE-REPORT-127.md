# MUSE-REPORT-127

Lane 127, fifth parallel wave. Analysis lane: estimate the formal
verification effort for Gabbro itself. No Lean/Rust code changes.

## What I did

- Read `dokumente/SATZKARTE.md` (§§7–10: 11 open items D1–D9/D11–D12),
  `dokumente/BEWEIS.md` (proof architecture, C-form census: 64 forms, 30
  undecided), `dokumente/PLAN-VERIFIKATION.md` (translation validation,
  witness pairs), `dokumente/PLAN-UMSETZUNG.md` (derivation print, U1–U8),
  `dokumente/PLAN-SYSCALL.md`, `dokumente/PLAN-BITS.md`,
  `dokumente/PLAN-ERWEITUNG.md`.
- Measured with `wc -l` and `git log --numstat`: Rust ≈ 88,600 lines
  (gabbro-check 76,250 incl. emit.rs 14,415; syntax 8,861; cli 3,523);
  Lean `grammatik/` 53,076 lines / 1,552 theorems; `programmlogik/`
  10,066; Isabelle `beweise/` 3,512 lines / 24 theorems.
- Velocity: human era +12,700 net Lean lines over ~25 active days
  (≈ 500/day); agent waves +44,100 net over 3 days (≈ 200–400 net per
  lane-day).
- Wrote `messung/VERIFIKATIONSAUFWAND-2026-09-12.md` (English): tables per
  §1–§4 of the task plus the one-paragraph bottom line.

## Exact names of new definitions/theorems

None. Analysis lane — no Lean definitions or theorems added, no `Grammatik.lean` change.

## Last `./lean-bau` result line

Not run: no Lean files touched, so no build impact. (`git status` shows
only the two new report files.)

## What remains open

Nothing in this lane except review of the estimate. Corroboration a
follow-up lane could do cheaply: re-run the measurement commands in §1.1
of the report; check the CompCert/seL4/CakeML/Vellvm ratios against
literature (mine are from memory, flagged as such); verify the "30
undecided C forms" count against `instrumente/zaehle-c-formen.py`.

## What I believe is wrong in the task

Two points, both minor:

1. The task's "+30% growth" is applied to my code baseline, but the
   dominant cost driver of strategy B (the C-subset semantics,
   ~10–20k new lines) scales with the *emitted* language, not the Rust
   codebase — growth in checker features barely moves it, while one new
   C form moves it a lot.
2. The task asks for "the project's OWN ratio (Lean lines per checked
   feature)". What I could measure is Lean lines per *modelled* feature
   (~300–600 lines per lane-task, ~34 lines/theorem) — the project has
   never verified a checker feature, so a true own verification ratio
   does not exist yet; strategy-A projections using it are
   extrapolations from modelling velocity, stated as such.
