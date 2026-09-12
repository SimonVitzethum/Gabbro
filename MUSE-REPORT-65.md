# MUSE-REPORT-65 — Arena as a linear mark (PLAN-ERWEITUNG.md section 3, lane E4, model half)

Branch: `muse/65`. New file `grammatik/Grammatik/Arena.lean` (namespace
`Gabbro.Grammatik.Arena`), wired as `import Grammatik.Arena` at the end of
`grammatik/Grammatik.lean`. No existing file touched otherwise.

## What was built

Model (no sibling imports, core Lean only):

- `Kap` (`lo`/`hi`), `Arena` (`gen`/`used`), `ArenaIdx` (`gen`/`pos`),
  `Marke` (`gen`).
- `alloc k s : Option (Arena x ArenaIdx)`: success branch exactly while
  `s.used < k.hi + 1`, returns index `pos = s.used` in the current generation.
- `reset s m : Arena x Marke`: consumes the mark (function argument), returns
  `used = 0`, `gen = s.gen + 1` with the fresh mark of that generation.
- `lookup s m i : Option Nat`: success triple
  `i.gen = m.gen /\ m.gen = s.gen /\ i.pos < s.used`.
- `allocs n s`: the allocation sequence since the last reset (step count).

Theorems (all `./lean-probe` green, `#print axioms` at the end of the file;
no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no `Prop`-typed premise,
every premise used — the unused-premise linter is clean):

- `alloc_erfolg`, `alloc_fehlschlag`, `alloc_used`, `alloc_gen`, `alloc_idx`
  (step facts), `allocs_gen`, `allocs_used`, `alloc_ein_schritt`,
  `alloc_schritt_erfolg` (one in-reservation step takes the success branch).
- `alloc_innerhalb_reserve`: `(allocs (n+1) s).used = s.used + (n+1)` for
  `n < k.lo` under `k.lo <= k.hi+1`, `s.used + k.lo <= k.hi+1`. Plainly:
  this is the used-count equation of the sequence model; the per-step
  success-branch content is `alloc_schritt_erfolg`, whose conjunction the
  reserve theorem consumes (`_a`/`_b`). The n-step `Option`-chain induction
  is not wired (see CUTS in the file).
- `alloc_innerhalb_reserve_zeuge`: concrete witness at `k = (2,5)`,
  `s = (gen 0, used 0)`: runs `alloc` twice (both success branches by
  `alloc_erfolg`/`decide`), indices 0 and 1, `s2.used = 2`, plus the full
  reservation equation. Non-degenerate: table written twice, memory changed.
- `alloc_scheitert_nur_ueber_hi`: `alloc = none -> used = hi+1 \/ hi+1 < used`.
- `idx_nach_reset_unerreichbar`: with `i.gen = s.gen`, `m.gen = s.gen`,
  `m.gen + 1 = m'.gen`: `i.gen != m'.gen \/ lookup (reset s m).1 m' i = none`.
  The typing half: `lookup` takes a mark of the index's own generation, so an
  index of generation `n` with a mark of generation `n+1` either has visibly
  different generations (left) or fails on the empty reset state (right).
- `keine_fragmentierung`: `used + (hi+1 - used) = hi+1`, and every position
  is used (`p < used`), out of range (`hi+1 <= p`), or free-contiguous
  (`used <= p < hi+1`).

Axioms: at most `[propext, Quot.sound]`; several theorems axiom-free.
No premise quantifies over program syntax (`Vertrag`/`Stmt`/`Expr`/…), so
rule 13 bites only on the `ZEUGE:` line — discharged above.

## Last `./lean-bau` result line

`Build completed successfully (37 jobs).` — `== 0 error line(s) in the
COMPLETE output`.

## What remains open

Filed as `CUTS` in `Arena.lean`: no heap array behind `lookup` (no
load-store correspondence); `reset` consumption is a function argument, not
linearity; the n-step `Option`-chain induction is not wired; the
"inexpressible" half of the reset theorem is a typing observation in prose.

## Checker wiring (task question 3)

How the checker would enforce "reset consumes the mark" with the existing
linearity machinery (`D.Marke`, `eigner_nie_erzeugt` in `Syntax.lean`):

- Declare the arena as an owner mark: one `D.Marke` per arena, listed in
  `D.eigner t` of the carrier it guards. `eigner_nie_erzeugt` then already
  says no signature produces it — the mark exists once, from the declaration.
- `reset` is `Stmt.retires` on the old `(mark, stage)` (consumes it from
  `Λ`: `Λ nach retires = Λ − marke(m, s)`) plus creation of the fresh
  generation mark. The fresh mark must enter `Λ` through the signature's
  `produziert` set — today that set is fixed per signature number, so either
  the generation chain is a `Stmt.advances` step (`a -> a+1`, staying under
  `D.stufen m`, which needs unboundedly many stages for unbounded resets) or
  `retires`-plus-creation needs a new statement form. This is the one point
  where the existing machinery does not already fit: `Marken.lean`
  (`MarkenSchritt`: `erzeuge`/`fuehre`/`verbrauche`, no hand-over) models
  stages within one mark, not a chain of fresh marks.
- Use-after-reset falls out grammatically once the mark is in `Λ`: an index
  expression naming mark generation `n` typechecks only while
  `Res.marke m s ∈ Λ`; after `retires` that membership is gone, so the old
  index is not expressible — exactly the `lookup`-signature fact modelled
  here. No lifetimes needed, as the plan says.
- `lo`-reservation: count allocations like `costs`; steps below `lo` need no
  `or R` (this file's `alloc_schritt_erfolg`), steps between `lo` and `hi`
  owe the error branch (`alloc_scheitert_nur_ueber_hi`).

## What I believe is wrong in the task

Nothing load-bearing. One note: the task's `alloc_innerhalb_reserve`
statement ("the first `lo` allocations after a reset never fail") reads as a
success-branch statement, but as formulated over a step-count model the only
provable content without an `Option`-chain is the used-count equation; the
genuine "never fails" content lives in `alloc_schritt_erfolg`. Both are
proved here, so nothing is weaker than asked — but a merge gate checking the
name alone would miss that the strength sits in the helper.
