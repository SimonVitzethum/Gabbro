# MUSE-REPORT-65 — Arena as a linear mark (PLAN-ERWEITUNG.md section 3, lane E4, model half)

Branch: `muse/65`. New file `grammatik/Grammatik/Arena.lean` (namespace
`Gabbro.Grammatik.Arena`), wired as `import Grammatik.Arena` at the end of
`grammatik/Grammatik.lean`. No existing file touched otherwise.

Second version (2026-09-12, after reviewer rejection of v1): the v1 theorems
carried no content (`allocs` never consulted the capacity; the reset theorem
was a tautology; the fragmentation statement was true of any numbers). This
version is TYPED: the claims are carried by the types.

## What was built

Model (no sibling imports, core Lean only):

- `Kap` (`lo`/`hi`).
- `Arena (k : Kap) (g : Nat)` with `used : Nat`, `hused : used ≤ k.hi` — the
  bound is construction, not premise.
- `ArenaIdx (g n : Nat)` with `i : Nat`, `hi : i < n` — an index into the
  first `n` cells of generation `g`.
- `Marke (g : Nat)` — a token with a PRIVATE constructor (`private mk`), so
  outside this module only `start`/`reset` produce marks.
- `start (k) : Arena k 0 × Marke 0`.
- `alloc (a : Arena k g) : Option (Arena k g × ArenaIdx g (a.used + 1))`:
  success branch exactly while `a.used < k.hi`.
- `reset (a : Arena k g) (m : Marke g) : Arena k (g+1) × Marke (g+1)` with
  used = 0. `a`/`m` are consumed at the TYPE level (the generation index
  changes); the remaining unused-variable linter warnings on these two defs
  mark exactly that value-level irrelevance.
- `lookup (a : Arena k g) (m : Marke g) (x : ArenaIdx g n) (h : n ≤ a.used)`:
  TOTAL, returns `x.i`. A stale index (`ArenaIdx g n` against `Marke (g+1)`)
  does not typecheck.
- `allocSeq (n) (a) : Option (Σ _ : Arena k g, List Nat)`: iterates `alloc`,
  collecting taken slot positions; `none` at the first full arena.

Theorems (all `./lean-probe` green, `#print axioms` at the end of the file;
no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no `Prop`-typed premise,
no `have _x :=` anywhere, every premise used):

- `alloc_erfolg`, `alloc_fehlschlag`, `alloc_used'`, `alloc_idx'` (step facts).
- `alloc_scheitert_gdw : alloc a = none ↔ a.used = k.hi` — both directions;
  forward uses `a.hused` against the negated guard.
- `allocSeq_gelingt` (helper, induction on `n` generalizing the arena):
  from `b.used + n ≤ k.hi`, `allocSeq n b = some ⟨b', l⟩` with `l.length = n`,
  `b'.used = b.used + n`, `l = List.range' b.used n`.
- `alloc_innerhalb_reserve`: from `(reset a m).1` (used = 0), `n ≤ lo ≤ hi`
  gives `allocSeq n … = some ⟨a', l⟩ ∧ l.length = n`. The success fact comes
  from iterating `alloc` — nothing is discarded.
- `keine_fragmentierung`: same setup gives `l = List.range n` (via
  `List.range_eq_range'`).
- `alloc_innerhalb_reserve_zeuge`: `k = ⟨2, 4⟩`, two allocs after reset give
  `some ⟨a', [0, 1]⟩` — the equation by `rfl` (kernel computation through
  `dite`; proof irrelevance covers the embedded bound proofs).
- `reset_used` (`rfl`), `reset_verbraucht`: `(reset a m).2 = m'` for ANY
  `m' : Marke (g+1)` — marks carry no identity beyond the type index, proved
  by casing both marks (private constructor is accessible in-module).
- `lookup_gilt`: `lookup a m x h = x.i ∧ x.i < a.used + 1`.

Axioms: at most `[propext, Quot.sound]`; `reset_used`, `reset_verbraucht`
axiom-free. No premise quantifies over program syntax, so rule 13 bites only
on the `ZEUGE:` line — discharged by the witness above (two successful
allocs changing used 0 → 2, indices 0 and 1; the arena analogue of a
memory-changing step; the syntax-level non-degeneracy clause is vacuous for
a syntax-free model).

## Last `./lean-bau` result line

`Build completed successfully (37 jobs).` — `== 0 error line(s) in the
COMPLETE output`.

## What remains open

Filed as `CUTS` in `Arena.lean`: "no index survives a reset" is a TYPE fact
(`ArenaIdx g n` vs `ArenaIdx (g+1) n` — Lean rejects the application; a
theorem stating it would have to exhibit the ill-typed term); `lookup`
returns the slot position, not a stored value (no heap array, no load-store
correspondence); linearity (`Λ` bookkeeping) stays checker-side.

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
  `or R` (this file's `allocSeq_gelingt`), steps between `lo` and `hi`
  owe the error branch (`alloc_scheitert_gdw`).

## Remarks on the task

- The v1 defects listed in the feedback are accepted as stated; v1 is fully
  replaced on this branch (never merged to master), keeping the required
  names `alloc_innerhalb_reserve`, `keine_fragmentierung`,
  `alloc_innerhalb_reserve_zeuge` and adding the required `alloc_scheitert_gdw`
  (as `↔`, stronger than v1's one-direction `∨`) and `reset_verbraucht`.
  `idx_nach_reset_unerreichbar` is dropped on purpose: per the feedback it
  can only be a tautology as a theorem — its content is now the TYPE fact
  documented in CUTS.
- `allocSeq` returns `Σ _ : Arena k g, List Nat` (positions, not `ArenaIdx`,
  since the bounds differ per step); `keine_fragmentierung` states the
  reviewer's `List.range n` on the positions, which is what "exactly
  `[0, …, n-1]`" means here.
