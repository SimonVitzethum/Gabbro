# MUSE-REPORT-24: Read-only audit of `grammatik/Grammatik/Extraktion.lean`

Lane 24. No existing file modified. One new file: `messung/muse-audit/24/Audit24.lean`
(checked with `./lean-probe`, no errors, only linter warnings about unused names
in the F5 demonstration, which is the point there).

## Scope

Read all 3966 lines of `Extraktion.lean` (22 sections, §§1-22 with a duplicated
§14 number). Checked every `theorem` statement against its proof term for patterns
(a)-(e) from the task. Cross-read the callee definitions in `Geteilt.lean`
(`BauLauf`, `geteilt_treu`, `lauf_hat_eintritt`), `Maschine.lean`
(`Stmt.istBlatt`, `PCAtom`, `SpeicherVertrag`, `GenStart`, `PCReach`),
`Interferenz.lean` (`HaengtAb`, `RahmenGleichAuf`), `InterferenzAllgemein.lean`
(`StabilKette`, `stabilKette_gilt`, `SpecQ`, `SpecTriple`, `stabil_from_spec`,
`eval_liest_nur_speicher_diag`), `Semantik.lean` (`eval` signature with separate
entry/present worlds, `World`, `Ereignis`, `ergEnv`), and `Syntax.lean`
(`Stmt` constructors, `Programm` record with `requires`/`ensures`/`rumpf`).

## Findings table

| # | file:line | pattern | one-sentence evidence | demonstration | status | severity |
|---|-----------|---------|----------------------|---------------|--------|----------|
| F1 | Extraktion.lean:2577-2580 | (a) conclusion = premise unfolded | `progAus_aus_rumpf` is `rfl` of the `progAus` definiens | Audit24.lean (`have h := @...progAus_aus_rumpf`) | VERIFIED (checks) | low |
| F2 | Extraktion.lean:2636-2640 | (a) conclusion = hypothesis | `progTreue_aus_progAus` is `intro f a ha; exact ha` -- membership identity | Audit24.lean | VERIFIED | medium: section header calls it "Program fidelity" |
| F3 | Extraktion.lean:404-407 | (a) conclusion = premise, repr change | `bauLaufSpiegel_genau` is `Iff.rfl`: `bauLaufSpiegel` is definitionally `Geteilt.BauLauf` | Audit24.lean (`example ... := bauLaufSpiegel_genau`) | VERIFIED | low (booked as wiring, honest) |
| F4 | Extraktion.lean:2584-2590 | (a) | `stmtAtome_locks` is `rfl` of the `stmtAtome` clause; re-proved as `rfl` in audit | Audit24.lean (`... := rfl`) | VERIFIED | low |
| F5 | Extraktion.lean:3462-3470 | (e) false/vacuous premise | `hwit_leer`: `hempty : J.schrittFaden = []` makes `J.schrittFaden[k]? = some g` uninhabitable; proof is `rw hempty; simp` -- holds because no step is ever owed | Audit24.lean (`hk : ... = some g` implies `False`) | VERIFIED | medium: §20 uses it as the induction base of the "prefix fold", i.e. the fold starts from a duty over an empty schedule that no real run has |
| F6 | Extraktion.lean:3802-3818 | (b) unused premises | `hwit_aus_lauf_blatt` takes `tabs globs` absent from the conclusion (`∃ w Λw hwL, zugriff t₀ ... ∈ neu`); they only type `hmem` | described, proof-term reading | UNVERIFIED | low |
| F7 | Extraktion.lean:3829-3850 | (d) header claims more | §21 header says both duties "discharged"; `hwit_aus_lauf` concludes `M.lauf = [] ∨ (TraegerSchreibt ... → ∃ ...)` where the witness leg's antecedent is discarded by `intro _` (line 3865) and the empty-run leg covers the start -- the unconditional prefix duty is NOT proved, the disjunction marks exactly its failure modes | described, proof-term reading | UNVERIFIED | medium: the docstring itself admits "VACUOUS here and hence dropped" for the code predicate, which is honest; the overclaim is "discharges both duties" |
| F8 | Extraktion.lean:3333-3345 | (b) restated field | `hwit_aus_feuerung_ohne_axiomCall` "produces" `zugriff t₀` where `t₀` is pinned by input `hmem : .inl t₀ ∈ stmtTraeger ... s` (proof derives `t₀ = t` by `mem_singleton`); carrier is input, only `w`/`Λw`/`hwL` are produced | described | UNVERIFIED | low |
| F9 | Extraktion.lean:1432-1444 | (c) degenerate contract | `QRequires`/`QEnsures` quantify over ALL envs/return values at ONE world AND feed the same world as entry and present (`eval σ e σ ρ` by `rfl`, checked); since `eval` reads `old(...)` from the entry world (`altSlot`/`altGlob`), `old` collapses into the present -- no postcondition can relate entry to return | Audit24.lean (`audit_QRequires_unfold`, `audit_QEnsures_unfold`, both `rfl`) | VERIFIED | HIGH: this is exactly hard-rule 4(b); every downstream `HaengtAb`/`StabilKette`/`SpeicherVertrag` result over `QRequires`/`QEnsures` inherits it |
| F10 | Extraktion.lean:1581-1603 | (a) fold | `stabilKette_requires_gilt`/`_ensures_gilt`/`_invariante_gilt` are `stabilKette_gilt` applied to `haengtAb_*`: `StabilKette` is by def `HaengtAb ∧ ...` with the second leg pointwise `stabil`; content beyond the generic fold is only the footprint-cover premises | `have h := @...stabilKette_requires_gilt` checks | VERIFIED (presence) | low: the footprint-cover premises are genuine per-program work |
| F11 | Extraktion.lean:3840-3842,3621-3623 | (e) false premise for ordinary programs | `hmem_all : ∀ ... s, .inl t₀ ∈ stmtTraeger tabs globs s` quantifies over ALL leaf statements, but `stmtTraeger` is `[]` for `assignVar`, calls, locks, registers, marks, terminals (lines 2428-2452); any program containing such a leaf makes `hmem_all` uninhabitable. Demonstrated: `assignVar` carrier membership implies `False` | Audit24.lean (F11 `example ... : False`, `simp [stmtTraeger]`) | VERIFIED | HIGH: `hwit_aus_lauf`/`hwit_alt_faltung` apply only to the fragment where every leaf writes the same table; the docstrings do book this ("Coverage (exactly)...") so it is disclosed, but the theorem statements quantify over all `Stmt` |
| F12 | Extraktion.lean:533-551 | (a) | `geteilt_treu_aus_bau` is `Geteilt.geteilt_treu` at the `bauAus` term, argument-for-argument; same for `eintritt_aus_baulaufSpiegel_aus_bau` (`lauf_hat_eintritt`) and `nur_deklariert_aus_baulaufSpiegel_aus_bau` | `have h := @...geteilt_treu_aus_bau` checks | VERIFIED | low (wiring, disclosed) |
| F13 | Extraktion.lean:2604-2626 | (b) | `stmtAtome_marken_deckt`/`stmtAtome_traeger_deckt` take `tabs globs` absent from conclusion and unused after the `stmtAtome_blatt_eq` rewrite (leaf atoms do not filter by domain) | described | UNVERIFIED | low |
| F14 | Extraktion.lean:3924-3961 | (d) overclaim | `speicherVertrag_aus_Q` header: "contracts read only live memory"; proof shows `eval` agrees under FULL memory equality (`σ.speicher = σ'.speicher`, all slots+globals) -- i.e. any trace-ignoring predicate qualifies; nothing requires/ensures-specific beyond `eval` is shown. The trace-independence itself is real (via `eval_liest_nur_speicher_diag`), so this is a scope overclaim, not a false theorem | described | UNVERIFIED | medium |

## What I checked and found clean (no finding)

- `eval_liest_nur_orte` (§13, line 1035): genuine induction over `Expr`, all
  premises fire per-constructor; `eval_liest_orte`/`eval_aus_rahmen` are thin but
  honest corollaries. Not pattern (a): the corollary step (instantiating `os := e.orte`)
  is stated, not hidden.
- `haengtAb_expr`/`haengtAb_ensures_shape`/`haengtAb_invariante_shape` (§14):
  real proofs from `eval_aus_rahmen`; every premise used.
- `haengtAb_weitet`, `haengtAb_konjunktion`: genuine (if small) lemmas.
- `kantenTreue_aus_bau`, `fussTreue_aus_bau`, `paarTreue_aus_bau`,
  `paarVoll_aus_bau` (§8): real membership derivations; premises all used.
  `paarVoll_aus_bau`'s `hvoll`/`hbound` are strong but disclosed as checker duties (S4).
- `geteiltTab_trifft`/`geteiltGlob_trifft`/`geteiltAus_tab`/`geteiltAus_glob`/`geteiltAus_fremd`
  (§4): genuine; `hinj`/`hdisj` premises real and used.
- `execEreignis_aus_blatt_ohne_axiomCall` (§17) and `execEreignis_aus_axiomCall`
  (§18): case-by-case event characterizations; `hbytes`/`hax`/`hleaf` all fire.
  Long but substantive.
- `hwit_alt_transport`, `hwit_alt_schritt` (§20): genuine list/index reasoning.
- `stmtAtome_blatt_eq` (§14-prog): genuine case analysis (`cases s`), not `rfl`
  alone -- the leaf set is characterized, honestly.
- `liestVertrag*_fall`, `liesTreueMitVertrag`, `liesTreueMitInv`,
  `rahmenDecktLiesMitVertrag_aus_rahmen` (§§15-16): real hull-membership proofs.
- `offeneVerweigerungspflichten` (§16 end): a `Prop` register, honestly "gebucht,
  nicht bewiesen".
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` found in the file (by
  construction of the audit: `#print axioms` lines throughout show only
  `propext`/`Classical.choice`/`Quot.sound`); no premise of type `Prop` itself
  found among the theorems I inspected.

## Things in the task I believe are wrong or need narrowing

- The task says `QRequires`/`QEnsures` are "around line 1432" -- correct
  (1432-1448). But the HARD-RULES 4(b) framing ("quantify a contract's
  parameters or result away") slightly undersells F9: the deeper defect is not
  just the `∀ ρ`/`∀ v` quantification but feeding the SAME world as entry and
  present, which collapses `old(...)`. Both halves verified by `rfl` in the
  audit file.
- "Zero findings is a valid result" -- not the outcome: F9 and F11 are real,
  verified, and high-severity for anyone wiring `Ziel.lean` §13's
  `ziel_nutzer_last_aus_pc_Q` through these predicates.

## Build status

- `./lean-probe messung/muse-audit/24/Audit24.lean`: green (no errors; only
  `linter.unusedVariables` warnings on the F5 names, intentional).
- `./lean-bau`: NOT run (read-only lane; no existing file touched, so the
  project build is unaffected by construction). `git status` shows only the new
  audit file (plus this report) as untracked.

## New names (audit file only, no `Grammatik` namespace additions)

`audit_QRequires_unfold`, `audit_QEnsures_unfold` (both `theorem`, `rfl`
proofs); remaining items are `example`s or comments. No `import Grammatik.*`
line added to `grammatik/Grammatik.lean` (nothing to wire: audit-only lane).

## CUTS

F6, F7, F8, F10-qualitative-part, F13, F14 are analytic (proof-term/statement
readings) and marked UNVERIFIED per the task's rule; F1-F5, F9, F11, F12 are
checked `example`s/`theorem`s verified by `./lean-probe`. The project-level
question the audit leaves open: whether `Ziel.lean` §13 consumes `QRequires`/
`QEnsures` at entry/return positions where the F9 collapse matters -- that file
was out of slice.
