# MUSE-REPORT-784: Hardware completion — CAS retry attempt bound

## What was done

New file `grammatik/Grammatik/X86/CasRetryBound.lean` (wired into
`grammatik/Grammatik.lean` with one import line): a bounded-or-divergent
retry discipline over the accepted single-attempt CAS steps. The static
retry bound `k` is **derived from contention structure** where available;
programs without contention structure get a recorded **DIVERGENCE**, never
a free constant.

Core idea: a terminating retry trace `bs = fs ++ [true]` (failures then
one success) whose failures charge against at most `n` distinct foreign
installers runs at most `n + 1` attempts, and the cost summary carrying the
derived bound names exactly `some (n + 1)`. Unknown contention derives
`none` and refuses every claimed constant through the accepted refusals.

## Exact new names

- `Contention` (inductive: `.begrenzt fremd` | `.unbekannt`) — checked data.
- `retryBoundOf : Contention → Option Nat` — `some (n+1)` vs `none`.
- `fehlZaehler : List Bool → Nat` — pure failure count over outcome lists.
- `retryBoundOf_begrenzt`, `retryBoundOf_unbekannt` — bound equations.
- `fehlZaehler_angehaengt` — exact charge count for failure prefixes.
- `CasRetryBound_verbindung` (TARGET) — trace length `≤ n+1`, summary
  names `some (n+1)`, shape cost `casKosten ≤ n+2`. Every premise is used.
- `CasRetryBound_verbindung_zeuge` (TARGET companion) — joint instance
  `[false] / [false,true] / n=1` with the derived summary, plus the
  non-degenerate package: fixture program writes a table, reached run moves
  slot `0 -> 5` (`ziel_ort_einfaden_zeuge`), executed CAS pair changes
  canonical memory (word `0 -> 9` at `lockAddr`).
- `casDivergenz_ohne_schranke` — `none` plus unboundedness (reuses
  `stutter_ohne_schranke`).
- `casDivergenz_verweigert_summe` + `_zeuge` — divergent summary with a
  finite `retryTry` claim is refused (reuses
  `kostenSummeOk_verweigert_unbegrenzt`).
- `casWiederholung_ausgefuehrt`, `casWiederholung_form` — executed
  failure-stutter plus memory-changing install over the accepted
  `casSchritt` (reuses `cas_fehlschlag_zeuge`, success `rfl`, two `decide`s).
- `casLaeuft_ueber_lock` + `_zeuge` — LOCK CMPXCHG bytes run through the
  fetched LOCK path, never the pilot dispatcher (reuses
  `decodeLockExt_lock`, `pin_lock_ext_verweigert_cmpxchg`,
  `pin_lock_cmpxchg_decodiert`).

## Verification

- `./lean-probe` green after every increment (0 errors); final file probe:
  0 errors, all `#print axioms` within `[propext, Classical.choice,
  Quot.sound]` (most theorems `propext`-only).
- `./lean-bau` full project green: `Build completed successfully (485 jobs).`
- `gabbro_ziel` axioms re-checked: `[propext, Classical.choice,
  Quot.sound]` (one transient `failed to create thread` on the first
  single-process probe of the whole goal chain — the known VA-space
  apparatus issue; retry passed).
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; no premise of type
  `Prop` itself; every premise of every theorem is used by its proof.

## Reuse and provenance (no duplication)

- Single-attempt semantics: accepted `casSchritt`/`casKosten`
  (`LockedOps`), failure/success adapters (`LockedInstructionExecution`),
  unboundedness (`cas_schleife_unbeschraenkt` lineage via
  `stutter_ohne_schranke`), admission Bool (`CostSummary`), retry
  obstructions (`BudgetExecution`). Nothing redefined.
- On the "reuse the ExtendedExecution dispatcher" instruction: CAS bytes are
  **explicitly refused** by `decodeExt` (accepted pin), so attempts run
  through the combined fetched LOCK decode (`decodeLockExt_lock`) — the
  honest interface, stated as a theorem rather than a second dispatcher.
- Manual grounding from the clone-local snapshot
  `.tmp/HARDWARE-REFERENCES/` (Intel SDM 325462-093US, Sep 2026): CMPXCHG
  Vol. 2A 3-194 (txt line 46967), LOCK prefix Vol. 2A 3-565 (txt line
  63495). The manual defines one atomic attempt and promises **no**
  software-retry bound — that absence is why contention is carried as
  program data. No silicon/fairness/timing claim is made.

## What remains open (see CUTS in the file)

Per-site contention proofs (lowering/certificate producer owns which points
share a site and how many installers overlap); fairness/progress/
termination (divergent sites may spin; `FortschrittG` untouched); hardware
timing (shape units, never cycles); TSO→W/GX simulation (bridge owns it);
faults (`DecodeFault`/`HardwareFaults` own them).

## Task feedback

Nothing in the task is believed wrong. One scoping note: the deliverable
bounds **terminating** retry traces; a non-terminating CAS loop is the
recorded DIVERGENCE case, not a bounded case — this matches the
`cas_schleife_unbeschraenkt` lineage and the `kostenSummeOk` refusal shape.

## Scope discipline

Owned files only (`CasRetryBound.lean`, `Grammatik.lean` import line,
this report). No new diagnostic/gift/example/CLI numbers, no MARKE changes,
no source/checker/Spec/goal/emitter edits, no friend-reserved optimiser
files. `git status` shows only the owned module modified (import line
committed earlier in the green skeleton checkpoint `c78ddea2`).
