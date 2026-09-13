# MUSE-REPORT-141 — three correspondence gaps closed in the Rust lanes (F1, F4, F5 of lane 126)

Lane 141 (SIXTH wave, Rust transfer lane). Lane 126 (`messung/muse/MUSE-REPORT-126.md`,
findings F1, F4, F5) showed the checker's views of the reference program drifting
from the Lean fixture `grammatik/Grammatik/ReferenzB.lean` (`refD`/`refP`): F1 a
`concurrent { … }` unit is booked `UNCLASSIFIED` by `gabbro zeugnis`, failing emission
stage 7; F4 `gabbro lean` (the program datum) drops both `ensures` and the place ranges
(`isInt` instead of `intIn 0 100`); F5 no Lean view names the lock (`Held(M)` exports
as `true`). This lane fixes all three. No Lean definitions or theorems were added or
changed (`grammatik/` untouched); the transfer is one of the model's decidable
declaration facts (guard facts in the `D.braucht`/`haelt` shape) carried into the
emitter's Lean view.

## What was done

1. **F1 — `concurrent` classified in the certificate census** (`crates/gabbro-check/src/zeugnis.rs`):
   new `EINORDNUNG` entry `concurrent` as `Traegt::Geloescht` (like `group`: a
   compile-time statement the emitter writes nothing for, checked at translation time
   by `nebeneinander.rs`), plus the explicit `ItemArt::Concurrent(_) => zaehle(&mut e,
   "concurrent")` arm in `erhebe` — without it the item falls into the catch-all that
   pushes `UNCLASSIFIED` directly and never consults the census (found by the new test,
   not by reading). `beispiele/104-referenz.gab` declares `concurrent { einzahlen, lies };`
   again; the emission driver runs both threads one after the other (the sequential
   composition the emitter produces — it emits no threads), observing `100 100 0` as
   before. The stage-7 booked line is unchanged (erased forms are not counted there).
2. **F4 — `gabbro lean` exports the ensures and the exact ranges** (`crates/gabbro-check/src/lean.rs`,
   `program()`/`routines()` only; the duty channel `module()` is byte-identical):
   `ensures` are translated at the `Bound` site with `old`/`result` bound (the same
   `clause_prop` the duty channel uses), emitted as `def <fn>_post (s s' : State)
   (r : Option Value) : Prop`; parameter shapes in `<fn>_pre` use the `hasShape`
   conjuncts with declared ranges (`(.hasShape "b" (.intIn 0 10))`); new defs
   `placesRanged : List (String × String × Int × Int)` and `wellFormedRanged`
   (`(s.world (.slot …)).hasShape (.intIn lo hi) = true`). Nothing drops by the names
   `old-state`/`result-in-ensures` any more. This deliberately reverses the decision
   documented in `messung/ERGEBNIS-ZWEI-NAMEN.md` §2 ("sayable, deliberately unsaid") —
   the reference program showed its price: the program view alone displayed a
   contract-free program.
3. **F5 — the lock and the guard facts are exported** (same files): new defs `locks :
   List String`, `lockProtects : List (String × String)` (as written), `tableGuards :
   List (String × String × List String)` (uniquely resolving places only; the rest stay
   in `lockProtects`, never dropped silently), and per routine `def <fn>_held :
   List String` from `locks` effects beside `requires Held` witnesses (new `held_of`,
   structural). For 104: `locks = ["M"]`, `tableGuards = [("Konto", "stand", ["M"])]`,
   both `_held = ["M"]` — the `braucht`/`haelt` halves of `refD`.
4. **Tests**: `referenz.rs`: `lean_program_view_gaps_stay_visible` replaced by
   `lean_program_view_carries_refD` (pins every carried fact above), new
   `concurrent_is_classified` (census books `concurrent` once, nothing unclassified);
   `rechenwerk.rs`: `lean_export_sagt_die_zusage_unter_dem_klauselnamen_ab` now pins the
   carried two-state post instead of the deliberate drop. `instrumente/miss-lean-reichweite.py`
   counts the new two-state post form as kept alongside `eval s …`.
   Emission script: `beispiel104` comment reworded (booked census line unchanged).

## Exact names of new definitions/theorems

No Lean items (rule 13 needs no `_zeuge`: no Lean theorems added). New Rust items, all in
`crates/gabbro-check/src/lean.rs` unless noted: `Routine::ranges`, `Routine::held`,
`held_of` (with inner `lock_of_ort`, `held_in_pred`); `program()` defs `placesRanged`,
`wellFormedRanged`, `locks`, `lockProtects`, `tableGuards`, `<fn>_held`, two-state
`<fn>_post`; `zeugnis.rs`: `EINORDNUNG` entry `concurrent` + `erhebe` arm. New tests:
`concurrent_is_classified`, `lean_program_view_carries_refD` (`referenz.rs`); rewritten
`lean_export_sagt_die_zusage_unter_dem_klauselnamen_ab` (`rechenwerk.rs`). New Gabbro
item: the `concurrent { einzahlen, lies }` set in `beispiele/104-referenz.gab`.

## Gate results

- `./cargo-pruef`: `== exit 0; failing tests: 0` (full suite, incl. the rewritten tests;
  two reds seen mid-lane were this lane's: the missing `erhebe` arm and the old
  deliberate-drop test — both fixed, none deleted).
- `./emission-pruef`: `== exit 0`, `ALL PASS`, `beispiel104` green in stages 1–8 with the
  `concurrent` set in the file (stage 7 books the unchanged line; certificate shows
  `concurrent 1x` under D ERASED, no UNCLASSIFIED).
- `./lean-bau`: `Build completed successfully (89 jobs).` (`grammatik/` untouched.)
- Text guardians, run directly: `kennungen` ALL PASS, `konstrukte` green, `saetze` green,
  `deckung` green (43 refusal reasons, UNCOVERED = 0 — no new `LeanReason`), `klauseln`
  exit 1 identical to the stashed baseline (`zucker`, pre-existing), `englisch` exit 1
  identical to baseline (the same 1 German finding; +32 English lines from this lane),
  `reichweite`/`grammatiktafel`/`widerruf`/`vergabe` green. `todo`/`zahlen` not run (they
  shell out to `cargo`, against rule 1); this lane changes no docs or numbers they book.

## Exported Lean view of 104 against refD (task item: compare, remaining differences)

| `refD` fact | Lean view after this lane | status |
|---|---|---|
| `Tab = Unit`, `count = 2`, one `.int 0 100` field | one table `Konto`, count 2, `stand : IntIn(0,100)`; `places`, `placesRanged (Konto,stand,0,100)`, `wellFormedRanged` | carries |
| `braucht () = [.inl ()]` | `lockProtects (M,stand)`, `tableGuards (Konto,stand,[M])` | carries (NEW) |
| `refSigEin`: params `[.int 0 10]`, no result, `haelt [()]`, writes | `_pre` hasShape `b` in 0..10, no result, `einzahlen_held [M]`, duty `einzahlen_writes [Konto]` | carries (NEW ranges/held) |
| `refSigLies`: no params, `.int 0 100` result, `haelt`, reads | `lies_held [M]`, `lies_writes []`, `lies_post` with bound `result` | carries (NEW held/post) |
| `refReqEin`/`refReqLies = true` | `requires Held(M)` exports as `true` (lock passes discharge it) | known deviation F2, unchanged |
| `refEnsEin` (`old ≤ new`) | `einzahlen_post` with `old#1`, `.bin .le` | carries (NEW) |
| `refEnsLies` (`result = slot`) | `lies_post` with `result`, `.bin .eq` | carries (NEW) |
| bodies `refRumpfEin`/`refRumpfLies` | `einzahlen_body` (assign + `lies` call), `lies_body` (slot return) | carries (already) |
| `refO`/`refO_gut`, `refSp0` | certificate A `none`; driver observes `100 100 0` | carries (already) |
| two threads | `concurrent { einzahlen, lies }` + census entry | carries (NEW) |
| `refB_erreicht`/`refB_pc_erreicht` (runs) | sequential driver only; the checker never runs | gap F6, unchanged |
| carrier/index params `(k, i)` beside `b` | surface needs them; model leaves them ambient | deviation F3, unchanged |
| `rang () = 0`, `held <= 50 ops` | checker-side only, not exported | remaining (minor) |
| result range `Stand 0..100` as its own clause | implied by `result == slot` + `wellFormedRanged`, not stated | remaining (minor) |

Lean-compile note: `pruefe-lean-programm.sh` (needs mathlib, not run per rule 1) compiles
the export against `Gabbro.Body`. Every new emitted form is either duty-channel vocabulary
that already compiles there (`clause_prop` bodies, `(.hasShape …)` terms, `(r : Option
Value)` binders — the foreign-post shape) or core Lean (`List`/tuple literals,
`(v).hasShape … = true` over the existing `Value.hasShape`, `∀ k` as in `wellFormed`).
`Spec.lean`/`SpecGift.lean` reference only `<fn>_body` and the first two `places`
columns, both unchanged in form.

## Numbers and what I believe is wrong in the task

- Codes 260–264 and gift 930–934 are reserved and stay free: no new refusal was needed
  (F1 is a census entry, F4/F5 export enrichment), so no sentence ratchet, no poison
  probe — precedent lane 113 (codes 205–209, gifts 877–879). Examples: only 104 modified,
  per instruction.
- "A driver that runs both threads" cannot mean real threads: the emitter produces no
  thread notion (by design — `concurrent` is erased, like `group`), so the driver runs
  both threads one after the other. The task's fallback is the only working reading, and
  the file header now says so instead of documenting an absence.
- F5's `D.braucht` half resolves by field name where exactly one table carries it (the
  same name matching the checker uses); ambiguous protections stay visible in
  `lockProtects`. A module-qualified `protects` spelling would remove the fallback and is
  not proposed — it would be grammar churn for a case the corpus never shows.

## Open

- `pruefe-lean-programm.sh` over the new datum (needs Lean+mathlib; vocabulary argument above).
- `todo`/`zahlen` guardians (shell out to `cargo`; no numbers of theirs were touched).
- F2/F3/F6 deviations and the two minor remainders in the table above.

## CUTS

No Lean work was done in this lane, so there is nothing unproved by this lane.
