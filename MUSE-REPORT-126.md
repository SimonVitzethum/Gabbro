# MUSE-REPORT-126 — the reference fixture as a real Gabbro program

Lane 126 (FIFTH wave, Gabbro + Rust tests). The Lean reference fixture
`grammatik/Grammatik/ReferenzB.lean` (`refD`/`refP`/`refO`/`refSp0`) now exists
as a real, checked, emitted, driven Gabbro program, with a Rust test holding
the checker's Lean view against `refD`.

## What was done

1. **`beispiele/104-referenz.gab`** (new): module `beispiel::referenz` —
   table `Konto` (`count 2`, one slot field `stand : Stand`, `Stand = u32 in
   0 .. 100`), `lock M protects { stand } rank 0 held <= 50 ops`,
   `einzahlen(k : ptr<normal, rw> Konto, i : index into Konto, b : Betrag)`
   with `requires Held(M)`, `ensures old(k.slots[i].stand) <=
   k.slots[i].stand`, body `k.slots[i].stand = 100; lies(k, i);`
   (write-call-return, like `refRumpfEin`), and `lies(k : ptr<normal, r>
   Konto, i : index into Konto) -> Stand` with `requires Held(M)`,
   `ensures result == k.slots[i].stand`, body `return k.slots[i].stand;`
   (like `refRumpfLies`). `Betrag = u32 in 0 .. 10` mirrors
   `refSigEin.params = [.int 0 10]`.
   Checker: `gabbro pruefe` → 0 errors, 0 hints. Emitter: `gabbro emit` → 45
   lines of C, exit 0. During construction the checker fired exactly once,
   correctly: `E008` (`einzahlen` called `lies` without naming `reads
   k.slots`; fixed by adding it — E008 closes effects over the call edge).
2. **Emission driver** (`instrumente/pruefe-emission.sh`, lauf
   `"beispiel104"`): sequential composition of both threads (threads cannot
   be driven from C — see F1), `einzahlen(&k, 0, 7)` (witness argument 7,
   as in `refRho7`) then `lies(&k, 0)`, observing `"100 100 0"`
   (answer, slot 0, untouched slot 1). All 8 stages pass; stage 7 books
   `0 assumptions (...), 1 templates (0 of them UNPROVED), 6 direct forms,
   1 foreign bodies (0 state their duty), 0 narrowings from foreign
   contracts` (the 1 foreign body is the lock `M`). Poison flips the cap
   `100` → `99` and the comparison falls.
3. **`crates/gabbro-check/tests/referenz.rs`** (new, 4 tests):
   `checker_accepts_referenz`, `lean_duty_view_matches_refD` (prints the full
   `lean::module` duty register; pins `@duty … total 3 goals 3 refused 0`,
   `shapeOf` `.intIn 0 100`, `einzahlen_writes = ["Konto"]`, `lies_writes =
   []`, `b` in `intIn 0 10`, `old#1` `.le` post, `result` `.eq` post with `0
   ≤ x ∧ x ≤ 100`, both bodies present and unrefused),
   `erklaerung_gestalt_matches_refD` (one table `Konto`, count 2, one
   `IntIn(0,100)` field; one lock `M` protecting `stand`; `einzahlen`
   writelocks, `lies` reads-only-locks, both `requires Held(M)`),
   `lean_program_view_gaps_stay_visible` (prints `lean::program`; pins that
   the program datum drops `old`/`result` ensures and place ranges by name).
4. **Bookkeeping this lane owns** (each was green at baseline, red through
   this lane's files, now green again): `MARKE_EMIT` 75 → 76 (emission
   script); README `76` → `77` clean examples (2 spots); DONE.md `~~76~~ 77`;
   TODO.md foreign bodies 122 → 123 (the lock `M`); `dokumente/PLAN.md`
   call-site preconditions 20 → 21 (the `lies` call); `messung/ZEREMONIE.md`
   `94 von 1408` → `96 von 1423` with a decomposition note; README Usability
   cell `1408` → `1423` clause sites. Example number 105 stays free (only
   104 was needed; no gift probes).

## Exact names of new definitions/theorems

No Lean definitions or theorems were added (this lane is Gabbro + Rust; the
task names no Lean file and no `ZEUGE:` target, so rule 13 needs no
`_zeuge`). New Rust tests: `checker_accepts_referenz`,
`lean_duty_view_matches_refD`, `erklaerung_gestalt_matches_refD`,
`lean_program_view_gaps_stay_visible` in `crates/gabbro-check/tests/referenz.rs`.
New Gabbro items: `beispiel::referenz`, `Konto`, `M`, `einzahlen`, `lies`,
emission lauf `beispiel104` with `TREIBER104`.

## Gate results

- `./cargo-pruef`: `== exit 0; failing tests: 0` (includes the 4 new tests;
  verified present and passing in `target/debug/deps/referenz-*`).
- `./lean-bau`: `Build completed successfully (61 jobs).` (no Lean files
  touched).
- `./emission-pruef`: lauf `beispiel104` green in stages 1–8; the
  `beispiele/` count mark (76) green; the stage-9 compile sweep `225 von 225`
  green under `cc` and `clang`. The stage still exits 1 on four count drifts
  in roots disjoint from this lane's footprint — pre-existing by
  construction (my tree delta is `+beispiele/104-referenz.gab`,
  `+crates/gabbro-check/tests/referenz.rs`, script edits; none of the four
  counts reads those paths): `messung/*/` 132 vs 73, `beispiele/gift/` 8 vs
  2, outside-roots 8 vs 1, `-- erwartet: cc` 2 vs 4.
- Text guardians: `pruefe-todo.py` back to baseline 3 BEFUNDE;
  `pruefe-zahlen.py` has FEWER BEFUNDE than baseline (two pre-existing ones
  fixed by the rebooking above; only the Widerruf file count remains, 299
  booked vs 400 measured, of which +100 is foreign drift and +1 is this
  lane's new file — left red, owned by whoever books that line);
  `pruefe-englisch.py` fails identically with and without this lane (three
  pre-existing `RATSCHE GEBROCHEN`); `pruefe-kennungen.py` ALL PASS.

## Premise classes for this program (task item 3)

- **Contracts at place.** The checker establishes the call shape (arg
  counts/types, E008 effects closure — measured above) but never evaluates a
  contract: `old ≤ new` and `result == slot` are Lean duties
  (`einzahlen_meets`, `lies_meets`, all carried, `gabbro_auto` + person).
  The V-call precondition (duty_3, `lies` requires at the `einzahlen` call
  site) is discharged inside `einzahlen_meets` via the `c_lies` hypothesis
  (generator wiring), not by a checker rule — the held-set-AT-call-site
  check against the callee hull is the booked `h020` remainder for Gabbro
  callees. So: place *shape* checked, place *truth* owed (person), call-site
  Held not re-verified by the checker.
- **Footprint.** Established at effects level: `reads`/`writes k.slots` +
  `locks M` on both functions, E008-closed over the call. The D7-style
  containment (contract-read carriers ⊆ write signature, folded by
  `haengtAb_vertrag_gesamt`) is not computed per function by the checker;
  the duty channel instead assumes effects completeness (`E008`/`E010`).
- **Guard discipline.** Established syntactically: `requires Held(M)` +
  `effects locks M` passes H007/H011/H020 with zero diagnostics (the
  `beispiele/01` idiom). The semantic half (table watches,
  `wache_aus_schuld` from `J.hSchuld`) is Lean-side and has no run here.
- **Unshared facts.** Vacuous for this unit: no marks, one table, no
  `concurrent` set, no context roots — W001/W002 and `PCMarkSep`/
  `PCUnsharedSep` owe nothing and establish nothing. Interference freedom of
  the two threads is NOT established anywhere: the threads exist only in the
  emission driver, outside every checker and Lean run.

## Findings (differences checker-vs-model; each is a correspondence gap)

- **F1.** `concurrent { einzahlen, lies }` was written, checked green
  (W001 passes — one writer), emitted fine (emitter skips it), but
  `gabbro zeugnis` books it as `UNCLASSIFIED: item 'concurrent'`, which
  fails emission stage 7. Any concurrent unit is therefore currently
  undrivable in `pruefe-emission.sh`. The declaration was removed from the
  file; the driver runs the sequential composition instead, as the task
  permits. The file header documents this.
- **F2.** `requires Held(M)` is strictly stronger than `refReqEin = true`.
  The checker needs a guard exhibit for a guarded slot (H007); the model
  assumes the guard via `haelt`/`darf`. Same for `refReqLies`.
- **F3.** Surface signatures carry `(k, i)` beside the value parameter `b`;
  `refSigEin` has one param, `refSigLies` none. The carrier and index are
  ambient in the model, explicit in the surface. The Lean duty view binds
  the index bound from `count 2` (`intIn 0 1`) — a true match, not a gap.
- **F4.** `gabbro lean` (program datum) drops both ensures (`post = True`,
  by the names `old-state` and `result-in-ensures`) and the place range
  (`isInt` where the duty keeps `intIn 0 100`). Contracts live in
  `gabbro pflichten --lean` (duty register), which carries all of them.
  Anyone reading only the program view sees a contract-free program.
- **F5.** Neither Lean view names the lock: `Held(M)` exports as `true`
  (by design — lock passes discharge it). Guard correspondence is
  checker-side only.
- **F6.** `refB_erreicht` (F-machine) and `refB_pc_erreicht` (PC machine)
  have no checker counterpart — the checker never runs the program. The
  emission driver covers the observable half (`refB_schreibt`: slot
  `0 -> 100`, pinned as `100 100 0`).
- **F7.** Pre-existing reds, unchanged by this lane (baseline measured via
  `git stash`): emission stage-9 drifts (above), todo 3 BEFUNDE, englisch 3
  broken ratchets, zahlen Widerruf/Kennzahlen entries. This lane's zahlen
  footprint was rebooked; two pre-existing zahlen BEFUNDE got fixed along
  the way (ZEREMONIE-insgesamt, README-Kennzahlentafel).

## What I believe is wrong in the task

- "Two threads/entries running them" cannot mean in-surface threads if the
  same program must also pass the emission check: F1 shows a `concurrent`
  declaration and a clean certificate are mutually exclusive today. The
  task's own fallback ("or their sequential composition") is the only
  currently working reading; the primary reading needs the certificate to
  classify `concurrent` first.
- "Same contracts as refP" is not literally satisfiable: F2/F3 (Held
  strengthening, carrier/index params) are forced by the checker. The test
  pins the exact shape of the deviation instead of claiming identity.

## Open

- 105 stays free; no gift probes (per task).
- `concurrent` certificate classification (owner: whoever owns `zeugnis.rs`).
- Per-call-site Held verification for Gabbro callees (`h020` remainder).
- The four pre-existing emission stage-9 drifts and the guardian reds in F7
  belong to their owners; this lane changed none of them.

## Merge resolution (2026-09-12, reviewer merge of master-neu)

Merge resolved per instruction (docs take the master side — note: under merge semantics that side is `--theirs`, not `--ours`; emission keeps `beispiel104` beside `beispiel96`; `MARKE_EMIT` re-booked 81 -> 83 measured; ZEREMONIE re-measured 111 von 1501); gates on the merged tree: cargo-pruef exit 0, lean-bau green, emission-pruef exit 0 (ALL PASS).

## CUTS

No Lean work was done in this lane, so there is nothing unproved by this
lane. The gaps above (F1–F6) are reported, not closed.
