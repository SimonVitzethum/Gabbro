# MUSE-REPORT-177: contracts on function-pointer types

Branch: lane worktree (no branch named; tree at `75a85cb2` + this lane). Rust lane.
No `.lean` files touched. `emit.rs` untouched (contracts are ghost).

## 1. What was asked, in one paragraph

A `fn(...) -> T` type carried costs and effects but no logic, so "for every
comparator that is a total order, the result is sorted" could not be stated in the
carried fragment. The model already quantifies the user obligation over every handler
that respects its contract (`KoerperGutS` / `RespektiertRahmen`, SATZKARTE.md §12-§16)
and admits indirect calls through `KandOk`. This lane builds the surface and checker
side: the contract rides on the pointer type, an indirect call is checked against it
as a direct call is checked against its callee's, and handing `&f` to the slot records
the refinement implication as a named user obligation instead of deciding it.

## 2. Measured first: the corpus before the lane

Commands (all against the baseline worktree at HEAD, `/tmp/base-177`):

- `grep -rln --include="*.gab" -E ":[[:space:]]*fn\(|= *fn\(" beispiele/ messung/` →
  **35 files** carry a function-pointer type (2 of them `beispiele/49`, `111`; the
  rest gifts, `messung/fnptr-proben/*`, fragments).
- Indirect call sites in code (`->name(` outside `--` comments, same roots) →
  **22 sites in 17 files**.
- What the checker did with them, per site class:
  - the TYPE: `N035` (missing `effects`/`costs`), `N036` (an effect no pass carries
    across: `locks`, `masks`, `consumes`, `publishes`), `N037` (any `requires` or
    `ensures` refused outright -- pinned by `gift/247` and `gift/248`).
  - the PRODUCER `&f`: `M127` (names a function), `M128` (effects `⊆`, costs `<=`,
    arity), `M142` (signature equality, both directions).
  - the CALL: typed from the slot (`M129` if the place is no pointer); effects fold
    into the hull (`E008` over the slot's words); costs add the slot's bound (`K001`
    over the slot's number); **arity compared with a truncating `zip` (a missing or
    surplus argument reached no rule)**; **`requires` never read; `ensures` never
    narrowed**.

So the grammar already spelled the full contract (`fncontract` in SYNTAX.md §2 had
`requires`/`ensures` since the type was built) while the checker refused two of its
four clauses. The lane closes that gap; it adds no production and no keyword.

## 3. What was built

**Surface / parser / AST: nothing to add.** `fnptr = "fn" "(" … ")" [ "->" typeexpr ]
fncontract` with `[requires] [ensures] effects costs` parses since 2026-08-21, in the
same fixed order and through the same sub-parsers as at an `fn` declaration. The one
surface addition is a sentence, not a production: SYNTAX.md §2 now states the
REFINEMENT DIRECTION -- `requires_type ⇒ requires_f` (contravariant) and
`ensures_f ⇒ ensures_type` (covariant) -- with the two gifts that fail if it swaps.

**Types** (`typen.rs`, `umgebung.rs`): `FnPtrContract` carries `requires` and
`ensures` (`Vec<Pred>`) beside effects/costs, plus `producer: Option<String>`
(`Some(f)` for a value made by `&f`, `None` for a declared slot). Equality stays the
SHAPE: a manual `PartialEq` compares parameters, result, effects and costs, never the
clauses (a `Pred` has no equality, and text equality would make two spellings of one
clause unequal -- the `M142` precedent, stated on the impl).

**Checker** (`m1.rs`):

- Indirect call: `N296` refuses an arity miss (the `M143` reading; reports beside the
  overlap comparison, like `M143`). The slot's `requires` is checked with the weak
  `M115` reading under a second code, `N295` (`requires_pruefen` grew a code
  parameter; the direct call keeps `M115`). The answer is narrowed by the slot's
  `ensures` through the same `bereich_aus_ensures` a direct call uses -- and booked
  nowhere as foreign: the candidates include bodies Gabbro sees, and the refinement
  behind the narrowing is counted (kind `C`), not assumed.
- Producer flow: `passt`'s `FnPtr` arm harvests one record per non-trivial half --
  the `requires` half where `f` carries any, the `ensures` half where the slot
  carries any (both empty is trivially true on both sides) -- and hints `N297` at
  the site. Effects, costs, arity and signature stay DECIDED beside it
  (`M128`/`M142`). Where the producer is unknown (a slot behind a slot) there is no
  one to owe the implication; that is the slot-subtyping question, left open (§7).
- `N037` is retired (issued nowhere since) and removed from its sentence; `247` and
  `248` pin the readings that replaced the refusal.

**Obligations** (`pflichten.rs`): new kind `Art::Vertragsimplikation`, letter **`C`**,
heading "Refinement of a function-pointer contract (slot requires => f requires; f
ensures => slot ensures)". The anchor is the value flow, the wording the consequent
side (the `V` shape: the only other kind where anchor and text part company). The
header line gains a trailing column (`…, {li} lock invariant, {zi} contract
refinement`); the appended position keeps the three manifest readers whole
(`pruefe-manifest.py` and `manifest-lage.sh` match a prefix, `pruefe-zahlen.py`
sums positions `$2..$12` -- all before the new column). The E1 balance (`zeige`)
and the `debug_assert` balance both learned the kind; both had caught every added
kind before any report was read, and the comments book the fifth catch.

**Refinement / Lean channels**: `Material::PointerContract` (both contracts per
half) is refused by name in `refinement.rs` under a new `Reason::HigherOrder`
(`higher-order`; `ALL` 6 → 7; `zaehle-p6.py` gained the row). In `lean.rs` the kind
maps to the existing `LeanReason::OtherValue` -- a function pointer already has no
term there (`FnWert` arm), so no `.lean` constructor is needed and none was touched.
`zaehle-lean.py` gained the `C` row (the fifth list over one set).

**Emitter**: untouched. `fnzeiger_deklarator` reads parameters and result only;
`requires`/`ensures`/`effects`/`costs` lower to nothing.

## 4. Variance (reviewer point 1)

`gift/957`: `hart_senden` demands `b > 0`, the slot nothing. The counted half is
`requires_slot ⇒ requires_f` -- not provable in general -- recorded as `C`, hinted
`N297`, refused nowhere. `gift/958` is the mirror in `ensures` (`true ⇒ result ==
true`). Under swapped logic both implications read `… ⇒ true`: no half recorded, no
hint, both gifts red. The swap is additionally pinned as a mutation each
(`verfeinerung-requires-zeigt-falschherum`, `verfeinerung-ensures-zeigt-falschherum`;
§8). Answer to "refused or counted": COUNTED, in all non-trivial cases -- the
checker decides no implication, not even `A ⇒ A` (example 126 records one on
identical contracts; §6).

## 5. Effects and costs on the pointer type (reviewer point 2)

A comparator talks about its arguments; a driver callback talks about the world, so
the slot carries `effects` and `costs` and the refinement runs over them too -- and
those two halves are DECIDED: `M128` (effects `⊆` with `pure` below everything,
costs `<=`, arity), pre-existing since 2026-08-21, measured again here. No new code
was needed for them, and none was minted: minting one would double-book the defect
against `gift/241`.

Example 127 (`beispiele/127-treiberrueckruf.gab`) is the driver callback: the slot
promises `requires k < 64`, `effects { writes Puffer.slots }`, `costs <= 8 ops`; the
producer keeps the bound and the effect and adds its lock duty; the caller holds the
lock in a `locks` block and calls `t->cb(k)` through the pointer. The caller's hull
and footprint compute over the SLOT's words -- deleting `writes Puffer.slots` from
`bediene` falls at `E008` (checked by hand, 2026-09-14). Ceremony and cost numbers
of existing programs do not move: `kosten` and `zeremonie` reports are byte-identical
before/after on all 105 pre-existing examples (measured, §8); only files spelling
the new clauses can change them.

The callback names the table directly (`beispiele/09` idiom), not through a pointer
parameter: a record holding a pointer-to-table inside a `fn(…)` sorts, in the
emitter's gangs, before the table's own definition, and the emitted struct would
reference a type not yet declared. That ordering is emitter business and was left
alone; the example documents the constraint where it bites.

## 6. Obligation counts before/after (reviewer point 3)

Criterion: what the extension generates, and how much of it the checker discharges.

| file | checker decides | handed to the user |
|---|---|---|
| `126` (sort through comparator) | arity/signature/effects/costs silent (`M128`/`M142` hold); indirect calls type-check; `N295` silent (slot requires empty) | 4 `N` (comparator + sortedness), 5 `V` (five `ordne` calls), **1 `C`** (`ensures` half, identical contracts -- dischargeable on sight) |
| `127` (driver callback) | same decidable sides silent | **1 `C`** (`requires` half: `k < 64 ⇒ Held(PUFFER) ∧ k < 64` -- the holder discharges it by calling under the lock) |
| `957` / `958` | nothing (hints only) | **1 `C`** each, in the half that can fail |
| `956` / `959` / rewritten `247` / `248` | `N295` / `N296` refuse | 0 |
| whole pre-existing corpus (914 files) | codes identical except `111` (+1 hint), `300` (+1 hint), `919` (+1 hint), `247`/`248` (rewritten) | obligations identical except `111` (0 → 1 `C`) |

"Stays in the carried fragment" reads as: every new refusal is a decidable shape
check beside an existing one, and every new undecidable shape is a counted line in
the register -- never a silence. The three extra hints on old files (`111`, `300`,
`919`) are correct harvests on producers that always carried contracts (a `raw fn`
with `requires BootPhase` in `300`); none of the three files changes verdict.

## 7. What is NOT carried (open halves, each booked)

1. **`Held` at an indirect call.** A `locks` effect cannot stand at the type
   (`N036`), and no pass holds a `Held` requirement at an indirect site either
   (`geteilt` resolves direct callees by name). Example 127 states this in its
   header: the slot repeats only `k < 64`, and the counted `C` implication
   (`k < 64 ⇒ Held(PUFFER) ∧ k < 64`) is exactly the holder's discharge. Closing it
   needs an indirect `H005` -- a new rule with its own measurement, not a line here.
2. **Slot-subtyping.** A slot behind a slot (no named producer) owes no `C` entry;
   the implication between two slot contracts is undecided everywhere. The decidable
   sides still hold on every flow.
3. **Aliasing through an ascribed `let`.** `let g : S = &f` stores the DECLARED type
   (flow-insensitive locals, the `M140` principle), so the producer is forgotten past
   the binding -- the flow that wrote it was already harvested. Without an
   ascription the producer travels with the value. Same class as `V`'s documented
   undercounts.
4. **The model side.** The Lean signature needs a contract field on the pointer type
   (the `D.sig`-neighbour: what `KandOk` quantifies over gains the `requires` /
   `ensures` the checker already reads). Named here, built by the later Opus task;
   no `.lean` file was touched.

## 8. Verification ledger

- `cargo build`: clean (one pre-existing `private_interfaces` warning in
  `certstmt.rs`).
- `cargo test --no-fail-fast`: **942 passed, 0 failed** (936 at HEAD + 6 new in
  `tests/zeigervertrag.rs`).
- New tests pin: `N295` exactly-once on `247`/`956`, `N296` exactly-once on
  `248`/`959`, the `N297` hint + the worded `C` line on `957`/`958` (direction
  guards), the green check + hint + `C` line on `126`/`127` (incl. the lowered
  `bool (*cmp)(uint32_t, uint32_t)` in 126's C).
- Codes before/after over 914 corpus files (baseline worktree at HEAD vs this
  tree): identical except the four intended (§6). Full outputs saved beside the
  run, not in the tree.
- Obligations before/after over all `beispiele/` + `messung/` units: identical
  except the appended `0 contract refinement` column and `111` (0 → 1 `C`).
- Emission: byte-identical C on **all 107** pre-existing examples (both binaries);
  `126`/`127` emit and `cc -std=c11 -Wall -Wextra -Werror -fsyntax-only` accept at
  `-O0` and `-O2`; hint-gifts `957`/`958` emit and compile (by design, the
  `916`/`918`/`919`/`930` precedent: hints never blocked emission).
- `kosten` / `zeremonie`: byte-identical on all 105 pre-existing examples.
- `./emission-pruef`: ALL PASS (252 von 252). Note: stage 9 counts only
  `git`-tracked files, so the two new examples and two emitting gifts move the
  marks only after this lane is committed -- for the merge: `MARKE_EMIT` 107 →
  **109**, `MARKE_EMIT_G` 12 → **14**. Lanes do not book these marks; the numbers
  are measured here for the merge to re-measure.
- Guardians: `pruefe-kennungen` ALL PASS (393 codes: 391 + 3 − 1 retired `N037`);
  `pruefe-vergabe` unchanged (32 candidates); `pruefe-saetze` green (393 codes,
  160 sentences, 55 without -- the new `m1.fnzeigervertrag`, the rewritten
  `namen.fnzeigervertrag`); `pruefe-widerruf` ALL PASS; `pruefe-konstrukte` clean;
  `pruefe-manifest` green; `pruefe-englisch` ends where HEAD ends (rc=1,
  pre-existing abort after the language section; German counts frozen: 28 feeders,
  7940 comment lines); `pruefe-klauseln` VERALTET as at HEAD (pre-existing; the one
  new homonym my first draft added, `Zeigervertrag::slot`, was renamed away --
  70 = 70).
- Mutation catalog: 409 → **413**, all four new anchors grip (verified by
  re-implementation of the anchor count: 386 von 413 grip; the 27 dead are the 27
  dead at HEAD -- 17 `lean-*`, 10 elsewhere -- pre-existing weathering). The full
  run aborts before measuring (`27 von 413 Ankern greifen ins Leere`, same at
  HEAD), so the four new mutations were validated targeted instead: each applied
  by hand turns `cargo test --test beispiele --test zeigervertrag` red (the gift
  arm in all four cases), each restored byte-identically after.
- `miss-grammatikdeckung.py` moves, unpinned: `fnptr.requires`/`fnptr.ensures`
  read REFUSES (via `N037`) before this lane; they now read CARRIES-or-better
  (accepted, C-identical, no new obligation on the bare probe pair). No guardian
  pins that table's verdicts.

## 9. Records moved (registers the guardians read)

- Codes: `N295` (indirect `requires`), `N296` (indirect arity), `N297` (hint:
  `C` recorded); `N037` retired (issued nowhere). `N298`/`N299` stay reserved and
  unassigned. Sentences: new `m1.fnzeigervertrag`; `namen.fnzeigervertrag` and
  `m1.fnzeiger` rewritten around the retirement.
- Gifts: `956` (`N295`, ranged spelling), `957`/`958` (`Hinweis N297`, the two
  direction halves), `959` (`N296`, minimal); `247` → `N295`, `248` → `N296`
  (same numbers, new readings -- the old refusal is gone, the files pin what
  replaced it).
- Examples: `126` (sort through a comparator contract), `127` (driver callback
  with world effects).
- Manifest: kind letter **`C`** ("contract refinement"); header column appended
  last; `zaehle-p6.py` + `zaehle-lean.py` rows added.
- Mutations: four (`indirekter-ruf-prueft-requires-nicht`,
  `indirekter-ruf-zaehlt-stelligkeit-nicht`,
  `verfeinerung-requires-zeigt-falschherum`,
  `verfeinerung-ensures-zeigt-falschherum`), all caught targeted.
- Numbers with guardians behind them: TODO `Sätze über 393 Codes` / `160 Sätze`
  (was 381/157, drifted since 2026-09-14); TODO `Mutationskatalog: 386 von 413`
  (was 392/403); README corpus row (109/668/942) and mutation rows (386/413,
  413). The pre-existing drifts found en route (kennungen 381→391 at HEAD,
  tests 891→936, the `--anker` speech-probe environment failure also failing at
  HEAD) are booked as found, not folded silently.

## 10. The one repair this lane had to make en route

`umgebung.rs` resolved named types (`typen`) before the carrier walk registered
tables, so an alias-held `ptr<…> Table` resolved to `Unbekannt` (and an alias-held
`index into Table` to the full word) -- the p8-hole class one map further out. It
was invisible until an `N297` hint spelled `ptr<…> ?`, and `M142` compares through
`Unbekannt` in silence, so the hole sat in the decidable check too. The repair is a
registration pre-pass (`tabellennamen`: names + counts only, sorted; fields still
resolve in the carrier walk, which overwrites both maps). Before/after over the
914 files: no verdict moves except the lane's own four (§6) -- no pre-existing file
relied on the silence.

## 11. What the Opus task needs (model side)

A contract field on the pointer type in the Lean signature: `requires`/`ensures`
beside the signature the value already carries (`Ty.fnptr sig`, `D.sig f = sig`),
so that `KandOk` (candidates keep the caller's footprint) and the
`RespektiertRahmen` handler class quantify over contract-respecting callees with
their logic, the way `KoerperGutS` already quantifies over handlers. The checker
side hands over: per slot, the two clause lists; per producer flow, the counted
implication (kind `C` material: both contracts, per half). Nothing in `.lean` was
touched from here.
