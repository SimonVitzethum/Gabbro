# MUSE-REPORT-254 — exporter width: biggest refusal class first (TODO §1 residue)

Lane 254 (Rust, exporter width). Branch `muse/254`.

## Census re-measurement (baseline moved — reported before building)

Lane 207's census (117 files, 15 export) has moved: the corpus is now
**127 files** (+10: `147`–`156`, all newer than 207). Re-measured with the
unmodified tree before any edit:

- **Exports: 15, the identical set as 207** (104, 108, 109, 118, 119, 120,
  121, 124, 130, 15, 16, 34, 62, 69, 73).
- First refusals: **LG001 x74** (was 71), LG002 x21 (was 19), LG003 x1
  (unchanged, file 131), LG004 x10 (was 5), LG005 x6 (was 4), **LG006 x0**
  (was 2 — 207's widening holds: files 19 and 46 now refuse LG005
  `unknown name passes`, as 207 reported).
- The +10 new files refuse: 147/148 LG004 (fall off with a result),
  149/155/156 LG001 (`assume`), 150/152 LG002 (array static), 151 LG004
  (int index), 153/154 LG004 (top-level `alloc`).

LG001 is still the biggest class, so it came first.

## What was done

**1. LG001 subclass survey (all 74, by refusal message).** Every subclass
needs Lean-side G-forms — none is pure-exporter work:

| subclass | files | G-form missing (model remainder) |
|---|---|---|
| `assume` (named assumptions) | 10 | `D.Annahme` + `Stmt.forever`/`retires` export |
| linear/ghost/order marks | 10 | `D.Marke` family (`konsumiert`/`produziert`, `advances`/`retires`) |
| foreign bodies (`is not impl`: extern/syscall/axiom/entrust) | 10 | `D.Ax` + `Stmt.axiomCall`/`bindAxiom` incl. `hd`/`hgd` proofs |
| `atomic` | 8 | `Glob atomar` + `publish`/`awaits`/`exchange` |
| `device` | 7 | `D.Reg` + `regLies`/`regSchreib` |
| table `tree`/`ops`/invariant/`backed` | 7 | walk lowering, table `D.Inv`, ops-generated functions |
| `lock` masked/shared-hold (`maskiert`, `geteilte_haltezeit`) | 4 | masked-lock semantics — **lane 255 territory, not touched** |
| `format` | 4 | `Tab` count-1 + `Block.pruefung` + `Expr.leseBytes` |
| fn `arch`/`deadline` + `asm` body | 3 | asm-body semantics (an `arch` ignore alone strands on `= asm`) |
| misc (`use`, `when`, `requires profile`, `section` at static, `accumulates`, `group`, start-guard shape) | 11 | linking/`D.Annahme`/placement/`D.Inv`/starts model work |

**2. One buildable widening attempt: bit-range alignment (61, 151).**
`beispiele/61` (`let a` exceeds annotation) and `beispiele/151`
(int index) are refused only because the exporter's bit-op intervals are
coarser than the checker's (`typen.rs::bitweise/schiebe_*`, `umwandlung_ruf`
K3, `m1.rs` `BitNicht`). I implemented the alignment (band `min`,
bor/xor mask, shr narrow, exact `~`, conversion-kept range) — both files
exported — and `./lean-probe` REJECTED both (7 and 10 errors).

Root cause (the finding): **the exporter's belief must equal the
elaborated term type.** The `let` ascription prints the belief, but the
term's type is computed by the MODEL's constructors from operand types
(`Zahl.band` yields `Zahl 0 h1`, `shr` yields `Zahl 0 h1`,
`bor`/`bxor` yield `Zahl 0 (2^w - 1)`). A narrowed belief ascribes a type
the term does not have (61: expected `.int 0 131070`, has
`.int (0+0) (4294967295+4294967295)`); and no `weiter` can repair it,
because the needed inclusion is FALSE at type level — only value-level
band/shift semantics justify it, which `by decide` cannot see. Closing
61/151 needs narrowed MODEL result types with redone proofs
(`Typen.lean`: `Zahl.band` → `Zahl 0 (min h1 h2)` via
`Nat.and_le_left/right`; `Zahl.shr` → monotone div/pow bound;
`Zahl.bor`/`bxor` → mask bound; exact complement via xor-ones;
`Syntax.lean`: the `Expr` result indices mirroring them). Specified
exactly instead of half-built, per the task. The narrowing was reverted.

**3. What landed (sound subset, belief == term type preserved):**
`crates/gabbro-check/src/lean_g.rs` —

- `breite_weiter()` (new helper): keep the left storage width where the
  result still fits (`0 <= lo`, `hi < 2^w`);never claimed past the width.
  Wired into `tr_bitop` (band/shr/shl results), `tr_binaer`
  (Plus/Minus/Mal results). Ranges untouched — terms elaborate exactly as
  before, widths agree with the checker's common form on every accepted
  program (literals take the other's form; disagreements refuse before
  reaching here).
- `tr_index`: integer-typed names (parameters, `let`s) accepted where
  their range fits the table, via the pre-existing `fit` (`weiter`
  coercion, proofs decided in Rust; over-wide keeps LG004).
- `tr_rest` `Let` arm: pushes the computed range with the ANNOTATED width
  (the checker types later uses by the annotation — `lage.lokal` keeps
  `ziel.unwrap_or(wert)` — so `~`/bit-op widths agree with the checker by
  construction; the range stays a sound over-approx the annotation covers).
- Module-doc ledger: one sentence on the index widening.

`crates/gabbro-check/tests/lean_g.rs` — 7 tests: positives
`accepts_int_typed_slot_index` (exact-fit bare var + narrower `weiter`
arm), `accepts_complement_over_let_bound_band` (`.bxor 16`),
`accepts_shift_through_unannotated_let` (`.shr 32`); poisons
`refuses_over_wide_int_index`, `refuses_complement_over_literal`,
`refuses_bool_slot_index`; `bit_range_remainder_stays_refused` pins 61
(LG004 `` `let a` exceeds its annotation``) and 151 (LG004
`index w in lies_byte`) to the model work above.

## Verification

- `./cargo-pruef`: `== exit 0; failing tests: 0` (incl. the 7 new tests).
- `./lean-bau`: `== lake exit code: 0`, `== 0 error line(s)`.
- `./emission-pruef`: `== EMISSION: ALL PASS` (MARKE_EMIT untouched).
- `pruefe-genlean.py`: 0 of 2 byte-identical — **pre-existing red**
  (lane 204's `obligations --g` RELEASE-OBLIGATIONS rows were never
  regenerated into `GenOblig104/108.lean`); my `obligations --g` outputs
  for 104/108 are byte-identical to baseline, so not worse by one byte.
  Regenerating the committed files is Lean-side and out of scope.
- Corpus export diff: **15 → 15, all 15 byte-identical**; all
  `obligations --g` outputs for exporters unchanged. Within-LG004 move:
  151's first refusal moved `index w in lies_wort` → `index w in
  lies_byte` (the param-index now translates; the derived `let w`
  needs the model narrowing). Zero gained exports, honestly reported
  (lane-207 precedent).
- The three new-shape snippets were additionally exported via CLI
  (checker-clean, since `lean-g` checks first) and each elaborates with
  `./lean-probe` exit 0, 0 errors (probe files in `$TMPDIR`, not
  committed). `obligations --g` shape verified on all three.

## Honest count

Gained exports per class: **0**. Moved between refusals: LG006→LG005
(19, 46 — lane 207's, holding) and one intra-LG004 move (151, this lane).
What stays refused, and where: LG001 x74 (table above), LG002 x21
(wrapping/float/array-statics/fn-ptr fields/record values/non-normal
address spaces — all `Ty`-level model work), LG003 x1 (131,
call-in-contract), LG004 x10 (125/147/148 fall-off — unbuildable by
design, inventing a return value; 98/99/153/154 top-level `alloc` —
needs an `Endblock` former; 61/151 — the model narrowing above; 110
top-level `bindCall` — same class), LG005 x6 (non-numeral/array consts,
`passes` invariants — plus `+=` behind 19/46).

## What remains open / believed-wrong in the task

- The model-narrowing lane (`Typen.lean`/`Syntax.lean` result types for
  `band`/`shr`/`bor`/`bxor`/complement, proofs redone) is the priced
  follow-up: with it, this lane's reverted beliefs become term-correct
  and 61 + 151 export (+2). The exporter half (widths, `tr_index`,
  hybrid) is already landed and tested.
- "Keep `pruefe-genlean.py` green, no exceptions" was unsatisfiable on
  arrival (red since 204's merge); it needs a regeneration lane with
  Lean scope, or an explicit waiver.
- No N codes (none added — widening removes refusals), no gifts, no
  examples (none taken; free stock from 157+ untouched). Touched only
  `lean_g.rs`, `tests/lean_g.rs` (+ this report). No checker passes,
  no `emit.rs`, no Lean files, no `MARKE_EMIT*`.

## Names added

Rust (`crates/gabbro-check/src/lean_g.rs`): `breite_weiter()`;
widened `tr_bitop`, `tr_binaer` (±/* arms), `tr_index`, `tr_rest`–`Let`.
Tests (`tests/lean_g.rs`): `accepts_int_typed_slot_index`,
`accepts_complement_over_let_bound_band`,
`accepts_shift_through_unannotated_let`, `refuses_over_wide_int_index`,
`refuses_complement_over_literal`, `refuses_bool_slot_index`,
`bit_range_remainder_stays_refused`. No Lean theorems added (no rule-13
witnesses owed); `#print axioms` N/A — Rust lane.
