# MUSE-REPORT-1041: Exact review of author 891 (Optimiser rule: CMOV selection rule)

CANDIDATE: 891 cc4a85e52f4d9b147e71f4f87ddfb1c960f9cf30
VERDICT: ACCEPT

Scope of acceptance (unchanged substance): bounded; layer-A rule lemma only,
no byte/hardware/TSO/budget-machine claims.

## Method

- Verified clone `/home/simon/Dokumente/gabbro-muse/a1041`, branch `muse/1041`; HEAD
  `b040b155159f47629542b0083e2f0a8a607f2b4c` equals the snapshot base exactly.
- Inspected the exact pinned snapshot: `SNAPSHOT.json` (1 entry, clean:true, exactly the
  3 files `MUSE-REPORT-891.md`, `grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/OptCmovSel.lean`),
  `OWNER-TASK.md`, `MUSE-REPORT-891.md`, `PATCH.diff` (614 lines), the full candidate file
  (491 lines), and `BUILD-EVIDENCE.json` (16 commands).
- Cross-checked every reused name against the base tree at the pinned base:
  `ControlFlow.cmovAnwenden` / `cmovAnwenden_flags` / `cmovAnwenden_speicher` /
  `cmovMemSchritt`, `ConditionalMove.cmovAnwenden_genommen_wert` /
  `cmovAnwenden_nicht_wert`, `witTrue`/`witReg`, `ReferenzB` (`refD`, `refEin_schreibt`,
  `refP`, `refO`, `refSp0`, `initB`, `MB`, `refB_erreicht`, `refB_schreibt`, `keinRuf`).
- Checked the Intel SDM reference snapshot (`REFERENCES.json`, edition 325462-093US):
  CMOVcc description lines confirm the load-bearing fact (see below).
- Checked DESIGN alignment: `DIRECT-COMPILER-DESIGN.md` §3A tile (lines 343-349) and the
  CMOVcc row (line 314); `grammatik/OPTIMIZER.md` has no CMOV-specific hard-gate text,
  consistent with the author's note that §7 holds no explicit CMOV-selection row.
- Owns only this report; no source file was created, modified, or rebuilt here.
  `./lean-bau` in this clone (base without candidate): green, 510 jobs (see below).
  `./lean-probe` on the candidate file was not re-run here: it would require placing the
  file under `grammatik/` (unowned path, also rejected by the lane permission gate), and
  the module name would not resolve from the snapshot path. The merge gate re-checks
  build and axioms mechanically.

## Architecture review (byte forms, operands, faults, memory, gates, canonical execution)

- Byte forms / REX / widths: the candidate claims and proves NOTHING at byte level
  (no `Befehl`, no `Codec` row, no encoding) and its CUTS say so explicitly. Correct
  bounding: CMOVcc has no pilot encoding, so a layer-A source/machine-value lemma is
  the most that can be claimed here. No invented byte semantics found.
- Operands: the modelled select is `cmovAnwenden` (register-only, `dst src : Register`),
  matching the DESIGN "register-only CMOV first" order. Destination/source/implicit
  operands are exactly the canonical function's; flags are read, never written
  (`cmovAnwenden_flags` by `rfl`); no memory operand exists in the modelled form.
- Flag semantics: `bedingung c0 s.flags` is reused, never re-decided. Taken/untaken
  equations come from the accepted `ConditionalMove` lemmas (exact names verified in base).
- Pre-fault effects / memory order: the load-bearing refusal `cmovSelVerweigert_speicher`
  (`nurRegister = false` forces admission `= false`, default stays branch) is
  architecturally CORRECT. Intel SDM Vol. 2A 3-157: "CMOVcc loads data from its source
  operand into a temporary register unconditionally (regardless of the condition code
  and the status flags)". A memory source is therefore read (and may fault) even when
  the condition is false. The canonical model agrees: `cmovMemSchritt` reads FIRST
  through permission-checked `read64` and keeps the fault on BOTH paths. Refusing to
  select the memory form is sound (a refusal to optimise, never a warning) and is the
  precise reason the register-only lemma cannot be misapplied to a memory site.
- `fehlerfrei = false` refusal covers division, faulting loads, trap-capable FP behind
  the site: no faulting form is speculated above its guard. Both arms of the proved
  fragment are literals, so the proved case cannot fault by construction.
- Feature/MXCSR/interrupt gates: none modelled, none claimed. `gleicheRundung` admission
  plus its refusal lemma bound the FP scope; the float conjunct is a `gleitPasst`
  congruence (moving the exact pattern, no new rounding), which is all the admitted
  register-only case needs. No silicon IEEE claim is made.
- TSO/atomicity/concurrency: `cmovAnwenden_speicher`/`_flags` frame is reused (`rfl`
  facts); both source arms are literals and the condition reads no places (`hc0`), so
  the rewrite adds no shared access. No TSO/GX bridge is claimed (CUTS leaves it OPEN).
- Canonical interaction: conjunct (2) equates `execEnd` outcomes of `branchEnd` vs the
  admitted `cmovWahlBlock` (same constructor/worlds/envs), proved by `rw` on `hc0`,
  literal-`orte` facts, `lese_leer`, `hc`, then `cases b`. This is a genuine outcome
  preservation over the real `exec`/`execStmt`/`execEnd`, not a restated premise.

## Premise use, witnesses, mutations, guarantee strength

- All premises of `OptCmovSel_verbindung` are used: `hz` (choice rewrite), `hc`/`hc0`
  (condition value/places), `hbed`/`hsrc`/`hdst` (placement, via taken/untaken lemmas),
  `hlink` (word/image link), `hW` (width bounds), `qa qb lo hi` (float conjunct).
  No `intro _`, no `have _ :=`, no Prop-typed premise, no conclusion-restating-premise,
  no quantified-away contract values. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`
  (grep-verified on the exact file; remaining hits are prose "admitted"/"admission").
- TARGET witness `OptCmovSel_verbindung_zeuge` (plus `cmovWahl_waehlt_zeuge`) is JOINT and
  non-degenerate: `refD` with `(vertragVon refD refEin).schreibt () = true` (a table some
  function writes) beside reached run `MB` (`refB_erreicht`) with
  `MB.speicher.slots () 0 () != refSp0.slots () 0 ()` (memory-changing). Source
  condition `.wahr`, target `witTrue` (taken arm 20 in `rbx`), all side goals `by decide`
  / `rfl` — the same shapes the base already decides (`cmov_witness_unterscheidet`).
  Inhabitation rule satisfied.
- Negative mutations present: `probe_cmovSelZulassen_speicher` and
  `probe_belegVerweigert_speicher` refuse the memory-tainted certificate; four further
  refusal theorems (fault/predictable/expensive/stale/cross-scope) plus the all-true
  positive probe. Default stays branch everywhere.
- No guarantee weakening, no desired-simulation assumption: placement facts
  (`hbed`/`hsrc`/`hdst`/`hlink`) are per-site validator premises the lowering lane must
  discharge (CUTS says so); they are not assumed as a global simulation. Nothing derives
  `ensures`; no refusal becomes a warning.
- CUTS/claim boundary is precise: no bytes/codec, no silicon correspondence, no TSO/GX,
  no ABI/loader/timing, budget only as same-shape source accounting with the formal
  level-(c) machine-work bound OPEN, lowering correspondence per-site. The report's
  prose matches the formal statements with one imprecision (see Blemishes).
- Scope hygiene: patch touches exactly the 3 snapshotted files; `Grammatik.lean` diff is
  one appended import line. No diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes,
  no source/checker/Spec/goal/emitter edits, no friend-reserved optimiser files.

## Axioms and build

- BUILD-EVIDENCE (author clone, pinned base): `./lean-probe` final states
  `== 0 error(s) ... exit 0` after two red intermediates (unknown identifiers from a
  truncated lemma name; a `vertrag`-binder scoping error; a `gleitPasst`-as-Prop error —
  all repaired in later commits, final file read here contains the repaired forms).
  `./lean-bau`: `== exit 0; 0 error line(s)`, `Built Grammatik (511 jobs)`.
- Printed axiom dependencies visible in evidence are all within
  `[propext, Classical.choice, Quot.sound]` (many `none`/`[propext]`/`[propext, Quot.sound]`).
  The two main-theorem lines are cut by the harness 2000-char line cap
  (`[propext, Classical.choic...`), but non-standard axioms are excluded by construction:
  the file declares no axiom and uses no `sorry`/`admit`/`native_decide`, and all imports
  are standard-green base modules. Merge gate re-verifies `#print axioms` mechanically.
- This clone (reviewer, base without candidate): `./lean-bau` →
  `Build completed successfully (510 jobs)` (tail shows only axiom-info lines, no errors).

## Blemishes (not repairs)

1. Commit `2898542a` message ("certificate: ...") describes the neighbouring commit's
   content (stale message file reused; author discloses it, amend denied by lane gate).
   Cosmetic; content verified correct.
2. File §6 comment says budget accounting is unchanged with "same block shape" — the two
   blocks differ in shape (`ite`-cons-`leave` vs `bind`-`leave`); what is proved is
   `execEnd` outcome equality, and the machine-work bound is OPEN per CUTS. One-word
   prose fix for the integration owner ("same outcome", drop "same block shape").
   The formal claim is unaffected.
3. `gleicheRundung` necessity is argued by refusal only (no cross-scope counterexample
   lemma). Adequate for a layer-A admission gate; noted for the lowering lane.

## What remains open (unchanged from candidate CUTS)

No CMOVcc pilot encoding/bytes; no silicon correspondence; no TSO/GX bridge; no
ABI/loader/timing; formal level-(c) machine-work bound; per-site lowering placement
(`hbed`/`hsrc`/`hdst`/`hlink`) for the validator/lowering lane.

## Task feedback

The owner task cites "premises from the DESIGN section 7 row". The DESIGN §7 table has
no explicit CMOV-selection row; the implemented premises correctly come from the §3A
CMOV tile (unpredictable AND cheap AND fault-free unselected side, register-only first)
plus the §7 flags-peephole pattern (admission in register, flag-liveness). The author's
report already discloses this. Suggest the next task text cite §3A directly.
