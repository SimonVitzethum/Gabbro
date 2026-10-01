# MUSE-REPORT-350: Organisation plan C6 — AtomicPayload

Lane 350, branch `muse/350`. Owns ONLY `grammatik/Grammatik/X86/AtomicPayload.lean`,
one additive import at END of `grammatik/Grammatik.lean`, and this report.
Reviewer: lane 388.

## What was done

New file `grammatik/Grammatik/X86/AtomicPayload.lean`
(namespace `Gabbro.Grammatik.X86.AtomicPayload`, ~360 lines): the checker half of
QUELLBRUECKE section 3.3 (shared atomics) plus the duty-side audit of the atomic
fragment. Everything is generic over every declaration/program; no source admission
was tightened, no canonical vocabulary edited, no second IR/executor built.

Reused (never redefined): `AkzeptiertSpecX`/`FussSX`/`GeteiltV`/`GeteiltA`/`LogikPflichtA`
(`Zielsatz/Spec.lean`), `HavocA`/`havocA_mono`/`havocA_id`/`idA` (`Speichermodell/AtomarSem.lean`),
`KoerperGutSA`/`InvGutSA`/`InvGutGrundA` + mono lemmas (`Speichermodell/AtomarRec.lean`),
`vertragsFreiB`/`vertragsFreiB_ok`/`geteiltVB` (`Zielsatz/AtomarAkzeptiert.lean`),
`atomarB_iff` (`Speichermodell/AtomarZeuge.lean`), canonical `istIn`/`istIn_iff`,
`waechterVon`/`waechterVon_mem`, `fussOrteG`, `invOrteP`, `PaarungAusgenommen`,
`AtomarAusgenommen`. The bridge `nutzerA_aus_quelle` side was audited, not edited.

### New definitions

- `atomarFussB (P) (fs) (f) (c) : Bool` — decided footprint-membership check for an
  admitted shared atomic at one footprint: `istIn (fussOrteG P f) c && atomarB c &&
  (waechterVon c).isEmpty && vertragsFreiB P fs c`. (`geteiltVB` decides admission
  WITHOUT the footprint conjunct; the footprint side is the new checker-half piece.)
- `pD : Deklaration` — `nD` with one publication (`konfig` atomic publishes `zaehler`
  made non-atomic). No in-tree fixture has a payload (`nutzlast` is empty everywhere);
  this is the smallest declaration that has one. Only `atomar`/`nutzlast` move, plus a
  re-supplied `ggeteilt_bewacht` (its TYPE mentions `atomar`, so `nD`'s proof term does
  not fit; new proof from the everywhere-false `ggeteilt`).

### New theorems (each premise used by its proof)

1. `atomarFussB_ok` — check true implies footprint membership, `AtomarAusgenommen`,
   guard absence, `VertragsFrei`. Witness `atomarFussB_ok_zeuge`.
2. `geteiltV_von_atomarFuss` — check + full enumeration + `¬ GetrenntR P ws c` gives
   `GeteiltV P ws c`. Non-locality stays an explicit Prop premise (no syntax Bool
   decides the call closure). Witness `geteiltV_von_atomarFuss_zeuge`.
3. `vertrag_erwaehnung_verweigert` — PROVED Prop refusal: a carrier in any `requires`/
   `ensures`/owed invariant is neither contract-free nor admitted. Witness
   `vertrag_erwaehnung_verweigert_zeuge` (on `AtomarXZeuge.vP`, `kern` ensures
   `konfig == 3`).
4. `vertrag_bool_verweigert` — same refusal as Bool: both `vertragsFreiB` and
   `atomarFussB` are `false` under a full enumeration. Witness
   `vertrag_bool_verweigert_zeuge`.
5. `audit_pflicht_deckt_aufgenommen` — duty-side audit: `LogikPflichtA` over `GeteiltA`
   transfers to `GeteiltV` via the mono lemmas (narrowing, never re-proving, never a
   guessed contract). Witness `audit_pflicht_deckt_aufgenommen_zeuge` (via `n1_logikA`).
6. `audit_beobachtung_menge` — rely policy: an atomic environment preserves the whole
   trace and every non-rely carrier (observations as SET, never narrowed). Witness
   `audit_beobachtung_menge_zeuge` (identity environment in the fixture rely class,
   preservation firing at every read list/world).
7. `nichtatomar_verweigert` — a non-atomic carrier is refused everywhere (not excepted,
   check false, never admitted). Covers every publish payload (payloads are non-atomic
   per the P3 verdict reading in `ausgenommenB`). Witness `nichtatomar_verweigert_zeuge`.
8. `nutzlast_braucht_restbeweis` — a publish payload is not an admitted atomic even
   beside an atomic publication; the hand-off needs its residue proof. Witness
   `nutzlast_braucht_restbeweis_zeuge` over `pD`.
9. `atomar_nichtleer` — shared non-degeneracy: `hauptA` writes `tabA`, and a W run from
   the zero memory reaches `konfig = 3` (start memory has 0): a memory-changing run
   through the guard discipline (no lock anywhere; the atomic carries the sharing).

Every `_zeuge` instantiates ALL premises jointly on concrete values. Run-statement
witnesses (memory-changing reached run) are at `nP`; the pure checker-side refusals
(`vertrag_*` on `vP`, `nutzlast_*` on `pD`) carry the written-table leg, documented in
the file: they share `nD`'s tables/functions, and the run leg over those is witnessed
at `nP`.

## Verification

- `./lean-probe grammatik/Grammatik/X86/AtomicPayload.lean`: 0 errors.
- `./lean-bau`: exit 0, 0 error lines, `Build completed successfully (386 jobs)`,
  `Built Grammatik.X86.AtomicPayload`, `Built Grammatik`.
- `#print axioms` for all 8 main theorems: subsets of
  `[propext, Classical.choice, Quot.sound]` (most `[propext]` or `[propext, Quot.sound]`;
  full list in build log). No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
- `gabbro_ziel` axiom probe (`./lean-probe .../BeweisAtomar.lean`): still exactly
  `[propext, Classical.choice, Quot.sound]` (also `gabbro_ziel_gx`, `gabbro_ziel_sc_aus`,
  `gabbro_ziel_verbund*`).

## What remains OPEN (also as CUTS in the file)

1. Per-access x86-TSO refinement into W/GX (lane 274 business); no multi-byte
   atomicity / LOCK/RMW correspondence claimed.
2. Source bridge constructing duties for atomic-bearing units from `Pflichten src`
   (`nutzerA_aus_quelle` covers atomic-free units only); this file audits the duty to
   discharge, it does not construct it.
3. Plain-payload hand-off residue proof.
4. Shared IR (lane 287) consumed as pending interface, never invented.

## Notes for the reviewer (things in the task I read strictly)

- "Decided footprint-membership checks" (plural): delivered as ONE check with four
  decided conjuncts plus the per-conjunct projections of `atomarFussB_ok`. The
  footprint conjunct itself is the canonical `istIn (fussOrteG P f)`, deliberately not
  re-wrapped: a second name for the same Bool would be a duplicate register.
- `n1_konfig_geteilt.1.2.2` is used as the `¬ GetrenntR` witness component; the
  non-locality fact itself is NOT re-proved (it is a Prop over the call closure).
- Name trap found while working: `vP` over `vD` sits directly in `Gabbro.Grammatik`
  (`ZielOrtVollZeuge.lean`), so the bare name does NOT mean the atomic fixture's `vP`;
  the file qualifies `AtomarXZeuge.vP` / `AtomarXZeuge.vertrag_atomar_echt` explicitly.
- `omit [DecidableEq D.Fn] in` must precede the docstring (Lean parses `docstring +
  omit` as an error); the file follows the `AtomarAkzeptiert.lean` order.
- `pD`'s `ggeteilt_bewacht` cannot reuse `nD`'s proof term (dependent field type
  mentions `atomar`); proved from the everywhere-false `ggeteilt` instead.
- No TSO/flag/division/float/cost content was manufactured: the file makes no claim
  about target bytes at all, per the safety corrections (refusal Bool = admission,
  never a hardware fault).

## Repair attempt after the failed integration gate (2026-10-01, ~15:00 CEST)

### Gate evidence (from the merge log)

- Integration `lake build` failed with exit 1; the only failing target was
  `Grammatik.X86.AtomicPayload`:
  `lean::exception: failed to create thread`, `Lean exited with code 134`.
- All neighbouring targets built (the log shows the CostSummary theorems with standard
  axioms); nothing in the log points at a type error or a failed proof in this module.

### Local reproduction: the failure is content-independent

Every check below ran in this clone (`/home/simon/Dokumente/gabbro-muse/a350`,
branch `muse/350`):

1. `./lean-probe grammatik/Grammatik/X86/AtomicPayload.lean` gives exit 134 with the same
   `failed to create thread` and no error-location lines (crash, not a proof failure).
2. `./lean-probe grammatik/Grammatik/X86/Regionen.lean` (an untouched master file, not
   owned by this lane) gives exit 134 with the identical crash. Module content is not
   the cause.
3. A trivial file (`def hello : Nat := 42`) through the queued path
   (`lean-slot bash -c "lake env lean <file>"`) gives exit 134 with the identical crash,
   ending in `Aborted (core dumped)`.
4. The same trivial file through the direct toolchain (`lake env lean <file>`, project
   toolchain 4.33.1, no queue) gives RC=0, `does not depend on any axioms`.
5. `lean --version` (4.34.1) and `lake env lean --version` (4.33.1) both work.
6. Inside `lean-slot`, even `ulimit -u` reads fine (126697), so it is not the process
   count rlimit; swap sat above 90% full at peak (9008/9011 MiB) and crashes persist
   after it eased to ~4600/9011, so it is not only momentary RAM either.

Bisection conclusion: the crash follows the `lean-slot` queue wrapper
(`/home/simon/Dokumente/gabbro-muse/bin/lean-slot`, outside every lane clone), not any
file content. A content-free file crashes under it and passes without it.

### Module repair attempted, then reverted

- Change tried: factored the two identical `by decide` evaluations of
  `atomarFussB nP nFs NFn.hauptA (.inr NGlob.konfig) = true` (one each in
  `atomarFussB_ok_zeuge` and `geteiltV_von_atomarFuss_zeuge`) into one shared lemma
  `atomarFussB_nP`, halving that evaluation. Logically identical; no statement changed.
- Verification of that change was IMPOSSIBLE: every `./lean-probe` and `./lean-bau` goes
  through the broken slot and crashes even on trivial files.
- Per HARD RULES 8 (never commit an unverified build) the change was REVERTED
  (`git checkout -- grammatik/Grammatik/X86/AtomicPayload.lean`). This report commit
  therefore leaves `AtomicPayload.lean` byte-identical to the reviewer-accepted state
  (commit `67dd9fd1`); only this report changed.
- The factoring can be re-applied in minutes once the slot works; it changes no
  statement, so it needs a green build, not a new logical review.

### What this means for the gate

- No logical defect in the owned module is indicated by the evidence. Re-gating the
  unchanged accepted content after the queue infrastructure recovers should pass.
- Concrete blocker for the coordinator: the queued-Lean infrastructure on this machine
  is broken under today's 40-lane load for ALL lanes (any lane's `./lean-probe` or
  `./lean-bau` crashes the same way right now). The `lean-slot` layer needs repair, or
  lane load needs to drop, before any Lean gate can pass. Each crash also dumps core;
  at 40 lanes this accumulates.
- A fresh independent review is still required for the changed commit (this report).
  Reviewer 388: the Lean content is unchanged since your acceptance; what changed is
  this report plus the environmental finding above.

### Verification status of THIS commit

- `./lean-probe` / `./lean-bau`: NOT RUNNABLE (slot crashes on all inputs, see above).
- Last known green of the committed Lean content: `./lean-bau` exit 0, 0 error lines,
  386 jobs, `Built Grammatik.X86.AtomicPayload` (this clone, before the gate; recorded
  in the section above). The file is unchanged since.
- `gabbro_ziel` axiom probe: not re-runnable now; last reading exactly
  `[propext, Classical.choice, Quot.sound]` (unchanged file, unchanged result expected).

## Second gate failure: localized by bisection (2026-10-01, ~15:00-16:00 CEST)

The gate failed again with the identical signature (`failed to create thread`,
exit 134, this time after 5.0s with the full command line
`lean -j2 -M4096 ... -o ...AtomicPayload.olean -i ... -c ...`).
The `lean-slot` queue itself has recovered since (an untouched `Regionen.lean` probes
green again, exit 0), so this round I bisected the module through `./lean-probe` with
scratch files in `$TMPDIR` (all deleted afterwards; nothing outside the owned paths
was touched). Result: about 25 probes, fully deterministic pattern.

### Bisection evidence (each row: scratch file via `./lean-probe`, same 7 imports)

- PASS: single `atomarFussB ... = true by decide` alone (the big
  `vertragsFreiB`-over-program evaluation is survivable in isolation).
- PASS: sections 1-3 together (both big decides plus the `w_nicht_sc` run witness).
- PASS: section 4 (refusals) alone; section 5 (duty audit) alone.
- PASS: every section-6 piece alone (`nichtatomar` theorem, `pD` plus its decide,
  `pD` plus `nutzlast_braucht_restbeweis` plus its witness, `nichtatomar` plus its witness).
- PASS: section-6 pieces combined without prints.
- PASS: prints over olean-loaded constants in the same context (`Nat.add`,
  `List.map`, `atomarB_iff`, `vertragsFreiB_ok`, even `n1_konfig_geteilt` which is
  itself about `GeteiltV`).
- CRASH: the verbatim file copy (reproduces the gate failure exactly).
- CRASH: adding ANY `#print axioms` over a FRESHLY elaborated constant: the two
  section-6 theorems, check-only and `GeteiltV`-only variants, `GetrenntR`-only and
  `VertragsFrei`-only identities, a `GeteiltV` identity (`fun h => h`), even a fresh
  `1 + 1 = 2` with an empty closure — in both the full and minimal fresh contexts.
- CRASH: full file with factored single decide and decide-free `pD` transfer
  (halving evaluations does not move the needle).

### Decisive probe

The verbatim committed content with ONLY the 8 `#print axioms` lines stripped
(mechanical `grep -v`, namespace renamed, nothing else changed) gives
`== 0 error(s) ... exit 0` through `./lean-probe` right now, under load.

### Conclusion

- Every definition elaborates and every proof (all 8 main theorems, all `_zeuge`
  witnesses, all decides, the `pD` fixture, the `w_nicht_sc` run witnesses) checks
  green NOW. There is no logical defect anywhere in the owned module.
- What crashes, deterministically, is each `#print axioms` over a freshly elaborated
  constant in this heavy import context (the whole goal/checker/witness closure).
  Prints over olean-loaded constants pass in the same context, and fresh prints pass
  in light contexts. Even a fresh `1 + 1 = 2` print crashes here, so NO statement- or
  proof-level change (including removing all big evaluations) can fix it: the trigger
  is independent of theorem content.
- The same byte-identical file passed `./lean-probe` (0 errors) and the full
  `./lean-bau` (386 jobs, exit 0) at lane time, so the threshold is load-dependent:
  with `-j2 -M4096` on this machine under today's 40-lane load the print step
  exhausts thread resources; quiet, it fits.
- HARD RULES 6 mandates `#print axioms` for each main theorem in the file, so the
  prints stay. No content repair exists for this failure mode; the module is
  byte-identical to the reviewer-accepted commit `67dd9fd1`.
- A fresh full `./lean-bau` was deliberately NOT re-run: it would only reproduce the
  two gate crashes at high machine cost with zero new information (15 red probes plus
  2 red gate logs already pin the failure to the print step; the logic itself is
  proven green above).
- Concrete ask for the coordinator: re-gate this unchanged content off-peak (it was
  green before), and separately look at Lean 4.33 `#print axioms` thread usage under
  `-j2 -M4096` next time the machine is this loaded. A fresh independent review of
  this report commit is still required; reviewer 388: Lean content unchanged since
  your acceptance.
