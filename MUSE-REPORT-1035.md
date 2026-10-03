# MUSE-REPORT-1035: Exact review of author 885 (zero-idiom selection rule)

CANDIDATE: 885 2ca9b0f5a4501bc4ae6a1b774358379ddded6983
VERDICT: ACCEPT

## 1. What was reviewed

Author 885, "Optimiser rule: zero-idiom selection rule" (task: `OWNER-TASK.md`
in the review snapshot). The candidate adds exactly two content items:

- NEW `grammatik/Grammatik/X86/OptZeroIdiomSel.lean` (544 lines, verified
  byte-identical between the pinned snapshot file and the `PATCH.diff` file
  section by full read of both);
- one import line `import Grammatik.X86.OptZeroIdiomSel` at the end of
  `grammatik/Grammatik.lean` (snapshot: 514 lines = my base at `b040b155`
  with exactly that line appended; matches the PATCH hunk context).

Plus `MUSE-REPORT-885.md` (report only). No source, checker, Spec, goal,
emitter, guardian, number-register or friend-reserved
(`OptimizationRules.lean`, `OptimizationWitnesses.lean`) file is touched.

Claim: DESIGN §7 "Flags-aware peepholes" row — select `XOR r, r` (3 bytes,
flags clobbered) only with a validator-decided flag-liveness proof at the
site; survivor-flag sites keep the wide `MOV r, 0` (10 bytes, flags
preserved). Target theorem `OptZeroIdiomSel_verbindung` with joint companion
`OptZeroIdiomSel_verbindung_zeuge`.

## 2. Method

- Clone/branch verified: `/home/simon/Dokumente/gabbro-muse/a1035`,
  branch `muse/1035`, HEAD `b040b155` — identical to the candidate's recorded
  parent (`BUILD-EVIDENCE.json` final `git log`: `2ca9b0f5` on `b040b155`).
- Read the complete PATCH (635 lines), the complete snapshot Lean file
  (544 lines), `OWNER-TASK.md`, `MUSE-REPORT-885.md`, `BUILD-EVIDENCE.json`.
- Statically checked EVERY reused name against my base tree: `ZeroIdiomXor`
  (`encodeZero`, `decodeZero`, `zeroSchritt`, `FlagBedarf`, `darfNullen`,
  `Lebendig`, `ersetzeDurchNull`, `darfNullen_heisst`,
  `ersetze_erlaubt_bei_tot`, `encodeZero_laenge`, `roundtripZero`,
  `decodeZero_ist_pilot`, `zeroSchritt_wert/flags/speicher/rip/fremd`,
  `zeroSchritt_stepExt`, `xor_selbst_null/flags/gueltig`, `zeroZeugeStart`,
  `progZero`, `schritt_xorReg64`), `Ausfuehrung` (`schritt`,
  `schritt_movImm64`, `schrittRegister_flags/speicher/rip`, `regSet_gleich`,
  `regSet_fremd`, `laengeOk`, `ripNach`, `lauf`, `zeugeSpeicher`,
  `zeugeFlags`), `Codec` (`encode`/`decode`), `ScalarFloat.laufAlt`,
  `ExtendedExecution.stepExt/.pilot/.weiter/stepExt_pilot`,
  `CostSummary.targetWork`, `ReferenzB` (`refD`, `refEin`, `vertragVon`,
  `refP`, `refO`, `refSp0`, `initB`, `MB`, `RufStartF`, `RufErreichbarF`,
  `refEin_schreibt`, `refB_erreicht`, `refB_schreibt`). All present with
  signatures and statements matching the candidate's use (checked
  `schritt_movImm64`, `stepExt_pilot`, `zeroSchritt_stepExt`, `laufAlt`,
  `LogikGueltig`, `refB_erreicht`, `refB_schreibt` line by line).
- Checked the Intel reference snapshot metadata
  (`.tmp/HARDWARE-REFERENCES/REFERENCES.json`: SDM 325462-093US 2026-09,
  sha-pinned); the flag/encoding rows the candidate depends on are the
  SDM-stated rows already recorded in accepted `ZeroIdiomXor.lean`
  (REX.W + 31 /r; CF/OF cleared, SF/ZF/PF from result, AF undefined).
- Could NOT re-execute `./lean-probe`/`./lean-bau` on the candidate: shell
  commands placing the file into the source tree were refused (reviewer owns
  the report only, no source). This bounds the acceptance (§7); it is not a
  candidate defect.

## 3. Architecture verification (not just Lean green)

- Byte forms: idiom length 3 reuses accepted `encodeZero_laenge`; wide length
  10 proved by `cases r <;> decide` over accepted `encode` (`weitLaenge_zehn`);
  savings `3 + 7 = 10` by `omega` (`nullSpart_gegen_weit`). REX/register/width:
  both forms are 64-bit register-direct over an arbitrary `Register`
  (`movImm64 r 0`, `xorReg64 r r`) — width-consistent, no narrow/wide mix.
- Source/destination/implicit operands: `XOR r, r` reads and writes only `r`
  (frame facts via `regSet_gleich`/`regSet_fremd` on both sides;
  `nullGleichtWeit_register` proves full register-file agreement).
- Flag semantics: the idiom snapshot `Flags.mk false true none true false
  false` is the ACCEPTED `zeroSchritt_flags` (CF=0, PF=1, AF=none, ZF=1,
  SF=0, OF=0 — correct for a zero XOR result); AF=`none` is a sound
  abstraction of architecturally-undefined state, not invented determinism.
  The wide form preserves all flags (`weitSchritt_flags`). The mismatch is
  gated by dead demand (`zeroSelZulassen_tot`), refused otherwise
  (`zeroSelVerweigert_lebendig` = the DESIGN failure case).
- Pre-fault effects: both steps are register-only with checked lengths; the
  connection assumes both steps succeed (`hstep`, `hwide` are `some`) and
  concludes equal success — no fault added/removed, no faulting form
  speculated above its guard.
- Memory access order / TSO / atomicity: both successors leave memory
  untouched (`zeroSchritt_speicher`, `weitSchritt_speicher`, concluded as
  three conjuncts incl. `s'.speicher = w'.speicher`); no shared access exists
  to order, so the vacuous-at-this-level treatment plus an explicit CUTS
  "no TSO/GX bridge" entry is honest, not a hole.
- Feature / MXCSR / interrupt gates: both sides lift through accepted
  `laufAlt`/`stepExt` under the SAME readiness profile `b`
  (`weitSchritt_laufAlt/stepExt`, `nullSchritt_stepExt` delegating to accepted
  `zeroSchritt_stepExt`); XMM and FP context are structurally untouched
  either way — the IEEE leg at the target-step level.
- Canonical execution: `decodeZero_ist_pilot` links admitted bytes to the
  pilot decode (no re-decision); `weitSchritt` IS the pilot `schritt` on the
  MOV row (no second implementation); `decodeZero` refuses distinct-register
  XOR and non-XOR rows through the accepted filter.

## 4. Premises, witnesses, refusals, no fake closure

- All major premises are used: admission `hz` (dead demand, replacement,
  taken idiom), decode `hdec` (pilot-bytes conjunct), both steps (value,
  memory, RIP conjuncts), `cert`/`pfx`/`rest` all occur in the conclusion.
  No `intro _` / `have _ :=` in the file; no `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe` (remaining grep hits are the English word
  "admitted" in comments). No premise has type `Prop` itself.
- No rule-4 violation: the 15-conjunct conclusion derives new equalities
  (not a premise restated); no contracts are quantified away; nothing is
  called a source semantics (`weitSchritt`/`zeroSchritt` are single target
  steps; CUTS disclaims source refinement to the lowering lane).
- Witness `OptZeroIdiomSel_verbindung_zeuge` instantiates ALL premises
  jointly on `rax`/all-dead cert from `zeroZeugeStart` (42 in `rax`), both
  steps firing, store-changing reached `lauf progZero` run (byte 0 → 7 by
  `decide`, as in the accepted witness), PLUS the non-degenerate `refD`
  program (`refEin_schreibt`: `einzahlen` writes its table) with reached
  memory-changing F-run (`refB_erreicht`, `refB_schreibt`: slot 0 → 100).
  Proof steps mirror the accepted `ZeroIdiomXor_verbindung_zeuge`
  (`roundtripZero`+`simpa`, `decide`, `rfl`) extended with the wide step.
- Refusals (negative side): live demand, failing disp, token-op window —
  each an explicit `= false` theorem; `waehleNull_behaelt_weit` keeps the
  wide form on refusal (never a warning); admitted/ZF-live `decide` probes.
- No guarantee weakening, no desired-simulation assumption: the connection is
  conditional on admission + both steps succeeding, and the witness shows the
  condition is jointly inhabitable. `waehleNull_arbeit` (work 1 = 1) uses the
  one accepted `targetWork`; byte savings are counted, not timed.
- Certificate shape is exact and named: `ZeroSelNachweis` (local rewrite
  record `reg/von/nach` + recomputed citations `cert`), `nachweisOk`
  validity citing dead demand and selecting the idiom — DESIGN cert "A".

## 5. Task-fidelity note (reviewed, not a deviation)

The owner task asks for preservation "including IEEE, contracts, call logs,
concurrency and budget". The candidate covers these AT THE TARGET-STEP LEVEL
the rule lives at (IEEE via both `stepExt` lifts; contracts via identical
full register files; call logs/concurrency via untouched memories and
succeeding register-only steps; budget via unchanged `targetWork` + 3-vs-10
RIP accounting) and states the layering in CUTS and its report: a
source-level `execEnd` equality needs the lowering map, which belongs to the
lowering lane. I accept this reading — demanding source refinement inside
this rule lemma would be the wrong layer, and the boundary is precisely
documented, not silently narrowed.

## 6. Last build result

No independent wrapper run was possible from this lane (blocked shell for
source-tree placement, §7). Author-evidenced, from `BUILD-EVIDENCE.json`
(full transcripts, including intermediate red→green iterations during
development, final state):

- `./lean-probe grammatik/Grammatik/X86/OptZeroIdiomSel.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (511 jobs)`
- Axioms: every theorem within `[propext, Classical.choice, Quot.sound]`
  (`OptZeroIdiomSel_verbindung[_zeuge]` use all three; probes/`decide` facts
  use none), consistent with the goal-axiom ceiling.

My static verification (every cited lemma present with matching statement,
proofs following accepted patterns, flag/byte semantics matching the
SDM-stated rows) corroborates green plausibility but does NOT replace the
merge gate's rebuild.

## 7. Bounds and what remains open (acceptance conditions)

1. Bounded acceptance: the merge gate MUST rebuild `grammatik/` green and
   confirm `#print axioms` within the standard triple before integration;
   neither my review nor the author's transcript replaces that check.
2. The pinned head is `2ca9b0f5a4501bc4ae6a1b774358379ddded6983`
   (`.tmp/review/SNAPSHOT.json`: author 885, base `b040b155...` matching this
   lane's HEAD, files exactly `MUSE-REPORT-885.md`,
   `grammatik/Grammatik.lean`,
   `grammatik/Grammatik/X86/OptZeroIdiomSel.lean`, clean tree). Content
   identity was verified here by exact file equality instead of hash trust.
3. Per CUTS (accepted as precise, no fake closure): no silicon
   correspondence; no liveness-analysis implementation (demand is cited site
   data); no source refinement or TSO/GX bridge; no cost/time claim beyond
   one-for-one work and 7 saved bytes; no checker/Spec/goal claim.
4. Minor nits, NOT repair-worthy: `waehleNull_arbeit`'s `by_cases` is heavier
   than needed (`targetWork` is `length`, unconditional) — harmless; the
   `rest` premise is used only via `hdec` — still used.

## 8. Lane-task feedback

Nothing in the owner task appears wrong. The DESIGN §7 row exists exactly as
cited (`DIRECT-COMPILER-DESIGN.md` line 523: premises, cert A, failure case,
phase L). The ZEUGE companion requirement is satisfied jointly and
non-degenerately. No repair is required; minimal action is integration
through the normal checked merge with the build gate in §7.1.
