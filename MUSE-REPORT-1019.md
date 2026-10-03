# MUSE-REPORT-1019: Exact review of author 869 (overflow-check elimination rule)

## Outcome

CANDIDATE: 869 565b2106e9fdf9c1b816a1fc7fbd0b008df950f9
VERDICT: ACCEPT

Acceptance is bounded by the remarks recorded below; the substantive
verdict is unchanged by this format fix.

## What was done

Report-only exact review of the pinned snapshot in
`.tmp/review/author-869/` (SNAPSHOT.json: author 869, head `565b2106`,
base `b040b155`, files `MUSE-REPORT-869.md`,
`grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/OptOverflowElim.lean`,
clean). Verified:

1. Clone/branch: `/home/simon/Dokumente/gabbro-muse/a1019`, branch
   `muse/1019`. Base `b040b155` equals this clone's HEAD.
2. Read the full candidate file (335 lines), OWNER-TASK.md,
   MUSE-REPORT-869.md, PATCH.diff (444 lines) and BUILD-EVIDENCE.json.
3. Independently verified every in-tree dependency the candidate uses
   exists with a matching statement in this clone: `InvariantenOpt`
   (`alsLitOpt`, `litLeBool`, `isWahrAll`, `isWahr`, `holdsBool`,
   `isWahrAll_sound`, `exec_pruefung_wahr`), `ReferenzB` (`refD`,
   `refEin`, `refO`, `refP`, `refSp0`, `initB`, `MB`,
   `refEin_schreibt`, `refB_erreicht`, `refB_schreibt`),
   `Syntax.vertragVon`, `Maschine.keinRuf`, plus the
   `Endblock.leave rfl` / `Block.nil` / `Env.nil` / `sp.welt []`
   usage patterns (all precedented in-tree, e.g. `SonstLeaveZeuge`).
4. Checked the design citations against `grammatik/OPTIMIZER.md`:
   B3 §3.5 ("overflow check removed only under a proved-impossible
   overflow (range entailment, recomputed)", PROPOSED), R4 §3.6
   (signed `sdiv`/`srem` to shift REFUSED), §3.9 (FP default REFUSE),
   §7.2 "checks (B1–B3)" row (certificate: SSA versions + range
   entailment; validator recomputes entailment `decide`), §6.4
   (target work/time transfer OPEN). All citations accurate.
5. Checked the hardware reference (`REFERENCES.json`: Intel SDM
   edition 093, clone-local text): the ADD entry (Vol. 2A 3-14)
   states ADD "evaluates the result for both signed and unsigned
   integer operands and sets the OF and CF flags to indicate a carry
   (overflow) in the signed or unsigned result, respectively". The
   candidate's `tragU` (sum reaches `2^w`) / `ueberlaufS` (sum
   leaves the symmetric `2^(w-1)` range) distinction and the
   width-8 divergence pin (`200` fits u8, not s8) are consistent
   with it. The candidate makes no encoding/REX/LOCK/TSO/MXCSR/
   interrupt claims, so the rest of the hardware checklist is
   out of scope by construction; CUTS say so explicitly.
6. Grepped the candidate for banned tactics: no `sorry`, `admit`
   (only English "admitted"), `axiom`, `native_decide`, `unsafe`,
   no `intro _` / `have _ :=`, no `forall rho` / `forall v`
   contract quantification.

## Findings (all checked against the actual text)

- TARGET `OptOverflowElim_verbindung` is sound as stated: admitted
  cert (`hz`) + recomputed entailment (`hEnt`, conditional on
  admission) imply (1) the literal bound check evaluates true
  (via `overflowBedingung_wahr` + `isWahrAll_sound`) and (2) exact
  `execBlock` outcome equality with the check-free continuation in
  the post-read world (via accepted `exec_pruefung_wahr`). The
  `sonst` branch is proved unreachable, not assumed. Every premise
  is used; no `ensures` derived; no refusal weakened; no fault
  speculated above its guard.
- Companion `OptOverflowElim_verbindung_zeuge` instantiates ALL
  premises jointly on `refD` (u8 check `0 ≤ 200 ≤ 255`, admitted
  cert, `Block.nil`, `Endblock.leave`) and is non-degenerate:
  `refEin_schreibt` (einzahlen writes its table),
  `refB_erreicht` (F-run reached), `refB_schreibt` (slot `0`: `0`
  vs `100`, memory-changing). Both conclusion conjuncts are used.
- Refusals cover every cert flag (`overflowVerweigert_bereich/
  breite/vorzeichen/shiftDiv/gleit`); probes are `decide` in both
  directions (admission passes; shiftDiv- and float-tainted certs
  refuse). Axioms of connection + witness are exactly
  `[propext, Classical.choice, Quot.sound]`; all other lemmas are
  subsets or axiom-free. Owned files only (new module + 1 import
  line + report); no friend-reserved optimiser files, no new
  diagnostic/gift/example/CLI numbers, no MARKE_EMIT or
  source/checker/Spec/goal/emitter edits.
- CUTS are precise: validator-side recomputation is a premise
  (analysis future work); no signed-division rule; no float rule;
  no `totalCost` inequality (OPEN per OPTIMIZER §6.4); no silicon,
  TSO/GX, ABI or loader claims.
- Build evidence is complete and honest: per-step `lean-probe`
  `0 error(s)` including one repaired red state, final full
  `lean-bau` `Build completed successfully (511 jobs)`, axioms
  printed from the real build output.

## Remarks (non-blocking, recorded for the record)

1. Report prose overstates one lemma: "outside sets it" holds for
   unsigned (`tragU_trifft`) but for signed only the UPPER
   direction is proved (`ueberlaufS_trifft`); there is no
   lower-bound `ueberlaufS` trigger lemma. Sound, but asymmetric.
2. `tragU_cf_of_auseinander` doc comment narrates `150 + 50`
   while the OF conjunct proves `100 + 100` (both sum to `200`;
   both correct). Cosmetic.
3. The report's `OptFoldConst.lean` line-256 note does not
   reproduce: the in-tree line reads `∃ (V : Vertrag refD)`
   (uppercase). The `vertrag`-unknown-identifier error in
   BUILD-EVIDENCE came from the author's own intermediate draft
   and was repaired before the pin. No action needed.
4. The CF/OF identity lemmas and the `breiteOk`/`vorzeichenFix`
   cert flags carry no proof weight in the connection (the
   entailment is over `Int`); the rule is sound as stated, but a
   future validator must actually check width/signedness against
   the real range facts. Bounded acceptance; CUTS cover the
   validator side as future work.
5. No independent build reproduction was run in this lane:
   applying the PATCH would mean owning source, which this
   report-only task forbids (`OWN ONLY MUSE-REPORT-1019.md`).
   Reproduction is deferred to the serial integration gate
   (merge script builds before committing); base matches the
   snapshot base exactly, and the evidence trail is complete.

## Last build result

No `./lean-bau` run in this lane (report-only; source untouched).
Author evidence: `./lean-bau` → `Build completed successfully
(511 jobs)`, exit 0, at pinned HEAD `565b2106`.
