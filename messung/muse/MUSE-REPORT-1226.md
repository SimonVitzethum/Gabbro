# MUSE-REPORT-1226: Exact review of lane 1225 (precise exceptions)

Lane 1226, clone `/home/simon/Dokumente/gabbro-muse/a1226`, branch `muse/1226`.
Report-only exact review. Candidate read from the coordinator-staged exact
snapshot (no author-clone access from this lane).

Re-review 2026-10-05: the previous verdict (ACCEPT of `b34a68e3`) is
superseded by the NEW pinned snapshot below. The author repair commit
changed NO Lean module: `HwPreciseFault.lean` is content-identical to the
previously reviewed version (same 471 lines, same 26 theorems + plug +
witness defs + 27 `#print axioms`, verified name-by-name and body-by-body
for the previously repaired proofs `przFertig_erhaelt`,
`przHandler_weiterleitung`, `prz_zeuge`). The delta is the author report
(a new integration-gate evidence section) plus a fresh 0-error
`lean-probe` run. All findings below were re-checked against the new
snapshot; every previous finding stands unchanged.

- CANDIDATE 1225, HEAD `4050ebbd7b2442f4fecb14a66d13693a5c66f6eb`,
  base `cbc0afe00eeb8708961b13489750e41e998740d1`, clean.
- Files: `MUSE-REPORT-1225.md` (extended by gate section),
  `grammatik/Grammatik.lean` (+1 import),
  `grammatik/Grammatik/X86/HwPreciseFault.lean` (new, 469 lines, unchanged
  since the previous review).

CANDIDATE: 1225 4050ebbd7b2442f4fecb14a66d13693a5c66f6eb

## Checks performed

- Forbidden tokens over the new file: no `sorry`, `admit` (tactic),
  `axiom` (declaration), `native_decide`, `unsafe`, `split_ifs`,
  `norm_num`, `ring_nf`. Only prose occurrences of "admits"/"admitted".
  No `intro _`, no `have _ :=`, no `sorryAx`.
- Axioms (author build evidence, final green run): every main theorem
  `[propext]` or `[propext, Quot.sound]`; `prz_zeuge` ends
  `[propext, Quot.sound]`. Standard subset, no `Classical.choice` needed.
  `#print axioms` present for all 27 theorems. CUTS block present and honest.
- Scope: exactly the owned files. `Grammatik.lean` diff is one appended
  `import Grammatik.X86.HwPreciseFault` line. Nothing else touched.
- Lift, not copy: every result reuses accepted vocabulary verified present
  in this clone's accepted modules — `hwFehlerSchritt_fehler_still`
  (`HwFaults.lean`, states `m' = m`, so the §2 mem/buffer/view lifts are
  faithful one-step rewrites), `asyncSchritt`/`asyncFertig`/`asyncMasch_wf`,
  `asyncSchritt_verweigert_maskiert/_vektor`, `hwWitStart`/`hwWitAdr`
  (`HardwareExecution.lean`), `hwFehler_wit_abruf`/
  `hwFehler_abruf_schlaegt_alles`/`hwWitStart_wf`/`hwFehlerZLeer`/
  `hwFehlerPgDunkel`, `witMaskiert`/`witSteuerNmi`, S3 (`HwInterrupts.lean`
  §1, lines 27-29, verified), byte equations
  `issueByte`/`loadByte`/`flushKern`/`neuestens`/`tsoAnsicht`, and the
  `HwAdapter` plug shape (`HardwareExecution.lean`: single-field `schritt`).
  No evaluator, machine, or model redefined or weakened.
- Premise use: every premise of every theorem is used. (`adapterPraezise_wf`
  closes the fault branch without `hwf`, which is used in the delivery
  branch — use by the proof overall, not a discard.)
- Agreement: `adapterPraezise_liefere_treue` by `rfl` (the plug IS the
  accepted step); fault refusal by construction (`rfl` on `none`).
- Refusals: masked and misranged delivery lift the accepted refusal lemmas;
  the witness instantiates the masked refusal with both side conditions
  discharged by `decide` (executable). Fault plug refusal sits in the joint
  witness by `rfl`. Remark (not a defect): the vector refusal is proved
  generally but not additionally instantiated by `decide` at witness level.
- Witness `prz_zeuge`: well-formedness, fetch-#PF self-loop on core 1,
  buffer length 1 on core 0, owner forwards 42, foreign core reads 0,
  drain installs 42 into shared memory observed from both cores, plus both
  refusals. Non-degenerate: the drain changes actual shared memory (0 -> 42)
  while the fault fires on the second core; all computational facts
  `decide`-evaluated on the accepted `hwWitStart` machine.
- Silicon: no new silicon facts. S3 is cited as the accepted named
  assumption (verified in `HwInterrupts.lean` §1); `.pf` vector 14 and the
  fetch-#PF candidate come from the accepted priority modules. The
  "unless the SDM says so" clause is correctly reported as resolved: the
  accepted `asyncSchritt` has no drain path, so there is no residual branch.
- Claim scope: no hardware-correspondence and no W/GX claim anywhere; CUTS
  and the author report list exactly what is not proved (no HW verification,
  no fault delivery, no per-access target-to-W/GX simulation, no word-level
  forwarding beyond the shared byte equations). No claim larger than proof.
- Builds: author evidence shows `lean-probe` 0 errors and `lean-bau`
  `Build completed successfully (641 jobs).` at the pinned commit (two
  earlier failures were environmental: transient olean read, resource
  exhaustion exit 134 — documented, retry green unchanged), plus a fresh
  0-error re-probe on the new commit. Own baseline `./lean-bau` in this
  clone: `Build completed successfully (641 jobs).`
- Integration gate (new author-report section, reviewed not re-run): the
  merge build failed environmentally — `failed to create thread`, Lean
  exit 134 at `[640/642] Building Grammatik.X86.HwPreciseFault`, with zero
  elaboration/proof errors in the quoted evidence. This matches the known
  apparatus failure mode (virtual-address ceiling; the author's own clone
  hit the identical signature twice and passed unchanged on retry). The
  author's repair decision — no module change, retry in the integration
  checkout — is correct under HARD RULES 4/5; editing green reviewed
  proofs to chase a worker-spawn crash would weaken guarantees for
  nothing. Consequence for this verdict: ACCEPT covers proof content at
  the pinned commit; the merge still needs one green integration retry,
  which is the merger's gate, not a lane finding.

VERDICT: ACCEPT

Candidate 1225 at `4050ebbd` meets the lane 1225 task: precise fault as
no-effect self-loop, delivery-is-not-a-drain (S3, named), handler forwarding
with foreign-visibility-only-after-drain, and a non-degenerate two-core #PF
witness — all by lifting accepted evaluators, with standard axioms and
honest CUTS. No unsupported desired-correctness premises, no weakened
guarantees, no fake closure found.

Co-Authored-By: muse-agent-1226 <muse-agent-1226@noreply.invalid>
