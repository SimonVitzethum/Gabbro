# MUSE-REPORT-1226: Exact review of lane 1225 (precise exceptions)

Lane 1226, clone `/home/simon/Dokumente/gabbro-muse/a1226`, branch `muse/1226`.
Report-only exact review. Candidate read from the coordinator-staged exact
snapshot (no author-clone access from this lane):

- CANDIDATE 1225, HEAD `b34a68e3a076237b4e90224b09ca16a7c456398e`,
  base `cbc0afe00eeb8708961b13489750e41e998740d1`, clean.
- Files: `MUSE-REPORT-1225.md` (new), `grammatik/Grammatik.lean` (+1 import),
  `grammatik/Grammatik/X86/HwPreciseFault.lean` (new, 469 lines).

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
  exhaustion exit 134 — documented, retry green unchanged). Own baseline
  `./lean-bau` in this clone: `Build completed successfully (641 jobs).`

## VERDICT: ACCEPT

Candidate 1225 at `b34a68e3` meets the lane 1225 task: precise fault as
no-effect self-loop, delivery-is-not-a-drain (S3, named), handler forwarding
with foreign-visibility-only-after-drain, and a non-degenerate two-core #PF
witness — all by lifting accepted evaluators, with standard axioms and
honest CUTS. No unsupported desired-correctness premises, no weakened
guarantees, no fake closure found.

Co-Authored-By: muse-agent-1226 <muse-agent-1226@noreply.invalid>
