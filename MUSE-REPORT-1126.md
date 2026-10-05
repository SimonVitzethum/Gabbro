# MUSE-REPORT-1126: Exact review of candidate 1125 (async interrupt delivery)

CANDIDATE: 1125 93bde9090d73053943fcbe9d24d166d871895e11

Clone `/home/simon/Dokumente/gabbro-muse/a1126`, branch `muse/1126` — verified,
clean tree. Report-only review; no Lean files added or changed by this lane.
New definitions/theorems by lane 1126: none.

## Candidate pin

- Author lane 1125, pinned HEAD `93bde9090d73053943fcbe9d24d166d871895e11`,
  base `8744590d77cbc7f31d809b4c62cd303bae4ed66f`
  (source: in-clone `.tmp/review/SNAPSHOT.json`).
- Review basis is the exact candidate diff only:
  `.tmp/review/author-1125/PATCH.diff` (1173 lines), the snapshot copy of the
  new file `grammatik/Grammatik/X86/HwInterrupts.lean` (1062 lines), the
  author report and `BUILD-EVIDENCE.json`. The author clone itself was never
  touched (HARD RULES §1; direct access was also permission-refused).
- Diff file list: `MUSE-REPORT-1125.md` (new), `grammatik/Grammatik.lean`
  (exactly one appended line: `import Grammatik.X86.HwInterrupts`),
  `grammatik/Grammatik/X86/HwInterrupts.lean` (new). No other existing file
  is modified.

## Checks performed

1. **Forbidden tokens**: strict word-boundary grep for `sorry|admit|`
   `native_decide|sorryAx|unsafe|split_ifs|norm_num|ring_nf` over the new
   file: zero matches (the substring hits for `admit` are the English word
   "admitted" in comments). No `^axiom` declaration. No `intro _` or
   `have _ :=` discard; no `Prop`-typed premise.
2. **Axioms**: 62 `#print axioms` lines present, one per main theorem.
   Author build evidence shows every theorem at `propext` or axiom-free,
   plus `Quot.sound` exactly where inductive existentials/cases are used
   (`hwIntSchritt_sync_*`, `witNmi_relation`, `asyncLiefer_zeuge`) — a
   subset of the standard `propext/Classical.choice/Quot.sound` set.
3. **Lift, not copy**: the accepted evaluator is referenced, never
   redefined — `liefere` via `liefere_zugestellt_wechsel/_behalten`,
   `pruefeTor`, `waehleStapel`, `schiebeRahmen`, `rahmenWorte`,
   `liesTorBytes`; witness reuses accepted `witMem`, `idtWitSteuer`,
   `loWit`, `wit_bereit`, `witMemDunkel`, `merkmalZugelassen_heisst_beide`;
   TSO stage reuses accepted `issueByte`/`loadByte`/`flushKern`/`tsoAnsicht`.
   No `def liefere`, no `theorem liefere_zugestellt` in the file.
   The `HwAdapter` plug matches the accepted single-field structure
   (`HardwareExecution.lean` §11: `schritt`, with `adapterInterrupt672`
   as the refusing `Unit` default) and the skeleton there already foresees
   this producer shape (own checked event type plus async step relation).
4. **Required legs**: (1) `HwWf` preservation for both stack paths
   (`asyncSchritt_zugestellt_wechsel/behalten_wf`, via `asyncMasch_wf`;
   every premise is consumed by the `simp`/`rw` chains);
   (2) agreement with `liefere` for both paths
   (`asyncSchritt_liefere_wechsel/behalten`, direct applications of the
   accepted stage lemmas under the same premises as the step-success
   equations, hence same memory, handler RIP, new IF and switch flag);
   (3) ten stage refusals plus two adapter projections, all failing closed
   with `none`; (4) joint witness `asyncLiefer_zeuge`, 18 conjuncts.
5. **Witness non-degeneracy**: NMI delivery on core 0 under IF=false
   (S1 bypass) reaching handler 8192 with IST switch, empty buffers on
   both cores (S3 witnessed), frame words 16/4660 read back at 16376/16344,
   observably changed cell (`witNmi_aendert_ss`: bytes differ at 16376),
   four concrete refusals beside it (masked, range, limit, dark-stack),
   core-1 buffered store with owner-only forwarding (42 vs 0), drain
   observed from both cores, `HwWf`, and a reached `HwIntSchritt.async`
   step. Two cores touch memory; two steps change shared-memory bytes.
6. **Silicon facts checked against the clone-local Intel SDM extracts**
   (edition 325462-093US): NMI delivered on vector 2 (txt:164096-164139,
   167196); maskable external vectors 32-255 (txt:9679, 163914); vectors
   0-31 reserved (txt:177461); IF inhibits maskable INTR while NMIs and
   exceptions are not prohibited by IF (txt:156039-156040, 164175, 164177,
   96466); interrupt gate clears IF, trap gate keeps it (txt:9702, 9852,
   164207-164208, 164765, 206823). S3 (delivery drains no store buffer)
   is held as a named assumption with a self-consistency proof
   (`asyncMasch_puffer_still`, zero buffer growth witnessed) — the file
   claims nothing beyond that.
7. **CUTS honesty**: the CUTS block discloses no hardware correspondence,
   no concrete maskable-success witness (the reused IDT image carries the
   vector-2 gate only; maskable admission is proved abstractly through the
   same stage equations), no nesting/#DF/handler execution, no W/GX
   simulation, no timing/APIC/SMI, and that the adapter reads control from
   the event while stored-control agreement (`hst`) is the extended
   relation's premise. No claim exceeds the proof; `gabbro_ziel` untouched.

## Build evidence

- Author evidence: `./lean-probe` 0 errors on the new file (after fixing
  three intermediate elaboration errors during development, all documented
  in `BUILD-EVIDENCE.json`); `./lean-bau` "Build completed successfully
  (601 jobs)" on the candidate tree.
- Reviewer note: the candidate was not rebuilt here — rebuilding it would
  require writing outside the one owned file, which the lane forbids. The
  build judgment for the candidate rests on the author's complete-output
  evidence plus the static checks above.
- Reviewer's own tree: `./lean-bau` ends with
  `Build completed successfully (602 jobs).` (602 vs 601: this clone's HEAD
  carries one more accepted module than the candidate base; baseline green,
  zero errors).

## What remains open (carried from the candidate CUTS, endorsed)

No hardware correspondence; no concrete maskable-success witness; no nested
delivery, #DF escalation, or handler execution; no target-to-W/GX leg;
no timing/arbitration/SMI. All are stated as not claimed, which matches the
task scope (one family connected with self-consistency).

## Non-blocking observations

- The author report places S5 in "§1 and CUTS"; in the file S5 is named at
  the §6 gate-kind theorems and CUTS, while the §1 ANNAHMEN header lists
  S1/S2/S3 (and numbering skips S4). Cosmetic documentation imprecision;
  every silicon rule used is still named somewhere and checked above.
- Agreement leg (2) is stated as paired theorems sharing premises with the
  step-success equations rather than a single corollary equating
  `asyncSchritt` output to `liefere` output; jointly the content is complete
  (same `m2`, offset, IF, switch flag).
- The adapter's control comes from the event; agreement with stored control
  is enforced by `hst` in `HwIntSchritt.async`, not by the plug — disclosed,
  and the task explicitly allowed the extended-relation alternative.

## Task feedback

Nothing in the review task is wrong. One apparatus note: my lane file gave
the candidate as "1125 <full pinned HEAD>" with the hash unresolved; the
pin was recovered from the in-clone `.tmp/review/SNAPSHOT.json`
(`93bde9090d73053943fcbe9d24d166d871895e11`). Future review lanes should
carry the full hash in the lane file itself.

VERDICT: ACCEPT
