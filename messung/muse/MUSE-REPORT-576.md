# MUSE-REPORT-576: Independent exact-candidate connection review of 558

## Scope verified

- Directory `/home/simon/Dokumente/gabbro-muse/a576`, branch `muse/576`: match.
- Review inputs: `.tmp/review/SNAPSHOT.json` (single entry, author 558, base
  `8596f83e`, clean true), `.tmp/review/author-558/OWNER-TASK.md` (identical to
  `lanes/558.md` task), `.tmp/review/author-558/PATCH.diff` (291 lines, two new
  files only), `.tmp/review/author-558/MUSE-REPORT-558.md`,
  `.tmp/review/author-558/BUILD-EVIDENCE.json`.
- Candidate file set: exactly `dokumente/x86/CONNECTION-PLAN.md` (new, 230 lines)
  plus `MUSE-REPORT-558.md` (new, 49 lines). No Lean, checker, goal, emitter,
  optimiser, or other docs file touched. Ownership rule satisfied.

## What was checked

1. Producer/consumer name resolution against this checkout at `9ef0afe2`
   (child of candidate base `8596f83e`; no X86 file moved between them per
   `git log --oneline`): `Codec.decode/encode/roundtrip/roundtrip_len_ok/
   decode_nichts_*`, `Byteschritt.fetchDekodiert/gehalt(fetch)/byteschritt/
   ByteAusgang/fetchCap=15/ausfuehrbarN/fetchDekodiert_entspricht/
   byteschritt_weiter/beide verweigert-Richtungen/fetch_nutzt_nur_praefix/
   kanonisch_schritt_ueberein/kette_mov_store_load/opcode_geaendert_verweigert/
   praefix_abgeschnitten_verweigert/ohne_exec_verweigert`,
   `Ausfuehrung.schritt/ripNach/effAddr`, `Bild.Profil/Abschnitt/Bild/Modus/
   effBias`, `Relokation.rel32Fuer/patchRel32/rel32_rundgang/
   rel32_adress_gleichung`, `TSO.TSOZustand/issueByte/loadByte/flushKern/
   TSOSchritt/tso_store_buffering/paket_reisst/kein_lock_schritt`,
   `Zugriffe.zugriff/erfolg_*_im_fuss/*_ohne_speicher/kein_atomarer_zugriff`,
   `NarrowOps.loadNarrow/storeNarrow/moveNarrow/loadNarrowExtend/
   narrowAdmitted`, `TableLayout.layoutOk/hinweisOk/layoutFuer`,
   `ValidatorSkeleton.valX86/valX86Voll/valLayout/valTore`,
   `Quelle.uebersetzeAllg/declOf/einheitAllg/Pflichten/nutzer_aus_quelle/
   nutzerA_aus_quelle`, `schwach_ist_gX` (via `Speichermodell/AtomarZiel.lean`
   and `GXMaschine.lean`, not the path the plan guessed, but the reuse claim
   itself is correct), `GateStub.torOkB/c186VerweigertB/c187VerweigertB`,
   `StackUnwind.lean` present. All resolve; no forged input, no second
   decoder/loader/executor/IR invented.
2. Mismatchspot-checks M1-M7, the load-bearing review criterion:
   - M1 CONFIRMED: `valX86 (p : Profil) (bild : Bild)` in
     `ValidatorSkeleton.lean:50` vs QUELLBRUECKE schema `valX86_sound
     (E : Zielsatz.Einheit D) (bild : Bild) (hV : valX86 E bild = true)`.
     The plan correctly refuses to paper this over and assigns an
     unassigned next-wave adapter file with explicit `hE` bookkeeping.
   - M3 CONFIRMED: `kein_lock_schritt` in `TSO.lean:480`, LOCK execution
     absent; plan keeps LOCK claims refused. Correct.
   - M4 CONFIRMED: `grammatik/Grammatik/X86/IR.lean` absent in this checkout;
     plan gates 572/573/574 on an explicit representation interface and
     forbids a competing IR. Correct.
   - M2/M5/M6/M7 consistent with the files read (`zugriff` potential-only,
     `StackUnwind.lean` present, optimiser files friend-reserved, gate/layout
     checks Bool-only). No invented ISA, FP, or fault claim; 563/565 rows
     honestly defer to real type names / byte evidence.
3. Connection quality (USER PRIORITY bar for a docs owner): each lane 559-575
   row names exact consumed and produced definitions, a measurable closure
   criterion (joint witness + planted refusal + no-duplication rule), and a
   prerequisite hash (`8596f83e`) with gated dependents (573/574 wait for
   ACCEPTED 567+570; 575 waits for ACCEPTED 559-566). Reviewer pairing N+18
   matches the registered wave (576->558). Five backfill tasks have no
   overlapping writers. This is actionable ownership, not repeated inventory.
4. Closure discipline: the plan's section 0 closure rule demands a NEW
   byte-evidenced execution/projection fact plus reuse, joint nondegenerate
   witness, planted refusal, standard axioms, and CUTS; section 5 states the
   document proves nothing and leaves `valX86_sound`/`schluss_x86`,
   per-access TSO->W/GX, extension byte rows, LOCK/fence, single IR, OBS-5,
   and O-cas-cost OPEN. No exaggerated closure, no vacuous conjunction
   counted as execution, no contract-duty weakening (OS/binding contracts stay
   user logic), no hardware mislabelling.
5. Negative checks: no `sorry/admit/axiom/native_decide/unsafe` (no Lean at
   all); no `Spec.lean`/goal/checker/emitter/friend-optimiser edits; no
   verdict changes to other lanes; English-only.

## Accepted bounded claim

The candidate delivers a correct, checkable integration-owner handoff at base
`8596f83e`: concrete producer/consumer interfaces per lane 559-575 over
verified definition names, the M1-M7 mismatch list with assigned follow-ups,
the gated dependency order, and explicit OPEN cuts. It proves no theorem and
claims no closed source-to-byte chain.

## Minimal repairs

None required. Optional (not a condition): at merge time re-confirm the base
hash has not drifted past `8596f83e` before publishing prerequisite hashes.

## Remaining open (not defects of this candidate)

Everything the plan lists as OPEN: `valX86_sound`/`schluss_x86`, per-access
TSO->W/GX simulation, extension byte rows, LOCK/fence execution, single
IR287, OBS-5, O-cas-cost, M1 validator adapter.

## New definitions/theorems

None. Review-only lane; no Lean file added or changed.

## Last build result

No `./lean-bau` run: neither the candidate (two new docs only, verified via
PATCH file list) nor this review (this report only) adds or changes any Lean
file, so the baseline build is unaffected. `git status` before this report
was clean; after it shows only `MUSE-REPORT-576.md` untracked.

## Task feedback

The task text is sound. The IR287-draft absence note in MUSE-REPORT-558 is
accurate for this checkout and correctly handled as M4 rather than a blocker.

CANDIDATE: 558 e48b0173f05d82bd9dbb77bbcbfce6e4c0da5290
VERDICT: ACCEPT
