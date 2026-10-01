# Muse Report 617: Independent overnight closure review of 605

- Branch: `muse/617`, clone `/home/simon/Dokumente/gabbro-muse/a617` (verified: `git rev-parse --abbrev-ref HEAD` = `muse/617`).
- Owned path only: `MUSE-REPORT-617.md` (this file). No Lean file touched, no umbrella import added, no other path written.
- Review inputs (exact, read-only): `.tmp/review/SNAPSHOT.json`, `.tmp/review/author-605/OWNER-TASK.md`, `.tmp/review/author-605/MUSE-REPORT-605.md`, `.tmp/review/author-605/PATCH.diff`, `.tmp/review/author-605/dokumente/x86/CONCURRENCY-CLOSURE-PLAN.md`, `.tmp/review/author-605/BUILD-EVIDENCE.json`, plus the live tree in this clone for name/file:line verification.

CANDIDATE: 605 c10e59c5dc457c3e1f6af16c11c295b2a2034ed4

VERDICT: ACCEPT

## What was done

Reviewed the exact 605 candidate (docs-only closure plan, two owned files, no Lean changes) against its owner task and the live accepted modules. Verified:

1. **Owned-path discipline:** `PATCH.diff` adds exactly `MUSE-REPORT-605.md` and `dokumente/x86/CONCURRENCY-CLOSURE-PLAN.md`. No `grammatik/` change, no umbrella import, no checker/`Spec`/goal or friend-reserved optimiser edit. Matches the owner task's `OWN ONLY` constraint.
2. **Every cited Lean name exists:** all ~30 reused names verified by grep in this clone: `histVon`, `sichtVon`, `spülen_baut_frische_nachricht`, `weiterleitung_ist_jüngste`, `fremd_weiterleitung_unsichtbar`, `hist_zeuge_gelenk`, `paket_reisst` (TSOHistory); `realisiert_fuss_abdeckung`, `byte_realisiert_fuss`, `realisiert_fuss_abdeckung_zeuge`, `realisiert_versagt_laenge`, `byte_ohne_fetch_kein_realisiert`, `realisiert_store64_wort_kein_atom` (AccessExecution); `lockSchritt`, `casSchritt`, `lock_xadd_atomar`, `cas_schleife_unbeschraenkt`, `rmw_nur_mit_lock`, `mfence_ordnung`, `locked_add_zwei_kerne`, `keine_lock_zyklus_schranke`, `LockNachW` (LockedOps); `WortGuard`, `wort_schritt_liest_zurueck`, `wort_fuss_reisst`, `WortNachW` (WordAtomicity); `atomarFussB`, `GeteiltV`/`GeteiltA`, `audit_pflicht_deckt_aufgenommen`, `audit_beobachtung_menge`, `nutzlast_braucht_restbeweis`, `nutzerA_aus_quelle` (AtomicPayload); `SchrittW`, `Lesbar`/`Frisch`, `schwach_ist_gX`, `w_kein_verlust`, `sicht_waechst` (Speichermodell); `exchange_liest_schreibt` (AccessList); `kein_lock_schritt`, `tso_store_buffering`, `tso_last_lesbar`, `tso_frisch_beispiel` (TSO).
3. **Load-bearing §2 gate verified verbatim in source:** `histVon` (`TSOHistory.lean:25-28`) builds a fresh two-message snapshot `[⟨0,0,∅⟩, ⟨1,bytes a,∅⟩]` per state, and `spülen_baut_frische_nachricht` (`:185-191`) concludes `Frisch ... 2` for the OLD snapshot plus `Lesbar` in the NEW snapshot. Timestamps are projection-local and reused per flush; no monotone counter, no extension relation. The plan's "snapshot fact vs real preserved run" distinction is accurate, not invented, and the gate rule (reject `Lesbar`/`Frisch`/`SchrittW`-shaped premises about the mapped event) is the correct enforcement.
4. **"Disconnected producers" verdict corroborated:** the only `SchrittW`/`RufSchrittGX` mentions in X86 producers are explicit non-claims (`TSOHistory.lean:315`, `TSO.lean:563`, `ReleaseAcquire.lean:254`; `WortNachW`/`LockNachW` proved empty by `kein_wort_nach_w`/`kein_lock_nach_w`). `PayloadResidue.lean:202-217` consumes assumed W steps as premises, constructing none from TSO. Nothing accepted today builds a source W step from a target TSO event. No self-consistency-as-hardware claim, no desired simulation premise, no competing interpreter, no extra IR proposed.
5. **Witness/refusal/CUTS/axiom hygiene:** the plan cites real joint witnesses (`hist_zeuge_gelenk`, `realisiert_fuss_abdeckung_zeuge`, `locked_add_zwei_kerne`, `tso_store_buffering`) and real planted refusals (`fremd_weiterleitung_unsichtbar`, `realisiert_versagt_laenge`, `rmw_nur_mit_lock`, tearing witnesses). No new theorems are added, so HARD RULE 13 inhabitation is N/A (correctly stated in the 605 report). No Lean means no new axioms and no `./lean-bau` claim; per the lane instruction for docs work this is correct, not a gap. No `sorry`/`admit`/`axiom`/`native_decide` found in the cited producers (one grep hit was the English word "admits" in a doc comment).
6. **Docs usefulness (594/604/605 bar):** concrete existing code throughout, a usable decision (strict order SourceMemory570 → TSOTrace596 → BridgeWrite573/BridgeRead574), bounded disjoint tasks T1–T5 with exact consumer names and proof/witness/refusal criteria, explicit non-goals, and an honest CUTS block. No filler.
7. **Template clauses correctly N/A:** Tools595 (read-only/restart/PID) and Rust618 (verifier verdicts/thread path) concern other lanes' deliverables; 605 touches neither tools nor Rust, so there is nothing to reproduce or diagnose here.

## Minor imprecisions (not repair grounds)

- File:line citations omit the `Speichermodell/` directory prefix (`MaschineW.lean:150`, `Sicht.lean:133/139`, `AtomarW.lean:279`); line numbers themselves verified correct.
- `sicht_waechst` lives in `Speichermodell/Atomar.lean`, not `MaschineW.lean:269`; `w_kein_verlust` lives in `Speichermodell/MaschineW.lean`, not `RMW.lean:191`. Wrong file, right theorem, right reuse leg. Bounded scope, no semantic effect.

## Bounded accepted scope

- Accepted: the audit, the §2 gate rule, the G1–G7 ordering, the T1–T5 task shapes, and the non-goals, as review guidance for owners 570/596/573/574 and the coordinator. It proves nothing and claims no closure.
- Not accepted (still open, correctly labelled so): G1–G7 themselves; any 573/574 simulation; any claim that byte-level projection facts constitute a source run.

## Follow-up for the coordinator (not 605 defects)

- This reviewer's base (`377b290e`) already contains a substantial `grammatik/Grammatik/X86/SourceMemory.lean` (committed candidate under review588 per the handoff), which postdates 605's base (`0044c258`). The plan's own CUTS anticipates exactly this: §3.7 and the T2/T3/T4 rows must be re-audited against the landed 570 interface once review588 resolves. Suggested next independent task: a bounded re-audit of §3.3/§3.7 against accepted `SourceMemory` (exact owner from the registry), reusing this plan's gate rule.

## Build evidence

- No `./lean-bau` run: docs-only candidate with zero `grammatik/` bytes changed (verified via `PATCH.diff`), so a full 400+-job build would measure the base, not the candidate. `git status --porcelain` in this clone is clean except this report. No `./cargo-pruef`/`./emission-pruef` run: nothing they measure was touched.

## What remains open (for 617: nothing)

- 617 owns only this report. No Lean work, no repair needed, no obstruction found.

Co-Authored-By: muse-agent-617 <muse-agent-617@noreply.invalid>
