# Muse report 490 — Independent exact-candidate review of 410

- Clone verified: `/home/simon/Dokumente/gabbro-muse/a490`, branch `muse/490` (HEAD `1c54c6da` at review time). Mismatch check passed; no other clone read.
- Candidate under review: author 410, pinned HEAD `1bc8057c288c1917570c09bab8c920988f78a8bc`, base `0b3132b7`, per `.tmp/review/SNAPSHOT.json`.
- Owned file only: `MUSE-REPORT-490.md` (this report). Nothing else created or modified; `git status` clean except this file.

## What was done

Independently inspected the exact supplied artefacts: `.tmp/review/SNAPSHOT.json`, `.tmp/review/author-410/OWNER-TASK.md`, `PATCH.diff` (477 lines, exactly two new files: `MUSE-REPORT-410.md`, `dokumente/x86/AUDIT-CALL-ABI.md`), `MUSE-REPORT-410.md`, `BUILD-EVIDENCE.json`, and the full audit document (409 lines). Verified:

1. Scope/ownership: PATCH touches only the two owned files. No Lean, Rust, checker, emitter, Spec/goal, friend (`OptimizationRules`/`OptimizationWitnesses`), or manifest changes. SNAPSHOT file list matches PATCH. `clean: true`.
2. No forbidden content: audit is prose documentation; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (the six grep hits for "admit" substrings are the English word "admitted" in probe descriptions). No new definitions/theorems, so no witness (`_zeuge`) obligation arises; nothing weakened or renamed.
3. Material correctness spot-checks against actual in-tree sources in this clone (all corroborated):
   - `Stapel`: `rahmenOk` (46), `spitze_ausgerichtet` (70), `sichereWort` (82), `argReg_sonde_rdi` (293), `argReg_sonde_r9` (296), `argReg_ab_sechs` (312), `sichereErgebnis`/`ladeErgebnis` (333/338), `rahmenZeuge_ok` (533), joint memory-changing witness `rahmen_schreibLese_zeuge` (557+, zero becomes 42 at slot 1 with observable byte change — read in full).
   - `AufrufOpt`: `InlinePflicht.vorOk`/`nachOk` (139/144), `rufAt_ok_vorOk` (149), `geistRekon_zeuge` (191), CUTS block (~256+).
   - `Ausfuehrung`: `schrittPush`/`schrittCall` (43/58), `schritt_ret_erfolg` (373), `zeuge_speicher_aendert_sich` (787), `probe_ruf_kehr` (804), `probe_schub_liest_alt` (809), `probe_nimm_rsp_gewinnt` (826).
   - `Zugriffe`: `stapelOben` (37), call row stores actual next RIP (57), refusal family `zugriff_*_versagt_kein_erfolg` (467–527), `kein_atomarer_zugriff` (540), `probe_zugriff_ruf_wert` (619).
   - `ControlFlow`: `direktZiel` (21), `setLowByte` (26+), `cmovMem_feheler_bleibt` (117), `direktZielOk` (174+), `cmov_speicher_zeuge` (279), refusal trio (306/313/320), `ziel_anfang_akzeptiert` (428).
   - `SpillPrivate`: `SpillFrisch` (24), `spillPrivatOk` (36) with three refusals (42–57) plus positive (60), `spill_fill_kommutiert_zeuge` (188), `spill_tso_zeuge` (327).
   - Trust-boundary consumers: `Syscall.schreibAbi` clobbers `rcx`/`r11` (55–59) vs `argReg` 4th arg `rcx` — the audit's P0 gap is real; `FremdRuf.GateData.regs` abstract indices (41–44); `Folge.fNach` clears armed bit on `callInd`/compounds/locks/loops (verified in `Folge.lean`); `N575`–`N577`/`C186`/`C187` references match `saetze.rs`.
4. No vacuity, forgery, or safety weakening: the verdict claimed is precisely bounded ("each helper sound within its stated claim and its CUTS; four P0 bridges missing; full source-to-final-byte validation remains OPEN"). No closed lowering, hardware, native expansion, or speed claim. Explicitly refuses to invent bugs for OPEN bridges (C2 GateStub, C4 EntryState, C1 TableLayout, C5 ValidatorSkeleton) and distinguishes false semantics (none found) from incomplete deliverables. P0–P2 repair list names owning follow-up work. CUTS of the audit document itself stated (sec. 10 + closing paragraph).
5. Build evidence: `BUILD-EVIDENCE.json` shows correct clone/branch (`a410`/`muse/410`), staged exactly the two owned files, and committed as `1bc8057c`. One probe entry has `status: error` with empty output — it is the `git remote -v` probe, correctly blocked for a lane (no network/remote). Author states `./lean-bau` not run because the commit is documentation-only; this is honest disclosure, not forged evidence, and correct: no Lean file is added or changed, so no proof gate is affected. This review likewise ran no full build (clone untouched by candidate; verification by source inspection). No `lean-bau`/`lean-probe` queue was needed since nothing suspicious was found requiring reproduction.
6. English only (no German text; non-ASCII is limited to logic symbols `∧ → ↔ ≠ … — – ’`).

## Exact names of new definitions/theorems

None. This review adds no Lean definitions or theorems and modifies none.

## Last `./lean-bau` result line

Not run — this review commits only this report (no Lean change), and the candidate is documentation-only. Clone working tree otherwise clean.

## What remains open

- The four P0 bridges the audit names (rsp-to-Rahmen linkage, indirect-target/`entry fn` provenance, ret/terminal provenance + callee-save, indirect ghost coverage + `nachOk`, x86 gate-stub correspondence + callee obligation (c)) remain OPEN by design; they belong to GateStub C2, EntryState C4, and related follow-ups, not to this candidate.
- Minor line-number drift (±a few lines) between audit citations (as-read at audit time) and newer master is expected; the audit discloses this. Spot-checks confirm all cited theorems/probes exist.
- The audit's "reproduced probes" are cited in-tree `decide` probes with file/line evidence, not re-executed builds — honestly disclosed in the author report and appropriate for an audit lane.

## Anything in the task believed wrong

Nothing wrong. The owner task's probe wording ("actual reproduced probes where useful") is satisfied by exact file/theorem/line citations of merged in-tree probes for a prose audit that adds no Lean code; demanding re-execution would add no signal here.

CANDIDATE: 410 1bc8057c288c1917570c09bab8c920988f78a8bc
VERDICT: ACCEPT
