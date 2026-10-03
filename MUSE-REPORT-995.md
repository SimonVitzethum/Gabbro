# Muse Report 995: Exact review of author 845 (relaxation-layout closing)

## Scope

- Review-only lane. Own file: `MUSE-REPORT-995.md`. No source, no live controls.
- Clone verified: `/home/simon/Dokumente/gabbro-muse/a995`, branch `muse/995`.
- Candidate reviewed from pinned snapshot in-clone:
  `.tmp/review/author-845/` with `SNAPSHOT.json`, `OWNER-TASK.md`,
  `MUSE-REPORT-845.md`, `PATCH.diff`, `BUILD-EVIDENCE.json`,
  `grammatik/Grammatik/X86/ComposeRelaxLayout.lean`.
- Reference manual index in-clone: `.tmp/HARDWARE-REFERENCES/REFERENCES.json`
  (Intel SDM combined volumes 1-4, edition 325462-093US September 2026;
  AMD unavailable, no AMD claim).

## Candidate

- Pinned snapshot: author 845 at head cc8b129807da520eea3e02ee544d08cff0de0b87
- Base: e7c75908456285d1e37c18dc32d4f9c0e10d1fa4 (per SNAPSHOT.json)
- Files: `MUSE-REPORT-845.md`, `grammatik/Grammatik.lean`
  (one import line added), `grammatik/Grammatik/X86/ComposeRelaxLayout.lean`
  (new, 409 lines). Patch matches the snapshot file inspected here.

## What the candidate does

New module `Gabbro.Grammatik.X86.ComposeRelaxLayout` closes one bounded
relaxation round to final-byte revalidation for direct call sites:

- Definitions: `RelaxStelle`, `relaxArtOk`, `patchAusRelax`,
  `relaxStelleOk`, `relaxRundeOk`, `relaxNarrow`, `relaxZeuge`.
- Theorems: `relaxStelleOk_beleg`, `relaxStelleOk_layout`,
  `relaxStelleOk_art`, `relaxRunde_nil`, `relaxRunde_glied`,
  `relaxNarrow_start`, `relaxNarrow_bytes`, `relaxStelle_dekode`,
  `relaxNarrow_ok`, TARGET `ComposeRelaxLayout_verbindung`, refusals
  `relaxStelleOk_kurz`, `relaxPatch_aussen`, `relaxPatch_innen`,
  `relaxStelleOk_ueberlapp`, companion
  `ComposeRelaxLayout_verbindung_zeuge`.
- Producers reused by name (no second decoder/loader/executor/ISA/IR):
  `BranchLayout` (`zweigOk`, `zweigLaenge`, `dispSigned`, `zweigOk_kurz`),
  `TableLayout` (`layoutOk`, `layoutFuer`, `zeugenU`,
  `ueberlapp_verweigert`, writer facts), `RelocatedExecution` (`PatchSite`,
  `siteStart`/`siteNext`, `patchSiteOk` + acceptance/refusals, `relocLen`,
  `relocBefehl`, `relocBytes` + `relocBytes_decode`, `patchSite_ziel`,
  `patchSite_ruf_schritt`, `zustandRuf`, `aussen_verweigert`).
  All names verified present in this clone's `grammatik/Grammatik/X86/`
  (`BranchLayout.lean`, `TableLayout.lean`, `RelocatedExecution.lean`,
  `Byteschritt.lean`, `Speicher.lean`, `Ausfuehrung.lean`,
  `ControlFlow.lean`). Consumer is the layout validator / whole-image
  coverage proof, not re-decided here.

## Architecture checks (not just Lean-green)

- Byte form: `relocBytes .ruf d = encode (.call32 d)`, i.e. E8 rel32,
  5 bytes. Witness `call +16` at 0x1000 to 0x1015 satisfies
  0x1000 + 5 + 16 = 0x1015; return address 0x1005 = 0x1000 + 5 with
  RSP 0x2000 -> [0x1FF8] 8-byte store. Length agreement
  `(relocBytes .ruf _).length = zweigLaenge false .weit` is 5 = 5.
  Matches Intel SDM CALL rel32 (E8) semantics recorded in REFERENCES.json
  scope; no AMD/vendor-difference claim made.
- REX/register/width/flags: 64-bit RSP/RIP, disp32 sign-extended via
  `dispSigned`/`hfeld`, `relocLen`/`direktZiel` equation. CALL touches no
  flags and no MXCSR; none modeled, none zeroed. No feature-gate needed
  for CALL; none invented.
- Operands: source (disp field), destination (mapped target), implicit
  (RSP, RIP, stack memory) all carried as premises (`hfeld`, `hgleich`,
  `hwin`, `hrip`, `hwr`, `hles`). `hart`/`hbed` pin class to unconditional
  call, so the conditional/data legs stay out by construction.
- Pre-fault effects: fetch window (`hwin`), executability (`hexe`),
  RIP alignment to site (`hrip`), fallible `write64` success (`hwr`) and
  readability (`hles`) are all premises; on fault the theorem is vacuous.
  No fault-order claim beyond the reused `patchSite_ruf_schritt`.
- Memory order / TSO / atomicity: single 8-byte push modeled by the
  producer's `write64`/`read64_nach_write64`; no LOCK, no atomicity or
  TSO/GX bridge claimed. CUTS explicitly excludes TSO/GX, concurrency,
  cost/time. Sound bounding, not weakening.
- Undefined state: `suffix` is arbitrary; memory outside the pushed word
  untouched. Witness initial byte 0 is a decided property of the concrete
  `zustandRuf` test state, not an axiom about undefined hardware. No
  invented determinism, no zeroed/ignored defined effect found.
- Zero-bias projection (`bias = 0, off = 0, vaddr = beleg.start`) is a
  bounded scope (one site at final layout), disclosed in CUTS ("one site
  per round step; multi-site convergence stays with ValidatorSkeleton").
  Not a soundness hole within the stated bound.
- `relaxNarrow` normalizes `form` to `.weit`; on accepted inputs it is
  the identity (proved via `zweigOk_kurz` exclusion), so
  `relaxNarrow_start`/`relaxNarrow_bytes` hold by `rfl` and
  `relaxNarrow_ok` re-decides `layoutOk` green. Vacuous for accepted
  inputs but proved, and the vacuity is disclosed (short stays refused,
  stays with `Rel8Reach`; whole-image convergence stays with the
  consumer). This is honest bounded closure, not fake closure: the file
  never claims short acceptance, whole-image convergence, source
  correspondence, hardware correspondence, ABI/loader/entry, or
  conditional/data sites.

## Proof-hygiene checks

- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the snapshot file
  (grep hits are only comments and `#print axioms` lines). No
  `intro _` / `have _ :=` discards. No premise typed `Prop` itself.
- Premise use: TARGET has 16 premises; each is consumed in the proof
  (`hok` via three projections, `hfeld` via target equation and step,
  `hgleich`/`hfit`/`hnext`/`hziel`/`haussen` via site admission and
  target, `hart` via call-step class, `hbed` via length agreement,
  `z`/`suffix`/`m`/`hwin`/`hexe`/`hrip`/`hwr` via step, `hles` via
  read-back). `relaxNarrow_ok` uses its check premise through the
  short-form exclusion. No desired-correctness premise assumed; missing
  legs are CUTS with owners named, never assumed.
- Witness: `ComposeRelaxLayout_verbindung_zeuge` jointly instantiates all
  premises on `relaxZeuge`/`zustandRuf`/writer unit `zeugenU`
  (`schreibt = ["konto"]`, `slotAufz != []`), with re-decoded bytes, a
  reached `byteschritt` call step, `read64` read-back of 0x1005, an
  observably changed byte (`m.bytes 0x1FF8 != initial`), plus a planted
  out-of-range refusal (`aussen_verweigert`). Non-degenerate and
  memory-changing per HARD RULE 13. Three further refusals proved
  (short, interior, overlap) through the accepted producer refusals.
- CUTS block present and precise; `#print axioms` for every main theorem.
- Pinned BUILD-EVIDENCE: `./lean-probe` ends 0 errors after an honest
  iteration history (rewrite/decide failures fixed, not hidden);
  `./lean-bau` exit 0, 0 error lines, 509 jobs, build completed
  successfully; axioms are subsets of `[propext, Classical.choice,
  Quot.sound]` (standard `gabbro_ziel` set).
- Scope hygiene from PATCH: only the new file + one import line + report.
  No source/checker/Spec/goal/emitter edits, no new
  diagnostic/gift/example/CLI numbers, no MARKE_EMIT changes, no
  friend-reserved optimiser files.

## Reproduction note

Review-only lane: the candidate file is not in this clone's
`grammatik/` tree (by ownership rule), so no `./lean-bau`/`./lean-probe`
re-run of the candidate was launched from here; re-running the build here
would measure this reviewer's tree, not the pinned candidate. Verification
is by pinned PATCH/file inspection, producer-name existence grep in this
clone, forbidden-pattern grep on the snapshot, arithmetic recheck of the
witness (0x1000+5+16=0x1015, ret 0x1005, stack 0x1FF8), and the pinned
queued-wrapper evidence above. No suspicious case requiring a separate
queued reproduction was found; no mutation testing beyond the four
planted refusals was needed.

## Last build result

No `./lean-bau` run from this lane (report-only, zero `grammatik/`
changes). Pinned candidate evidence: `== exit 0; 0 error line(s) in the
COMPLETE output`, `Build completed successfully (509 jobs)`.

## What remains open

- Per candidate CUTS (accepted as bounds, not defects): short-branch
  acceptance (`Rel8Reach`); whole-image convergence/coverage
  (`ValidatorSkeleton`); conditional-branch and data-field sites
  (`RelocatedExecution`); source correspondence, TSO/GX bridge,
  concurrency, cost/time, ABI/loader/entry, hardware correspondence.
- Nothing in the owner task statement was found wrong; the wide-fallback
  reading of "narrowed branch re-decoded" is documented in the file
  header and matches the short-refusal design.

## Decision

- Substantive decision: ACCEPT (bounded: one wide call site per round step to
  re-decoded final bytes with re-decided layout, reached
  memory-changing `byteschritt` execution plus planted refusals; all
  wider legs explicitly remain with their named owners).

## Machine-readable verdict

CANDIDATE: 845 cc8b129807da520eea3e02ee544d08cff0de0b87
VERDICT: ACCEPT
