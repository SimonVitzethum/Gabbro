# MUSE-REPORT-930: Exact review of author 780 (MFENCE drain-own semantics)

Lane 930, clone /home/simon/Dokumente/gabbro-muse/a930, branch muse/930 (verified).
Review-only lane: owns ONLY this file. No source touched, no live controls used.

## CANDIDATE and VERDICT

CANDIDATE: 780 5c486ed6a46b366d8fda9a3b68fe98112f9607a5
VERDICT: ACCEPT
Scope: bounded to MFENCE as own-buffer drain-then-gate over canonical TSO, no foreign discharge.

Scope of acceptance: the three pinned files only
(`MUSE-REPORT-780.md`, `grammatik/Grammatik.lean` one import line,
`grammatik/Grammatik/X86/MfenceDrainOwn.lean` new, 346 lines).
Base matches this clone (`56537272`); PATCH applies cleanly on top of it
in content (import append + new module + report).

## What was reviewed

- Full candidate module (`.tmp/review/author-780/grammatik/Grammatik/X86/MfenceDrainOwn.lean`),
  PATCH.diff (453 lines, only the 3 owned files), OWNER-TASK.md, BUILD-EVIDENCE.json,
  MUSE-REPORT-780.md, SNAPSHOT.json.
- Master-side reused interfaces in this clone: `TSO.lean` (`TSOZustand`,
  `flushKern`, `loadByte`, `zaunBereit`, `TSOErreichbar`, `flush_schreibt_kopf`,
  `flush_rahmen`, `flush_entfernt_kopf`, `load_ohne_eintrag`, `neuestens`),
  `FenceDrain.lean` (`drainVoll`, `drainKernN`, `drain_fremd_puffer`,
  `fdStart/fdS1/fdS2/fdS3/fdX/fdEins/fdSieben`, `fd_voll_schritt`,
  `fd_speicher_aendert`, `fd_fremd_wartend`, `fd_fremd_bleibt`,
  `fd_schritt1/2`, `drain_voll_leer/bereit`), `LockedOps.lean`
  (`lockSchritt`), `LockedInstructionExecution.lean` (`decodeLock`,
  `pinMfence`, `pinZaunUd`, `pin_lock_mfence_decodiert`,
  `pin_lock_zaun_ud_decodiert`, `.lockAufZaun`).
- Official local manual: Intel SDM 325462-093US Sep 2026 snapshot
  (`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`,
  MFENCE Vol. 2B 4-15 at line 65050, encoding row at 148185).

## Architecture findings (independent, byte-level)

- Encoding: `pinMfence = [0F, AE, F0]`; ModRM F0 = mod 3 / reg 6 / r/m 0.
  Manual: `NP 0F AE F0`, ZO, SSE2, and "any opcode of the form 0F AE Fx".
  The accepted `decodeLock` checks only `reg == 6` (line 230), i.e. admits
  the full Fx family exactly as the manual's r/m-ignore sentence requires.
  No new decoder row in the candidate; reuse only. Correct.
- Neighbour refusal: `[0F, AE, E8]` has reg 5 (LFENCE /5) and is `none`
  under the same accepted decoder arm. Correct, no over-admission.
- LOCK prefix: `F0 0F AE F0` parses to `ud .lockAufZaun` in the accepted
  decoder (line 217) and the candidate's `mfenceMitLock_ist_ud` restates
  exactly the accepted `pin_lock_zaun_ud_decodiert`. Matches manual
  "#UD if the LOCK prefix is used". Correct.
- Truncations `[0F]`, `[0F, AE]` are `none` in the accepted decoder;
  candidate's `decide` restatements are direct consequences. Correct.
- Semantics fit: `mfenceDrain IS drainVoll` (own flush iteration);
  `zaunBereit` is own-buffer-empty by canonical definition, so
  drain-then-ready is the manual's "prior stores globally visible"
  rendered at TSO level. `mfenceDrain_ordnung` additionally gates on
  `lesbar` (permissions respected). `mfenceDrain_fifo` proves oldest-first
  visibility for two buffered stores via `flush_schreibt_kopf` +
  `flush_rahmen`. No invented determinism: foreign buffers proved
  byte-identical (`mfenceDrain_fremd`), and `mfenceDrain_loest_fremd_nicht`
  exhibits the surviving foreign entry (proved no-everywhere-discharge).
- Gate composition is honest: the candidate does NOT redefine admission;
  `mfenceDrain_vs_gate` shows on the joint witness that the accepted gate
  (`lockSchritt .mfence`) refuses exactly the nonempty buffer the drain
  flushes, with an observable memory change. SSE2 gating stays with the
  accepted `lockSchrittVoll` and is named as reused, not restated.

## Rule compliance

- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` in the candidate
  (grepped the snapshot; clean). No `Prop`-typed premises; every premise of
  the TARGET is used (hdec/hreach/hdrain/hpend all consumed). No discarded
  premises, no contract quantification, no fake semantics.
- TARGET `MfenceDrainOwn_verbindung` + companion `_zeuge` both present as
  the task's ZEUGE requires. Witness is non-degenerate and joint:
  `fdS2` (reached by two issues, own buffer `[fdX:=1]` nonempty, foreign
  buffer `[fdY:=7]` pending) drains to `fdS3` with a `decide`-proved memory
  change at `fdX`. Reached run, memory-changing step, foreign pending
  throughout. Satisfies INHABITATION.
- Axioms per BUILD-EVIDENCE final probe: every new theorem within
  `[propext, Quot.sound]`, several axiom-free. Standard; goal files untouched.
- CUTS block present with per-theorem `#print axioms`; claim boundary is
  precise (no foreign drain, no SFENCE/LFENCE/LOCK-RMW, no register/flag/RIP
  at TSO level, no timing/interrupts/devices, no source/W/GX/goal change).
- No new diagnostic/gift/example/CLI numbers, no MARKE changes, no
  optimiser-reserved files, no source/checker/Spec/emitter edits. English.

## Build evidence assessment

BUILD-EVIDENCE.json is complete and internally consistent: intermediate
`lean-probe` failures during development (unsolved goals, unknown `s2`)
were repaired in later probes ending at 0 errors with the full axiom
listing; `./lean-bau` ended green (exit 0, 485 jobs, "Build completed
successfully"). The two mid-lane `lean-bau` failures are both at the root
aggregator step with resource signatures (`Eq.olean.private` unreadable,
`std::bad_alloc`) while all module jobs built, then green on retry with no
source change: credible transient flakes, honestly reported. No reproduction
was run from this lane (report-only ownership forbids staging the candidate
into this clone's `grammatik/` tree); every `decide` claim was instead
verified by reading the accepted decoder arms and pins it restates, and the
manual text was checked directly.

## Bounded acceptance / what is NOT claimed

ACCEPT covers exactly: own-buffer drain-then-gate for decoded MFENCE bytes,
FIFO order half, foreign-intact plus proved no-foreign-discharge, explicit
neighbour refusals, reached-run extension, and the joint witness. Still OPEN
(per CUTS, endorsed): foreign drain, SFENCE/LFENCE, LOCK RMW, fetched-level
register/flag/RIP restatement, SSE2 admission (lives with accepted modules),
timing/progress, interrupts/devices/MMIO/DMA, further faults, and any
source/W/GX simulation or goal change. No minimal repairs required; no
REPAIR items found.
