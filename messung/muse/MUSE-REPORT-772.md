# MUSE-REPORT-772: Hardware completion — rel8 reachability

Lane 772, clone `/home/simon/Dokumente/gabbro-muse/a772`, branch `muse/772`
(verified: `.git/HEAD` = `ref: refs/heads/muse/772`).

## What was done

New module `grammatik/Grammatik/X86/Rel8Reach.lean` (599 lines) plus the
one-line import registration in `grammatik/Grammatik.lean`. This is the
short-branch **selection/reachability layer** over the accepted lane-680
short forms (`EB cb`, `70+cc cb`) and the accepted lane-423 wide
certificate (`zweigOk`). No `Befehl` constructor, decoder row, executor,
address model or interpreter was added; no pilot file touched.

Definitions (4): `rel8Passt`, `disp8Signed`, `rel8Wahl`, `rel8Handbuch`
is NOT added (provenance lives in the file header + CUTS instead; the
`indirektHandbuch` string of lane 680 is reused by reference, not copied).

Theorems (22):
- fit/value: `rel8Passt_grenzen`, `disp8Signed_schranke`,
  `disp8Signed_passt`
- byte pins: `pin_disp8_vor` (+16), `pin_disp8_zurueck` (-5),
  `pin_disp8_max` (+127), `pin_disp8_min` (-128),
  `pin_reichweite_oben` (127 ok / 128 refused),
  `pin_reichweite_unten` (-128 ok / -129 refused)
- bridge: `bit7_equiv` (reuses accepted `testBit_div_pow`),
  `dispWort8_bridge` (mirrors accepted `dispWort_bridge`; lets the
  relocation address equation speak about the reused `kurzZiel` step)
- selection: `rel8Wahl_kurz`, `rel8Wahl_weit_aussen`,
  `rel8Wahl_weit_ohne_start`, `rel8Wahl_garantiert` (over the reused
  `indirektZielOk` decoded-start check)
- encoder pins on reused lane-680 encoders: `pin_rel8jmp_vor` (`EB 10`),
  `pin_rel8jcc_zurueck` (`74 FB`), `pin_rel8jmp_max` (`EB 7F`),
  `pin_rel8jmp_min` (`EB 80`)
- `rel8_fallback_passt` (reachable minus 3/4 stays in signed-32)
- `Rel8Reach_verbindung` (TARGET): reachable + admitted short jump
  yields a wide rel32 field to the SAME target (via reused `dispVonFit`),
  reused `zweigOk` acceptance, reused `direktZielOk` admission, and BOTH
  reused steps (`jmpKurzSchritt`, `schritt`/`jump32`) land on the target
- `Rel8Reach_verbindung_bedingt`: the taken-conditional twin (delta 4,
  length 6, reused `jccKurzSchritt`/`jumpIf32` taken equations)
- `Rel8Reach_verbindung_zeuge` (TARGET companion): joints ALL premises
  on start 4096 / rel8 +16 / target 4114 / admitted start, both steps on
  target, plus a memory-changing store (return word 4101 written at 8184,
  reads back, byte observably changed from zero; reuses accepted
  `zweig_schreibbar8`, `zweig_lesbar8`, `read64_nach_write64`,
  `writeBytesN_hit`, `addrOff_null`).

Manual grounding (clone-local, no network): Intel SDM 325462-093US Vol.2A
Ch.3 `JMP-Jump` (`EB cb`, "Jump short, RIP = RIP + 8-bit displacement
sign extended to 64-bits", p.3-504), `Jcc-Jump if Condition Is Met`
(`7x cb` rel8 table, p.3-499), relative-offset rule (signed 8/16/32-bit
immediate added to the address following the instruction, pp.3-504-3-505).
`REFERENCES.json` verified 2026-10-02; AMD retrieval failed, no AMD claim.

## Check results

- `./lean-probe grammatik/Grammatik/X86/Rel8Reach.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0` (repeated after every
  increment). Every `#print axioms` is either dependency-free or exactly
  `propext, Classical.choice, Quot.sound`. No `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe` (no `sorryAx` in any axiom print).
- `./lean-bau`: `== exit 0; 0 error line(s) in the COMPLETE output`,
  `Build completed successfully (485 jobs)`. Two earlier runs failed at
  the final root `Grammatik.lean` aggregation step with apparatus
  signatures (`Sets.olean.private` unreadable; `failed to create thread`,
  exit 134) while the module itself always probed green; a retry on a
  quiet pool succeeded with zero changes to the work. Root cause was
  transient resource/toolchain contention, not an elaboration error.

## What remains open / handoff notes

- `lean-bau` whole-project green IS measured from this clone
  (485 jobs, exit 0); no revert needed, all three owned files commit.
- Deliberately NOT claimed (see CUTS): silicon correspondence, timing/
  caches/TLB/asynchronous effects, new decoders/steps/admissions (all
  reused from lanes 680/423/291), pilot/short collision refusals
  (proved in 680, cited), whole-function narrowing convergence, source/
  checker/emitter/goal connection, TSO/GX/concurrency.
- Task-text scope notes: TSO/async/fault/flag/gate modelling for the
  claimed forms is inherited from the reused steps (jumps preserve
  flags/registers/memory per the reused frame equations; fetch needs
  execute permission per the reused `Byteschritt` discipline; branches
  perform no memory access, hence no store-buffer interaction is
  introduced). No new silicon behaviour is assumed anywhere.
- Nothing in this lane needs new diagnostic/gift/example/CLI numbers,
  MARKE_EMIT changes, or friend-reserved optimiser files; none touched.

## Task-text assessment

The fixed ZEUGE pair (`Rel8Reach_verbindung` +
`Rel8Reach_verbindung_zeuge`) is proved as specified: short-branch
reachability (-128..+127 of virtual next-RIP) with the decoded-start
check (reused `indirektZielOk`) and the wide-form fallback (same-target
`zweigOk` + `direktZielOk` + both reused steps), pinned bytes. No extra
premise was needed beyond honest machine bounds (no-wrap next-RIP facts
`start+5/6 < 2^64`, carried in the theorems, all used).
