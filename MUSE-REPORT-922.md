# MUSE-REPORT-922: Exact review of author 772 (rel8 reachability)

Lane 922, clone `/home/simon/Dokumente/gabbro-muse/a922`, branch `muse/922`
(verified: HEAD `56537272` = snapshot base).

CANDIDATE: 772 e569041f09c6aed8096105321e70f4df80acc184

VERDICT: ACCEPT

Scope of this ACCEPT (bounded): short-branch selection/reachability layer only, as cut.

## What was reviewed

Exact pinned snapshot from `.tmp/review/author-772/`: `PATCH.diff` (717 lines),
`OWNER-TASK.md`, `MUSE-REPORT-772.md`, `BUILD-EVIDENCE.json`, and the candidate
file `grammatik/Grammatik/X86/Rel8Reach.lean` (599 lines) in full. Cross-checked
every reused name against the base tree at `56537272` (BranchLayout, Relokation,
RelocatedExecution, IndirectControlHardwareForms, Ausfuehrung, Speicher, Codec).

## Architecture findings

- Byte forms correct: `EB cb` unconditional (`encodeJmpKurz = [235, d8]`,
  reused lane-680 def), `70+cc cb` conditional (`encodeJccKurz = [112 + condCode c, d8]`).
  `condCode .e = 4` confirmed in `Codec.lean`, so pin `74 FB` is JE rel8 -5. Correct.
- Pins `EB 10`, `74 FB`, `EB 7F`, `EB 80` are `rfl` on reused encoders; range edges
  +127 ok / +128 refused and -128 ok / -129 refused are `decide`. No re-encoding.
- `dispWort8_bridge` reuses accepted `testBit_div_pow` via `bit7_equiv` and mirrors
  accepted `dispWort_bridge`; lets relocation address equations speak about reused
  `kurzZiel`. No invented determinism.
- Selection `rel8Wahl` over reused `indirektZielOk` decoded-start check, with
  acceptance, both refusals (out of range, unadmitted target) and the
  start-or-entry guarantee via `indirektZielOk_garantiert`. Lengths consistent with
  `zweigLaenge` (short 2, wide 5/6); fallback deltas 3/4 check out arithmetically
  (`ziel = start+2+d = start+5+(d-3)`, conditional `+6`/`d-4`).
- Steps only update `rip` (defs inspected: flags/registers/memory kept), inherited
  from reused `jmpKurzSchritt`/`jccKurzSchritt`/`schritt`; no new memory access, so
  no new TSO/store-buffer effect. No feature gate needed (base ISA); fetch
  permission via reused `Byteschritt` discipline, cited not claimed. Pre-fault
  behaviour stays in the reused `Option` steps. No REX/register width issue:
  short branches carry no register operands; REX rows belong to the reused
  indirect forms, untouched.
- No `Befehl` constructor, decoder row, executor, address model or interpreter
  added; no pilot file touched. Scope hygiene clean: 3 files only
  (`MUSE-REPORT-772.md`, one import line in `Grammatik.lean`, `Rel8Reach.lean`);
  no diagnostic/gift/example/CLI numbers, no MARKE_EMIT, no Spec/checker/emitter/
  goal edits, no friend-reserved optimiser files.

## Proof hygiene

- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (mechanical grep of the
  candidate file; only hit is English "admitted"). No `intro _` / `have _ :=`
  discards observed in the full read. All major premises used (spot-checked
  `Rel8Reach_verbindung`: `hfit` via omega context, `hgleich` via wide/short
  equations, `hd` via rewrite, `hstart` via `hzok`, `hrip` via target equations,
  `hkurz` via `jmpKurzSchritt_erfolg`, `hnext` via next-RIP facts).
- ZEUGE satisfied: `Rel8Reach_verbindung_zeuge` jointly instantiates ALL premises
  of `Rel8Reach_verbindung` on start 4096 / rel8 +16 / target 4114 / admitted
  start, both reused steps land on the target word, plus a `write64`/`read64`
  pair with an observably changed byte (`writeBytesN_hit`, `addrOff_null`,
  inequality by `decide`). Non-degenerate, memory-changing.
- Axioms per build evidence: dependency-free or exactly
  `propext, Classical.choice, Quot.sound`. Standard.
- Build evidence credible: module `lean-probe` green at every increment (two red
  intermediates show honest iteration: a `simp` unsolved-goals pair and a free-
  variable error, both repaired); final `./lean-bau` exit 0, 485 jobs. Two whole-
  project failures carry apparatus signatures (`Sets.olean.private` unreadable;
  `failed to create thread`, exit 134), retried green with zero work changes.
- CUTS precise: no silicon correspondence, no timing/caches/TLB/async, no new
  decoder/step/admission, no layout-iteration convergence, no source/checker/
  emitter/goal/TSO-GX claim. Claim matches proof.

## Boundary / what I did not re-verify

- The 26 MB local reference text could not be re-opened from this lane (shell
  read blocked by the permission classifier; per instructions I did not work
  around it). Byte-shape grounding is therefore accepted on the cited SDM
  headings/pages (325462-093US Vol.2A `JMP` p.3-504, `Jcc` p.3-499,
  relative-offset rule pp.3-504-3-505; `REFERENCES.json` verified 2026-10-02,
  sha prefix matches the file header) plus in-tree accepted-encoder
  self-consistency. No AMD claim is made anywhere; none accepted.
- No rebuild of the candidate in this clone (reviewer owns only this report; no
  source writes). No suspicious case needed reproduction: all pins are
  `rfl`/`decide`, all bridges reuse accepted lemmas with matching signatures
  verified above.

## Minimal repairs

None required.
