# MUSE-REPORT-1291: Capstone byte-decoder disjointness across all families

Lane 1291, clone `/home/simon/Dokumente/gabbro-muse/a1291`, branch `muse/1291`.
Owned files only: `grammatik/Grammatik/X86/HwKapsteinDecoder.lean` (new, 994 lines),
`grammatik/Grammatik.lean` (one import line), this report.

## What was done

NEW FILE `grammatik/Grammatik/X86/HwKapsteinDecoder.lean`: one deterministic
priority chain `kapDecode` over all eight byte decoders the capstone union
uses — `decodeMulDivWidth` (itself unified-first over `decodeExt`/`decodeWd`),
`s32Decode`, `mxcsrDecode`, `decodeLock`, `decodeLockAdr`, `decodeC`,
`decodeCore`, `Avx2Join.dekodiereAvx2` — with:

- §1 Agreement: `kapDecode_breit/s32/mxcsr/lock/lockAdr/kompakt/kern/avx2`
  (each level takes its bytes exactly where earlier levels refuse),
  `kapDecode_nichts`, `kapDecode_deterministisch` (one string, at most
  one answer). Every premise is used.
- §2 Eight closed witnesses `kapW_wd/s32/mxcsr/lock/lockAdr/kompakt/kern/avx2`
  with own-arm acceptance (`kapW_*_akzeptiert`), reusing accepted pins and
  round trips (`pin_wdmul_ecx_dekode`, `s32Roundtrip_addssRR`,
  `mxcsrRoundtrip_ld` + `pin_disp_rax_code`, `pin_lock_xadd_decodiert`,
  `decoder_nimmt_skaliert`, `roundtripC_movImm32Zx`, `roundtrip_andReg64`,
  `Avx2Join.dekodiere_paddq`), never re-decided.
- §3 Full refusal matrix (~50 theorems): every witness is refused by every
  other level's decoder. Reused accepted pins where they exist
  (`ext_weist_wdmul32_zurueck`, `pin_disp_vereinheitlicht_weist_s32_zurueck`,
  `pin_disp_mxcsr_weist_s32_zurueck`,
  `pin_disp_vereinheitlicht_weist_ldmxcsr_zurueck`,
  `pin_disp_s32_weist_ldmxcsr_zurueck`, `pin_lock_ext_verweigert_xadd`,
  `produzent_weist_skaliert_zurueck`); closed `decide` evaluations otherwise.
  NO witness-level overlap exists anywhere in the 8x8 matrix.
- §4 `kapKette_*`: the chain takes every witness in its own arm (each level
  reachable, none shadowed), via the accepted dispatcher lemmas.
- §5 Overlaps with winners, each an exhibited byte string plus chain
  evaluation: `kapUeber_wd_ext_mul64/div64/imul2` (REX.W rows keep the
  unified arm), `kapUeber_wd_neu_div32` (new row stays width),
  `kapUeber_f64_bleibt_breit` (scalar-DOUBLE stays unified; both FP arms
  refuse it), `kapUeber_mfence_lock` (MFENCE bytes go to LOCK).
  `kapUeber_wd_bedeutung_mul64/div64` cite the accepted evaluator
  agreement (`wd_mul64_ist_mulRax`, `wd_div64_ist_divRax`): the overlap is
  not a divergent meaning.
- §6 Full domain partition LOCK vs addressed-LOCK:
  `kap_lockModrm_gegen_adrTail` (ModRM level: mod=3 parsed #UD, mod=2
  non-SIB producer-owned, mod=2 SIB splits on byte 36, mod 0/1
  extended-only) + `kap_lock_gegen_lockAdr` (top-level lift over the
  shared LOCK+REX+0F+XADD prefix). No byte string is accepted by both.
- §7 ISA-internal domain partition: `kap_kompakt_weist_sechs_zurueck`,
  `kap_kern_weist_sechs_zurueck` — compact/core acceptance refuses all six
  shared arms (accepted `familien_disjunkt` lifted arm by arm).
- §8 `kapDecode_zeuge`: all eight arms reached on closed strings.
- CUTS block + `#print axioms` for every main theorem.

FINDING status: NO divergent-meaning overlap found. The only byte-level
overlap class (REX.W Group-3/0FAF width rows) keeps the unified arm in both
dispatchers with definitionally equal evaluators; LOCK vs addressed-LOCK is
proved disjoint. Nothing to report as high-priority.

## Verification

- `./lean-probe grammatik/Grammatik/X86/HwKapsteinDecoder.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau` (full project, incl. the new import):
  `Build completed successfully (677 jobs).`
- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`, no unrecorded axiom
  declarations (grep-checked). Axioms per main theorem: `[propext,
  Quot.sound]`, except `kapKette_mxcsr`, `kap_lockModrm_gegen_adrTail`,
  `kap_lock_gegen_lockAdr`, `kap_kompakt/kern_weist_sechs_zurueck`,
  `kapDecode_zeuge` which additionally list `Classical.choice` —
  inherited from reused accepted lemmas (`mxcsrRoundtrip_ld`,
  `familien_disjunkt`/`decF` signature lemmas, `beq_iff_eq` paths), all
  within the standard set; nothing new introduced. No `Prop`-typed or
  unused premises.

## What remains open (also in the file's CUTS)

Domain disjointness beyond the proved partitions stays open (witness-level
only): width vs s32/MXCSR/LOCK/lockAdr/compact/core/AVX2, s32 vs MXCSR and
later levels, MXCSR vs later levels, LOCK vs width/unified (the family-local
open item of the capstone CUTS), lockAdr vs width/unified/compact/core/AVX2,
compact/core vs fp-double, vector and width sub-arms and vs
s32/MXCSR/LOCK/lockAdr/AVX2, AVX2 vs all. System forms have no byte decoder
(control snapshots, not bytes): disjoint by construction, not a proved
bytes-fact. AVX2 VEX covers four pinned rows only (accepted `Avx2Join`
limitation). No silicon re-check, no W/GX bridge.

## Notes on the task text

- "The AVX2 VEX decoder if merged in the tree": it is merged
  (`Avx2Join.dekodiereAvx2`, imported in `Grammatik.lean`) and included as
  the last chain level (note: it returns `Option Avx2Zeile` without rest
  bytes; the chain answers `[]` there, documented).
- "The system-form decoder": no such byte decoder exists on master
  (`HwSystemForms` steps on `SysSteuer` snapshots); recorded as
  disjoint-by-construction in CUTS rather than invented.
- The generic MECHANISM paragraph (new event type, `HwAdapter`, `HwWf`
  preservation, two-core memory witness) describes a family-connection
  lane; this lane's specific task is the decoder chain over the existing
  union, so no new machine adapter was defined — the union events of
  `HwKapstein.lean` are reused by reference, not duplicated.
- `beq_iff_eq` (used for the opcode-193 value equality) and `m.isLt`
  (byte bound) both exist in this repo's Lean v4.33.1; no invented names.
  One self-correction during the work: an early `§4` draft stated a false
  dispatcher-refusal for the width witness itself and was replaced before
  probing.

Co-Authored-By: muse-agent-1291 <muse-agent-1291@noreply.invalid>
