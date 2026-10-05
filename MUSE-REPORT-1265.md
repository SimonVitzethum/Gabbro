# MUSE-REPORT-1265: AVX2 join (Vex/Ops/State/Mem on the coherent machine)

## Repair after integration gate failure (NOT merged, fresh review required)

- Integration evidence: `import Grammatik.X86.Avx2State failed, environment
  already contains 'Gabbro.Grammatik.X86.avxWitS0_wf' from
  Grammatik.X86.Avx2Join`. The sibling `Avx2State` piece landed after this
  lane's base and owns the natural top-level witness name `avxWitS0_wf`
  (likely further `avxWit*` names).
- Repair: the entire module content now lives under `namespace Avx2Join`
  (one-line addition + one `end` line; no statement, proof, or name
  otherwise changed). Every declaration is now
  `Gabbro.Grammatik.X86.Avx2Join.*` (confirmed in `./lean-probe`
  output); the file adds ZERO top-level names to
  `Gabbro.Grammatik.X86`, so this collision class is closed against all
  present and future sibling pieces. Residual risk noted honestly: only
  a sibling also opening `namespace Avx2Join` could collide, which no
  sibling lane number suggests.
- Local checks after repair: `./lean-probe` **0 errors** (axioms still
  within `[propext, Quot.sound]`), `./lean-bau` **Build completed
  successfully (658 jobs)**. Guarantees unchanged (no weakening, no new
  axioms, no `sorry`). The integration-tree build with `Avx2State`
  present cannot be reproduced in this clone (stale base, no network);
  the namespacing argument above is structural, not empirical.
- No claim about the full source/binary chain is made. Fresh
  independent review of the changed commit is required.

## Status: DONE (green)

- Last `./lean-probe grammatik/Grammatik/X86/Avx2Join.lean`: **0 errors**.
- Last `./lean-bau`: **Build completed successfully (658 jobs)** with the new
  `import Grammatik.X86.Avx2Join` in `grammatik/Grammatik.lean`.
- Commits on `muse/1265`: part 1 (`e79a0557`) + this report (pending second commit).

## What was delivered

NEW FILE `grammatik/Grammatik/X86/Avx2Join.lean` (~1350 lines, 79 theorems),
plus one import line in `grammatik/Grammatik.lean`. No existing file was
modified otherwise; nothing was copied from any piece (all reuse is by
reference: `ymm*`, `avx2TierZugelassen`, `avx2Bereit`, `HwMaschine`,
`HwSchritt`, `HwWf`, `issueListe` + fold lemmas, `ladeAcht`,
`schreibbar8_einzeln`, `effAddr`, `ripNach`, `stufe_avx256_verweigert`).

1. **VEX rows (§1)**: `Avx2Op` (add/sub/cmp with width, widthless
   and/or/xor/andn, imm shifts, aligned/unaligned 256-bit loads/stores
   via base+disp8), `Avx2Zeile` (op + length), 4-row pinned decoder
   `dekodiereAvx2` (VPADDQ/VPXOR/VMOVDQU-ld/VMOVDQU-st, each `decide`),
   VEX.128 and non-VEX refusals (`decide`).
2. **Profile<->leaf bridge (§2**, the gap lane 1239 lists as missing):
   `cpuAusBlaettern` (EDX[26]/EBX[5]), `xcr0AusWort` (bits 0/1/2),
   `avx2Bruecke_vor` (tier->leaf, needs leaf AVX + OSXSAVE bits) and
   `avx2Bruecke_zurueck` (leaf->tier, needs SSE2 + x87 + control
   freedom + OS state), plus concrete `avx2Bruecke_blatt_zeuge` (`decide`).
3. **Joint machine + 32-byte TSO forms (§3)**: `Avx2Maschine`
   (`HwMaschine` + per-core `YmmDatei`), `Avx2Wf`, flat 32-entry
   `ymmEintraege` (length `rfl`), `ymmSpeichern` (= accepted
   `issueListe`, append/no-mem-change reused, `erfolg` from 4 chunk
   permissions), `ymmLaden` (4x accepted `ladeAcht`, halves joined).
4. **Register evaluation (§4)**: `avx2RegAuswertung` lifts every
   accepted `ymm*` function; 10 agreement theorems (`rfl`/`cases`),
   refusals for `.b8` shifts, `.b64` sra, and memory rows on this path.
5. **Machine steps (§5)**: `ymmGpFehler` (32-byte boundary for the
   aligned shape, with `decide` pins), `avx2Addr` (machine GPR +
   zero-extended disp8), `avx2SetReg` (RIP advance, memory/buffers
   kept, dst written), gated `avx2RegSchritt`/`avx2LadeSchritt`/
   `avx2SpeicherSchritt`, `avx2RegSchritt_gleich` plug equation.
6. **Extended relation (§6)**: `Avx2Ereignis`, `Avx2Schritt`
   (alt/reg/ladeA/ladeU/speichereA/speichereU/still),
   `avx2Schritt_wf` (HwWf preserved), exact `einbettet`/`projiziert`.
   No bare `HwAdapter` is instantiated: it cannot carry the YMM file
   (`HwKern` has no YMM slot), so the extended relation is used (the
   task's allowed alternative). Documented in §6 header.
7. **Refusals (§7)**: absent gate on all three paths, memory/register
   path separation, misaligned `vmovdqa` store, plus the old-row
   cross-check (`stufe_avx256_verweigert` reused).
8. **Two-core witness (§8)**: `vpaddb` (lane 0 `0xFF+2=1`, lane 1
   `1+1=2`), 32-entry buffered store (memory kept at `7`),
   owner-only forwarding (`1` vs `7`), full-word load-back of the
   stored word, memory-changing flush (`7`->`1`), gate/`#GP`/shift
   refusals beside; joint `avx2Wit_zeuge` (13 conjuncts incl. both
   `Avx2Schritt` links, all three `Avx2Wf`, the bridge witness).

Axioms: every `#print axioms` reports a subset of
`[propext, Quot.sound]` (standard; no `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe` anywhere). File ends with a `CUTS:` block.

## FINDINGS (task asked to report disagreements / missing pieces)

1. **Only lane 1239 (`Avx2Ops`) is in this tree.** `Avx2Vex` (1237),
   `Avx2State` (1241), `Avx2Mem` (1243) do not exist here, so the
   decoder, the YMM file and the 32-byte forms are minimal substitutes
   defined in this file (marked as such). If the siblings land with
   different shapes, re-point this file at them.
2. **No unconditional profile<->leaf equivalence holds.** The two
   gates speak about disjoint inputs (leaf side lacks SSE2/control
   input; profile side lacks AVX/OSXSAVE silicon input), so the bridge
   is conditional both ways with each missing conjunct named.
3. **Disp8 is zero-extended** (`avx2Addr`); silicon sign-extends. The
   witness uses disp 0 where both agree. Recorded in CUTS.

## What remains open (see CUTS in the file)

4-row decoder coverage only; no VEX.128/YMM-legacy semantics,
VZEROUPPER, MXCSR SIMD traps, fault taxonomy, whole-vector atomicity,
W/GX bridge, source correspondence, `TSOErreichbar` induction.

## Verification

- `./lean-probe`: 0 errors, all `#print axioms` standard.
- `./lean-bau`: 658 jobs, success (includes the new import).
- No Rust touched; no text guardians affected.
