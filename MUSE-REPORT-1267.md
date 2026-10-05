# MUSE-REPORT-1267: AVX2 per-lane equation for arithmetic shift right

## What was done

NEW FILE `grammatik/Grammatik/X86/Avx2SraLanes.lean` (709 lines) plus one
`import Grammatik.X86.Avx2SraLanes` line appended to `grammatik/Grammatik.lean`.
Follow-up of lane 1239 (`Avx2Ops.lean`): `vecSraImm`/`sraLane` had witnesses
only; this lane proves the per-lane equation in the admitted range, lane
separation, saturation to the sign, half agreement, and connects the family to
the coherent machine (`HwMaschine`/`HwSchritt`) via a `HwAdapter` and an
extended step relation with exact embedding. Nothing existing was redefined;
the accepted evaluator is lifted unchanged throughout.

### New definitions

- `SraBreite` (`w16`/`w32`) with `SraBreite.breite` (`.b16`/`.b32`). `.b8`
  and `.b64` have no constructor: refusal by type, not semantics.
- `sraFolge` (both 128-bit halves shift in place over two XMM regs of one
  core; memory and RIP kept), `sraRegSchritt` (Tier-3-gated register plug),
  `HwSraEreignis` (`hwAlt`/`sraReg`/`verweigert`), `adapterSra`,
  `HwSraSchritt` (`alt` + `sra`).
- Witness: `hsraWitMem`, `hsraWitXmm0/1`, `hsraWitReg`, `hsraWitKern`,
  `hsraWitStart`, `hsraWitAdr`, `hsraWitT1/M1`, `hsraWitT2/M2`,
  `hsraWitR1/R2/M3`, `hsraLaneOut`, `hsraMemOut`, `hsraBufOut`,
  `hsraLoadOut`.

### New theorems (all green, axioms subset of standard)

- Refusals: `sraBreite_kein_b8`, `sraBreite_kein_b64`,
  `sraRegSchritt_profil_verweigert`, `adapterSra_verweigert_alt`,
  `adapterSra_verweigert_fehler`, `adapterSra_fremder_kern`.
- Per-lane equation: `laneNat_sraImm` (admitted range),
  `laneNat_sraImm_satt` + `satt_neg`/`satt_pos` (count >= width saturates
  to the sign), 256-bit `ymmSra_lane_lo/hi`, `ymmSra_satt_lo/hi`.
- Separation/agreement: `vecSra_allein`, `ymmSra_allein_lo/hi`,
  `ymmSra_halb`, `sraFolge_lo/hi`, `sraFolge_ymm_lo/hi` (all `rfl`-level).
- Machine: `sraFolge_speicher`, `sraRegSchritt_gleich`,
  `sraReg_ist_schritt`, `hwSraSchritt_wf` (HwWf preserved),
  `hwSraSchritt_einbettet`, `hwSraSchritt_projiziert` (exact both ways).
- Witnesses (`decide`): `vecSra_spur_wort/dwort`,
  `vecSra_spur_saettigung_neg/pos`, `vecSra_spur_dwort_saettigung`;
  machine pins `hsraWit_r1_lo/hi`, `hsraWit_r1_mem_still`,
  `hsraWit_r2_lo/hi`, `hsraWit_m3_buf/fwd_eigen/fwd_fremd/mem_still`;
  steps `hsraWit_schritt1/2/3`, gate `hsraWit_gate(_m1)`,
  `hsraWitStart_wf`, and the joint `hsraWit_zeuge`.

## Last check results

- `./lean-probe grammatik/Grammatik/X86/Avx2SraLanes.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (658 jobs).`
- `python3 instrumente/pruefe-kein-sorry.py --rev muse/1267 --diff master`:
  `0 violations` (1 recorded allowlist axiom `dma_inhalt`, pre-existing).
- `#print axioms`: every main theorem depends only on `propext` and/or
  `Quot.sound` (several on nothing at all). No `sorry`/`admit`/`axiom`/
  `native_decide`/`unsafe` in the new file.

## What remains open (see CUTS block in the file)

No VEX decoder/encoder (no byte correspondence, RIP unchanged by
construction); no YMM register file (halves ride two XMM regs -- a modelling
choice, not silicon); no W/GX bridge, source, budget or timing claims; silicon
correspondence beyond the cited SDM lines stays OPEN.

## Two things in the task I believe are wrong

1. **SSE2 half-agreement target does not exist.** The task asks for
   "agreement of each 128-bit half with the accepted SSE2 packed
   arithmetic shift in `VectorIntegerHardwareForms.lean` where it
   exists". A grep over the tree shows that file holds only the LOGICAL
   quadword shifts (`vecShlQ`/`vecShrQ`, PSLLQ/PSRLQ) and no packed
   arithmetic shift (no PSRAW/PSRAD, no `vecSra`) at any width. The
   agreement leg is therefore vacuous; what is proved instead is that
   each 256-bit half IS the accepted `vecSraImm` half (`ymmSra_halb`,
   `sraFolge_ymm_lo/hi`). Documented in CUTS, not worked around.
2. **"Cores where the family touches memory" has no instance.** SRA by
   immediate is register-only (`sraFolge_speicher`,
   `hsraWit_r1_mem_still`): no family step touches memory, so no
   family-level forwarding witness can exist. The `_zeuge` witness joins
   two XMM-changing SRA steps on two cores PLUS a base-machine byte
   issue through `alt` (buffered store, owner-only forwarding,
   unchanged canonical memory), each step honestly attributed. The
   generic mechanism paragraph over-specifies for a register-only
   family; this deviation is stated, not hidden.

## Process notes

- One parser incident, worth recording: a multi-line nested function
  application inside a structure update (`xmmSet (xmmSet ... ... ...)`
  split across lines) failed to parse (`unexpected token '('`), and the
  `show`-with-underscore patterns built on it failed defeq. Restructuring
  `sraFolge` with `let`-bindings plus `have ... := rfl` + `rw` fixed all
  three errors at once.
- No credentials touched; only the three owned paths were written.
