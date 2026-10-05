# MUSE-REPORT-1303: Extended context state (x87, MXCSR_MASK, XSAVE header, YMM)

## Repair 2026-10-05 (integration gate failure, nothing merged)

Gate evidence: `import Grammatik.X86.HwXsaveFull failed, environment
already contains 'Gabbro.Grammatik.X86.VollEreignis.noConfusion'
from Grammatik.X86.HwTranslateFull`. A sibling lane merged first
and owns the `Voll*` namespace.

Repair (owned files only, semantics and proofs untouched): every
identifier starting with `Voll`/`voll` renamed to `Xsave`/`xsave`
(two mechanical `replaceAll` passes, e.g. `VollMaschine` →
`XsaveMaschine`, `vollSpeichern` → `xsaveSpeichern`,
`vollRundlauf_maschine_zeuge` →
`xsaveRundlauf_maschine_zeuge`). All name lists below read with
that mapping. Additionally hardened three unprefixed generic
names with no evidence against them but plausible collision
surface: `kanonisch` → `xsaveKanonisch`, `witArt` →
`xsaveWitArt`, `witFehler` → `xsaveWitFehler`.

Verification after repair:

- `./lean-probe grammatik/Grammatik/X86/HwXsaveFull.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (677 jobs).`
- `#print axioms`: unchanged standard subsets (all `[propext]`
  or `[propext, Quot.sound]`); no new axioms, no `sorry`.
- Residual risk, stated plainly: this clone does not contain
  `HwTranslateFull`, so the local build cannot reproduce the
  integration collision; the gate re-checks. Only the evidenced
  family plus three generic names were moved. If the gate names
  another collision, the same mechanical pattern applies.
- No claim is made about the full source/binary chain; a fresh
  independent review of the changed commit is required.

Original report follows unchanged (names read as renamed above).

---

Lane 1303, branch `muse/1303`, clone `/home/simon/Dokumente/gabbro-muse/a1303`.
Follow-up of lane 1247 (`HwContextState.lean`). All work in the NEW file
`grammatik/Grammatik/X86/HwXsaveFull.lean` (~2830 lines) plus one import line
in `grammatik/Grammatik.lean`. No other file touched.

## What was done

Full XSAVE area on the coherent machine, reusing the accepted definitions
unchanged (never copied): `HwMaschine`/`HwSchritt`/`HwWf` (HardwareExecution
§11), `issueByte`/`loadByte`/`flushKern`/`issueListe`, `ctxAlle`,
`fxEintraegeAux`, `ctxLadeAux`, `ctxLade_geladen`, `ctxFalte`, `ctxNull`,
`ctxByte`, `ctxOffsets`, `mxcsrReserviertFrei`, `ldmxcsrArchOk`,
`xcr0SseBereit`/`xcr0AvxBereit`, `YmmDatei`, `vecJoin`/`vLo`/`vHi`, `ArchFehler`.

Main definitions: `X87Bild`, `x87Reset`, `XsaveKopf`, `kopfStandard`,
`x87Offsets`, `maskOffsets`, `kopfOffsets`, `ymmOffsets`,
`vollOffsets` (RFBM-selective: x87/mask/header always, legacy iff SSE,
YMM iff AVX), `kopfByte`, `ymmByteAt`, `vollByte`, `x87AreaOff`,
`VollBild`, `vollDekodiere`, `VollMaschine`, `vollHw`, `VollWf`,
`setVollTso`, `setVollKern`, `vollEintraege`, `VollFehlerIn`,
`VollAusgang`, `kanonisch`, `vollSpeichern`, `vollWiederherstellen`,
`vollFinit`, `VollEreignis`, `vollOpt`, `VollSchritt`.

Main theorems: `vollRundlauf_x87/_maske/_kopf/_legacy/_ymm` (pure),
`vollKongr_mxcsr/_xmm/_x87/_maske/_kopf/_ymm`, `vollOffsets_nodup`,
`vollSpeichern_puffer/_kein_speicher/_wf`,
`vollWeiterleitung_gespeichert`, `vollWiederherstellen_wf/_erfolg`,
`vollRundlauf_maschine` (save-then-restore identity on the enabled
components), the ordered fault gates
(`vollSpeichern_fehlerNM/_fehlerUD_ohne_cpuid/_fehlerUD_lock/
_fehlerGP_ohne_x87/_fehlerUD_ohne_sse/_fehlerUD_ohne_avx/
_verweigert_leer/_fehlerGP_nicht_kanonisch/
_fehlerGP_falsch_ausgerichtet/_fehlerSS/_fehlerPF/_fehlerAC/
_verweigert_ohne_schreibrecht`, restore mirror plus
`_fehlerGP_reserviert` with `vollRestore_stimmt_ldmxcsr_ueberein`),
`vollFinit_*` + `vollFinit_rundlauf`, `vollSchritt_wf`,
`vollLade_ist_hw`, `vollGibAus_ist_hw`, `vollSpüle_ist_hw`,
`vollSpüle_ist_hw_zurueck`, witness observes (`wit_buf`,
`wit_fwd0/1`, `wit_fremd`, `wit_restore0/1`, `wit_drain`,
`wit_gp_reserviert`, `wit_verweigert`, `wit_h1/h1b/h2/h2b`
outcome equalities by `rfl`, `wit_rundlauf_anwendung0/1`,
`wit_schritt_*`), and the joint witness
`vollRundlauf_maschine_zeuge` (joins all identity premises on a
reached two-core run: 476-entry AVX-only + 480-entry SSE-only
saves, owner-only forwarding, memory-changing drain, applied and
observed round trips, refusals, FINIT, wf). Helpers
(`nodup_append_of`, `x87mem`/`maskmem`/`ctxmem`/`kopfmem`/`ymmmem`,
`disj_*`, `addrOff_inj832`, `neuestens_*832`,
`issueListe_anderer_kern`, `fxEintraegeAux_laenge`) are in-file.

Mechanism choice (task allowed either): an extended step
relation `VollSchritt` with exact two-way TSO-leg embedding, NOT
a `HwAdapter` plug. Reason: x87 images, masks and YMM upper files
live beside `HwMaschine` (in `VollMaschine`, like the accepted
`YmmMaschine` wrapper), so no adapter over `HwMaschine` can carry
a save without inventing that state. Documented in §7 and CUTS.

## Verification

- `./lean-probe grammatik/Grammatik/X86/HwXsaveFull.lean`:
  `== 0 error(s) in the COMPLETE output; exit 0`.
- `./lean-bau`: `Build completed successfully (677 jobs).`
  (`✔ [676/677] Built Grammatik`.)
- `#print axioms` for 20 main theorems: all subsets of
  `[propext, Quot.sound]` (several `[propext]` only). No `sorry`,
  `admit`, `axiom`, `native_decide`, `unsafe` in the file.
- No `sorryAx` anywhere; standard axioms only.

## Findings (measured, not yields)

1. Kernel wall: a 736-entry joint save exceeds kernel memory
   (`(kernel) excessive memory consumption detected`; 480 works,
   736 OOMs). Consequence, recorded in CUTS: the joint set is
   proved generic (`vollRundlauf_maschine` is flag-parametric)
   and OBSERVED per enabled set (476 AVX-only, 480 SSE-only).
   The 736 `decide`/`Nodup` is deliberately not in the tree.
2. Permission-window bug caught by the kernel: my first witness
   permission range covered 736 bytes while the footprint spans
   832 (offsets to 831); the `decide` failed loudly. Fixed to
   832-byte areas before any commit.
3. Header BV values are request-dependent and verified as such:
   AVX-only request writes BV bits 0+2 (= 5), observed `5`.
4. `++` parses left-nested in this toolchain; the footprint is
   parenthesised right-nested explicitly so the membership API
   reads. `if sse then … else …` (Bool) elaborates with
   condition `sse = true`: `rw [hs]` does not close it,
   `if_pos`/`if_neg` do. `by_cases … with` is not valid syntax
   here; bullets are. `set_option … in` must precede the
   docstring, not follow it.

## What remains open

Nothing in this lane: every task bullet is delivered (opaque
footprint-exact x87 block with FINIT, MXCSR_MASK carried and
written but ignored on restore, standard-form header with zero
XCOMP_BV, YMM_Hi128 via `Avx2State`, NM/UD-CPUID/SS/PF/AC/
canonical outcomes via `HwFaults`, XSAVE-then-XRSTOR identity
generic + applied + observed, handler bodies untouched).
Remaining work is the documented CUTS list in the file (x87 FPU
execution, mask silicon semantics, header enforcement,
compaction/supervisor forms, RFBM/fault-input derivation, 736
joint kernel eval, W/GX bridge, source link, timing).

## Task notes (things believed wrong or imprecise)

1. None blocking. Two readings were resolved as documented
   above: the `HwAdapter`-or-relation choice (relation taken,
   reason given) and the `_zeuge` target (no `ZEUGE:` line in
   the task; `vollRundlauf_maschine_zeuge` joins the identity
   premises jointly on non-degenerate state).
2. The task's "XCOMP_BV zero in the standard form" is modeled
   and observed (written `0`, decoded back); its ENFORCEMENT on
   restore is deliberately absent and booked in CUTS.

Co-Authored-By: muse-agent-1303 <muse-agent-1303@noreply.invalid>
