# MUSE-REPORT-1239: AVX2 256-bit integer operation semantics

Lane 1239, clone `/home/simon/Dokumente/gabbro-muse/a1239`, branch `muse/1239`.
Owned files only: `grammatik/Grammatik/X86/Avx2Ops.lean` (new),
`grammatik/Grammatik.lean` (one import line), this report.

## What was done

New file `grammatik/Grammatik/X86/Avx2Ops.lean`: pure semantic functions
on 256-bit AVX2 integer values, modelled as a pair of 128-bit halves
(`Ymm := Vektor × Vektor`), for VPADD/VPSUB B/W/D/Q, VPAND/VPOR/VPXOR/
VPANDN, VPCMPEQ B/W/D/Q, VPSLL/VPSRL/VPSRA by immediate. Each half reuses
the accepted `Vektor` lane vocabulary (`vecAdd`, `vecSub`, `vecAnd`,
`vecOr`, `vecXor`, `laneNat`, `vecMk`, `vecShlQ`, `vecShrQ`); nothing is
redefined. No shuffle/permute, no gather, no FMA. No decoder, register
file, machine step, or memory op (sibling Vex/State/Mem pieces).

Silicon provenance (checked against the clone-local
`.tmp/HARDWARE-REFERENCES/intel-instruction-reference.txt`, Intel SDM
325462-093US): VPANDN order `DEST := (NOT SRC1) AND SRC2` (lines 40830,
74796); VPCMPEQ equal lanes fill FFH else 0 (lines 75960-75989);
PSLLW/D/Q `COUNT > 15/31/63` zeroes the destination (lines 85640-85714);
PSRAW/D `COUNT > 15/31` clamps to 16/32 so lanes become their sign fill
(lines 86274-86325); VPSRAQ is EVEX-only, no VEX.256 row exists (lines
86120-86129 vs 86511-86530); VEX.256 imm shifts act per 128-bit lane
(lines 85485-85504).

Definitions: `Ymm`, `ymmLo`, `ymmHi`, `ymmAdd`, `ymmSub`, `ymmAnd`,
`ymmOr`, `ymmXor`, `ymmAndn`, `vecCmpeq`, `ymmCmpeq`, `vecShlImm`,
`vecShrImm`, `sraLane`, `vecSraImm`, `ymmSll`, `ymmSrl`, `ymmSra`,
`vecEins`, `kontrollAvxFrei`, `avx2TierBereit`, `avx2TierZugelassen`,
`avx2Cpu`, `avx2Xcr0`.

Theorems (50): half agreement `ymmAdd_halb`, `ymmSub_halb`,
`ymmAnd_halb`, `ymmOr_halb`, `ymmXor_halb`, `ymmCmpeq_halb`;
shift facts `vecShlImm_satt`, `vecShrImm_satt`, `laneNat_shlImm`,
`laneNat_shrImm`, `vecShlImm_b64` (= `vecShlQ`), `vecShrImm_b64`
(= `vecShrQ`); lane separation `ymmAdd_allein_lo/hi`,
`ymmSub_allein_lo/hi`, `ymmAdd_lane_lo/hi`, `ymmAnd_lane_lo`,
`ymmOr_lane_lo`, `ymmXor_lane_lo`, `laneNat_cmpeq`,
`vecCmpeq_selbst`; algebra `ymmAdd_comm_lo/hi`, `ymmAnd_comm_lo`,
`ymmOr_comm_lo`, `ymmXor_comm_lo`, `ymmAdd_zero_lo`, `laneNat_eins`,
`ymmAnd_eins_lo`; gate `kontrollAvxFrei_braucht_legacy`,
`avx2Tier_ohne_avx/sse2/xcr0/kontrolle/osxmm/merkmal`,
`avx2Tier_verfeinert_legacy`, `avx2Tier_basis_zugelassen`,
`avx2Tier_strikt`; witnesses `ymmAdd_spur_ueberlauf`,
`ymmAdd_spur_qword_ueberlauf`, `ymmSub_spur_borg`,
`ymmSll_spur_saettigung`, `ymmSll_spur_eins`,
`ymmSra_spur_vorzeichen`, `ymmSra_spur_zugelassen`, `ymmCmpeq_spur`,
`ymmAndn_spur` (all `decide`).

Checks: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`
(word-boundary grep clean, matching `pruefe-kein-sorry.py`);
`#print axioms` per main theorem: standard only (subsets of
`propext, Classical.choice, Quot.sound`; `Classical.choice` enters via
`beq_self_eq_true` and `mask_and_eq_mod`, same as the accepted files).
No premise quantifies over program syntax, so rule 13 needs no `_zeuge`
companions (witnesses are deliberately suffixed `_spur`, not `_zeuge`).

Last build: `./lean-bau` → `== exit 0; 0 error line(s) in the COMPLETE
output`, `Build completed successfully (642 jobs).`
`./lean-probe grammatik/Grammatik/X86/Avx2Ops.lean` → 0 errors.

## What remains open (see file CUTS)

No `HwAdapter`/`HwSchritt` connection (belongs to Mem/State
integration); no per-lane equation for `vecSraImm`/`sraLane` in the
admitted range (witnesses only); `.b8` shifts and `.b64` arithmetic are
total but have no AVX2 encoding; no profile↔leaf bridge between
`avx2TierBereit` and `CpuFeatureHardwareForms.avx2Bereit`; no
decoder/state/memory/TSO/GX/source/budget claims.

## Task issues found while working

1. The MECHANISM paragraph (HwAdapter, HwWf, two-core memory witness)
   contradicts the FILE SCOPE (pure semantic functions, independent
   piece). I implemented FILE SCOPE and recorded the adapter as open.
2. Name collision: `avx2Bereit` already exists in
   `CpuFeatureHardwareForms.lean` (leaf-level). Mine is renamed
   `avx2TierBereit`/`avx2TierZugelassen` with the level difference
   documented; no model was duplicated.
3. My first `ymmSll_spur_eins` stated a wrong high-half lane value
   (`.2 1 = 8`, correct is lane0 `= 8`, lane1 `= 6`); `decide` caught
   it, fixed before commit. Silicon-first works.
4. `simp only [...] at h` with deep `Bool.and_eq_true` destructuring
   did not flatten as written; replaced by a deterministic
   cases+simp_all proof (`avx2Tier_verfeinert_legacy`).
