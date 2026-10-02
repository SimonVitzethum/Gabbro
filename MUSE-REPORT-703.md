# MUSE-REPORT-703: Exact review of author 702 (scalar binary32 SSE2 forms)

Clone `/home/simon/Dokumente/gabbro-muse/a703`, branch `muse/703` — verified.
Own only this report; no source, no live controls, no network/push touched.
Task typo noted: §21 says "Own only MUSE-REPORT-693.md" — read as 703.

CANDIDATE: 702 a156fdbce65818622b999dc41e35591b69acd731
VERDICT: ACCEPT (bounded; §6 lists the exact boundary, all already in the candidate CUTS)

## 1. What was reviewed

Exact pinned snapshot `.tmp/review/author-702/` (SNAPSHOT.json: head
`a156fdbc…d731`, base `a6315567…670c`, clean, 3 owned files) — PATCH.diff
(98,702 bytes), module
`grammatik/Grammatik/X86/ScalarFloat32HardwareForms.lean` (1853 lines, read
in full §§1–9, witnesses, CUTS, 5 `#print axioms` lines), OWNER-TASK.md and
MUSE-REPORT-702.md in full, plus BUILD-EVIDENCE.json (incremental probe
history ending green). Official local manuals
`.tmp/HARDWARE-REFERENCES/` (REFERENCES.json: Intel SDM 325462-093US Sep
2026, sha256 `a4a62e6…f321`; extracted `.txt` 17.7 MB contains MOVSS 53x,
ADDSS 63x, UCOMISS 38x, CVTSS2SD 37x, CVTSI2SS 38x, CVTTSS2SI 43x and the
cited Vol.1 sections 5.5.1.1/5.5.1.2/5.5.1.3/5.5.1.6, 10.4.1.2, 11.5.2.x).
PATCH touches only the 3 owned files; `Grammatik.lean` diff is one additive
import line. No source/checker/Spec/goal/emitter or friend-reserved file
touched.

## 2. Architecture verification (not just Lean green)

- Genuine f32 kernel, no duplicate interpreter: `s32Rechne` routes
  definitionally to accepted `Gleitprofil.fadd32/fsub32/fmul32/fdiv32` over
  `bites32`/`muster32`; conversions via accepted `wertExakt`/`rundeExakt`
  (`cvtSS2SD`/`cvtSD2SS`), `ofInt` at f32 directly (`cvtSI2SS32/64`, never
  via f64), truncation + integer indefinite in `cvttSS2SI`. State is the
  accepted shared `FpZustand`; fetch reuses `geholt`/`ausfuehrbarN`/`laengeOk`,
  memory reuses `read32`/`write32`, bytes reuse `parseLe32`/`leBytes32` and
  the accepted ModRM/SIB helpers. No second XMM file, no second fetch.
- Byte forms: F3 scalar-single rows (10/11, 58/5C/59/5E, 5A), F2 only for
  CVTSD2SS, NP only for UCOMISS; REX.R/B extend reg/r/m, REX.W selects width
  on the two integer rows and is refused elsewhere, REX.X refused; ModRM
  mod=11 register vs mod=10 memory + disp32, SIB 36 iff low base code is 4,
  both SIB shapes. Length accounting checked (reg 4/3+REX, mem 8/7+REX+SIB).
  All-XMM register round trips (10) + memory round trips (4) proved; closed
  high-register instance `s32_rex_waehlt_hoch_addss` (0x45 → xmm8/xmm9) and
  both REX.W rows proved.
- Register/width/flag semantics: `setzeTief32` low-32 replace with upper-96
  and `vHi` preservation proved; register MOVSS preserves upper 96
  (`s32Schritt_movssRR_hoch`) while memory load clears them
  (`…_movssLade_nullOben`, via `xmmLadeTief32_nullOben`) — the specified
  asymmetry. CVTSS2SD writes low 64 via accepted `xmmSchreibeTief` keeping
  upper 64 (`…_cvtss2sdRR_vHi`); legacy upper-YMM halves carried untouched
  (`s32SchrittVoll_ymm`). `ucomissFlags` tuple matches the accepted
  `ucomiFlags` shape exactly (CF,PF,AF=some false,ZF,SF,OF; unordered=all
  three, less=CF, equal=ZF) with decide-checked rows. No silent f64
  promotion: joint pair `s32_stallt_bei_2hoch24`/`s32_f64_steigt_weiter`
  (f32 stalls at 2^24, f64 advances). Bare CVTT separated from the
  saturating wrapper (`cvtt_trennt_vom_saettiger`: NaN → `0x8000…` vs
  `gleitRoh` → 0).
- Pre-fault effects / memory order: guards ordered length → profile →
  memory; every failure returns `none` with no partial state; RM forms do
  one `read32` (4-byte footprint theorems `read32_wert_klein`,
  `read32_braucht_lesbar`, `write32_braucht_schreibbar`), store does one
  `write32` with readback (`s32_speichere_liest_zurueck`) and overlap frame
  (`s32_speichere_rahmen`). No pre-fault register/memory effect exists.
- Gates: `s32Eintritt = mxcsrGueltig` (RNE, FTZ/DAZ off, all masks; sticky
  bits unchecked — matches accepted profile); FTZ word closes every form
  (`s32Schritt_ftz_verweigert` via accepted `mxcsr_ftz_verweigert`),
  sticky word stays open (`s32Schritt_sticky_offen`); silicon/OS/profile
  gate `s32Zugelassen`/`s32ByteschrittTor` fail-closed all three legs with
  pass-through proved. `s32Byteschritt` takes only state, never a
  caller-supplied decoded value.
- No invented determinism: NaN results stay class-only (raw-bit witnesses
  for 1+2, +0/-0, subnormal growth, 1/0=+inf, 0/0=NaN class; NaN-payload
  mutation proves two payloads share one class with different bits).
  Conversion fallthrough to fixed `nanQ` is only ever observed by
  class-theorems; payload/SNaN/DAZ-FTZ/sticky-accumulation gaps are OPEN in
  CUTS, not claimed.

## 3. Mechanical checks

- Forbidden tokens over the candidate file: `sorry` 0, `axiom` 0,
  `native_decide` 0, `unsafe` 0; `admit` hits are English words
  ("admitted") only; no `Prop`-typed premise; every premise of the step/
  frame/refusal theorems is used (unfold+simp/rewrite+cases pattern).
- Premise hygiene: no conclusion-is-premise restatement, no
  `forall rho/v` contract quantification (no Vertrag/Stmt premises at all —
  hardware model over `FpZustand`, so rule-13 `_zeuge` is not mechanically
  required and no ZEUGE target line exists in the owner task); no
  memory-less "semantics"; no `intro _`/`have _ :=` discards found.
- CUTS block complete (§9, proved rows vs OPEN list) and 5 `#print axioms`
  lines present.
- Joint reached memory-changing witness: `s32Zeuge_fetched_lauf` runs
  fetched ADDSS then fetched MOVSS-store from actual executable bytes,
  changes real RAM (byte `0x2002` `0x00`→`0x40`) with exact `read32`
  readback; plus conversion witness (`s32Zeuge_cvtsi42`), NaN-payload
  mutation, blind-memory refusal (`s32_blind_verweigert`), overlap frame.
  Negative mutations cover wrong-width (F2 arithmetic/MOVSD), wrong/missing
  prefix (F3-on-compare, prefix-less arithmetic, 66), REX.W/X, mod=1,
  register-store, truncations, FTZ/sticky control words.

## 4. Evidence (actual, from BUILD-EVIDENCE.json + local reference grep)

- `./lean-probe grammatik/Grammatik/X86/ScalarFloat32HardwareForms.lean` →
  `== 0 error(s) in the COMPLETE output; exit 0` (final entry; intermediate
  entries show genuine red→green repair, including one transient `sorryAx`
  that is absent from the final axioms).
- `./lean-bau` → `Build completed successfully (469 jobs).`
  (`ScalarFloat32HardwareForms` built in 45s; umbrella `Grammatik` built;
  final axiom samples within the standard set, e.g. `s32Zeuge_fetched_lauf`
  `[propext, Quot.sound]`, `s32_nan_nutzlast_mutation` no axioms).
- No rebuild was run from this report-only lane (own-only-report; copying
  the candidate into `grammatik/` would violate ownership); verification is
  by exact-snapshot inspection, evidence-chain review and local accepted-
  interface/reference cross-checks above.

## 5. On the task text

Nothing factually wrong. Two scoping notes (neither blocks acceptance):
(1) "stable generic raw-state/MXCSR adapter with 668 once accepted" could
not be concretized because lane 668 is unaccepted — the candidate exposes
the narrow shared surface (`xmmTief32`, `s32Eintritt`/`mxcsrGueltig`,
`FpZustand`) by construction and names the integration points in CUTS;
(2) "Own only MUSE-REPORT-693.md" in §21 is a number typo for 703.

## 6. Bounded acceptance (all in candidate CUTS, restated)

Proved: MOVSS reg-merge/load/store shapes, ADDSS/SUBSS/MULSS/DIVSS reg+m32
shapes, UCOMISS reg+m32 with ZF/PF/CF rows, CVTSS2SD/CVTSD2SS reg shapes,
CVTSI2SS/CVTTSS2SI reg shapes with REX.W widths; REX.R/B high-XMM and REX.W
selection through the independent decoder; fetched fetch/decode/step with
length+permission checks; fail-closed silicon/OS/profile gate; legacy
upper-YMM preservation; joint fetched RAM-changing run. OPEN (never
claimed): NaN payload/quiet-bit/SNaN discipline, rounding beyond RNE rows,
DAZ/FTZ execution, sticky accumulation, denormal conversion inputs,
all-input CVTSS2SD exactness, memory-source integer conversions, VEX/EVEX +
AVX zeroing, packed SIMD, TSO tearing/GX bridge, fault delivery beyond
explicit refusal, timing/budget, `decodeExt`/`stepExt` + `PerfMerkmal`
integration (local `S32Hw` gate is the sharing point). Byte rows are stated
canonical contracts mirroring the accepted F2 rows (Vol.2 opcode pages
absent from the extracted text — declared in the file header, never a
silicon claim).
