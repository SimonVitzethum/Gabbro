# MUSE-REPORT-675: Exact review of author 674 (SIMD enabled-state gates)

CANDIDATE: 674 7916dce7f062f4c1379978e241645696c6249ff2
VERDICT: ACCEPT

## Scope of this review

Report-only exact review. I inspected the pinned snapshot
(`.tmp/review/author-674/`: `PATCH.diff`, `VectorHardwareProfile.lean`
(763 lines), `MUSE-REPORT-674.md`, `OWNER-TASK.md`, `BUILD-EVIDENCE.json`,
`SNAPSHOT.json`) and cross-checked every referenced producer in my own
clone plus the official local Intel SDM snapshot
(`.tmp/HARDWARE-REFERENCES/`, 325462-093US Sept 2026, sha-verified).
I own only this report; no source file was added or modified, no live
controls touched. My clone/branch verified first:
`/home/simon/Dokumente/gabbro-muse/a675`, branch `muse/675`.

## What the candidate does

New leaf module `grammatik/Grammatik/X86/VectorHardwareProfile.lean` plus
one additive import line in `grammatik/Grammatik.lean`. PATCH touches
exactly those two files plus `MUSE-REPORT-674.md`. No producer, source,
checker, Spec/goal, emitter, or friend-reserved optimizer file is touched.

1. Enabled-state (§1): `CpuMerkmal`, `Xcr0Bild`, `KontrollBild`,
   `xcr0SseBereit` (x87 && SSE), `kontrollSseFrei` (!EM && !TS && OSFXSR),
   `hwVektorBereit` (silicon SSE2 && XCR0 && controls && `osXmm`),
   `vektorHwZugelassen` (finite `paketInt128` admission AND hardware
   readiness), four projection theorems, safe refinement
   `vektorHw_verfeinert` (checked gate implies old `vecEintritt`).
2. Gated execution (§2): `stepVectorHw` (accepted `stepVector` under the
   gate, `none` otherwise); CPU/XCR0/control refusal theorems; width
   fact `vektorBreite_spur`; PXOR low/high and PADDQ high lane theorems;
   rFLAGS preservation.
3. Memory forms (§3): `VektorSpeicherForm` (aligned/unaligned),
   `vektorGpFehler` (#GP iff 16-byte misaligned, aligned form only),
   `vektorSchreibZugelassen`, footprint `vektorHw_fuss` (16-byte
   `vecFuss`), tearing `vektorHw_teilt` (no atomicity claimed).
4. AVX2 (§4): `VektorStufe`, 128-bit row IS the gate, 256-bit row always
   `false`; scalar fallbacks `skalarPaarXor`/`skalarPaarAdd` with half
   lemmas, lane bridges, and `skalarPaarXor_gleich` (xor fallback reads
   back exactly the packed `vecXor` word lane by lane).
5. Adapter + witnesses (§5): `vektorValidatorZugelassen`
   (`extZugelassen` AND hardware gate) with projections;
   `stepExt_vec_hw`; `vectorHw_fetch_bridge` through unified
   `extByteschritt`; joint `vectorHw_zeuge` (pinned canonical PXOR bytes
   decode, gate admits, gated step and unified dispatch reach the same
   successor, chained MOVSD store changes memory byte 0, closed by
   `decide`); seven negatives (no CPU / no XCR0 / EM-set / no OS bit /
   misalignment / alias overlap / unknown opcode byte 0).

## Independent verification (evidence, not trust)

- Forbidden tokens: precise grep for `sorry|admit|native_decide|unsafe`,
  `^axiom`, `intro _`, `have _ :=`, `: Prop` premises — all CLEAN.
  (Loose matches are only English words like "admitted".)
- Premise use: every theorem's premises are load-bearing. The two
  `cases ... <;> simp_all` refusals (`stepVectorHw_ohne_xcr0`,
  `stepVectorHw_ohne_kontrolle`) genuinely need `hx`/`hk` (without them
  the gate could still be true). Bridge theorems are identities over
  producer theorems with all of `hf`/`hgate`/`hs` used. No conclusion
  restates a premise; no contract quantification; no fake semantics.
- Producer existence + signatures: `vecEintritt`, `stepVector`,
  `stepVector_pxor_spur`, `stepVector_paddq_spur`, both `_flags`
  theorems, `stepExt_vec`, `extZugelassen`, `fetchExt`,
  `extByteschritt`, `extByteschritt_weiter`, all `vecZeuge*`,
  `vecFuss_in_traeger`, `vecWrite_teilt`,
  `vecFuss_teilueberlapp_verweigert`, `laneNat_xor`, `xorB_nat`,
  `vLo_vecJoin`, `laneGet_toNat`, `merkmalZugelassen`,
  `merkmalBreite .paketInt128 = .b32` — all confirmed present.
- No producer drift: the six producer files are byte-identical between
  the candidate base `1d08711` and my HEAD `33b7d56`. The only
  `Grammatik.lean` delta is an unrelated merged import
  (`FloatValidatorAdmission`); the candidate's import appends cleanly
  after `WordDrainInterleaving` (standard import-union at merge).
- Build evidence: final `./lean-probe` 0 errors; `./lean-bau` "Build
  completed successfully (460 jobs)"; every `#print axioms` within
  `[propext, Classical.choice, Quot.sound]`. Intermediate `sorryAx`
  states in the evidence log were repaired before the final commit
  (final probe lists `[propext]` for those theorems). `gabbro_ziel` is
  untouched (leaf import only), so its axiom set cannot have moved.
- Intel SDM cross-check (ch. Vol.2B 4-201-4-203, 4-530-4-532; Table 2-21
  Type 4): legacy PXOR `DEST := DEST XOR SRC`, PADDQ per-lane
  wraparound, both `DEST[MAXVL-1:128] unmodified`, Flags None, Numeric
  None — the model writes the full 128-bit XMM word, preserves rFLAGS,
  requires no MXCSR, and reads dest before writing (ModRM:reg r,w).
  Correct. Type 4 #UD (CR0.EM, CR4.OSFXSR, CPUID 0, LOCK→decode
  refusal since F0 is no canonical REX) and #NM (CR0.TS) are all in the
  gate. MOVDQA-#GP-on-misalignment / MOVDQU-never matches the manual.
  No defined effect is zeroed or ignored; no determinism is invented.

## Bounded acceptance notes (not repairs)

- XCR0 x87&&SSE is required for legacy SSE although Table 2-21 imposes
  XCR0 only on VEX rows: safe over-strength (refuses more, admits
  nothing unsound). Likewise REX-required decoding refuses valid
  non-REX encodings (inherited from the accepted producer).
- `.b32` profile label vs `.b64` admitted lanes is stated side by side
  in `vektorBreite_spur`, never redefined; reconciliation stays with
  the profile owner, as the author flags.
- Coverage honesty: PADDQ low-lane restatement and the ADD-fallback
  joint equality are absent (only halves); the author claims exactly
  "low-lane PXOR, high-lane PXOR/PADDQ", so nothing is overstated, and
  each follows from the producer in ~3 lines via `stepVectorHw_gleich`.
- The joint witness chains a scalar MOVSD store for the observable
  byte change because the admitted register forms correctly touch no
  memory; this is explicit in theorem and CUTS. `vektorSchreibZugelassen`
  carries no explicit no-wrap conjunct but feeds no execution (negatives
  only). `simdFreigabe` untouched; TSO/GX/source/budget/progress open
  in CUTS. Manual heading/page provenance stays OPEN (file absent in the
  author clone; I verified the rows above against the local snapshot).

## Remaining open / follow-ups

Single-line merge concern only: `Grammatik.lean` import-union with the
meanwhile merged `FloatValidatorAdmission` line. Suggested tiny
follow-ups (new lane, not this candidate): PADDQ low-lane gate
restatement, `skalarPaarAdd_gleich`, and — if ever needed — relaxing
the XCR0 conjunct for pre-XSAVE silicon as an explicit, separately
reviewed widening.

## Task remarks

The owner task text was truncated at 2000 chars in `lanes/674.md`, so
any requirement hidden in the tail (e.g. template-obligation naming)
could not be reviewed; everything visible is delivered or explicitly
cut. The missing-manuals situation the author reported is real for his
clone but the manuals exist locally; I checked the load-bearing rows
(PXOR/PADDQ operation, flags, exceptions, Type 4, MOVDQU alignment)
myself — citations above.
