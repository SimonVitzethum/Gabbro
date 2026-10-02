# MUSE-REPORT-683: Exact review of author 682 (MXCSR control byte execution)

CANDIDATE: 682 ed966d9be411e362a4fbdf602c8d7f92db806004
VERDICT: ACCEPT (bounded; no repairs required)

## Scope of this review

- Pinned snapshot from `.tmp/review/SNAPSHOT.json`: author 682, head
  `ed966d9b…`, base `e12bf1b9…`, files `MUSE-REPORT-682.md`,
  `grammatik/Grammatik.lean`, `grammatik/Grammatik/X86/FpControlHardwareForms.lean`, clean.
- Inspected: full 1311-line module, PATCH.diff (1409 lines), OWNER-TASK.md,
  BUILD-EVIDENCE.json, author report, and the local Intel SDM snapshot
  (`.tmp/HARDWARE-REFERENCES/`, edition 325462-093US, sha256-verified).
- Reviewer boundary: the candidate file is absent from this clone and this
  lane owns only this report, so no independent `./lean-bau` rerun was
  possible. Lean-green is taken from the author's queued evidence
  (`./lean-probe`: 0 errors; `./lean-bau`: 463 jobs, success) plus static
  inspection of every section, manual cross-checks of every architectural
  claim, and API-existence checks of every reused definition in current master.

## Architecture verification (independent, against the local manual)

- Byte forms: `NP 0F AE /2` LDMXCSR m32 and `NP 0F AE /3` STMXCSR m32,
  ModRM mod 10 + disp32 with the pilot SIB rule (`0x24` iff base code 4),
  optional `F0` LOCK. Opcode map confirmed in the local text
  (`NP 0F AE /2 … Load MXCSR register from m32`; `NP 0F AE /3 … Store
  contents of MXCSR register to m32`). Lengths 7/8 (+1 LOCK) proved;
  generic round trips for both forms and both SIB shapes.
- Semantics: `MXCSR := m32` / `m32 := MXCSR` confirmed verbatim. Reset
  `1F80H` confirmed. Reserved bits 16–31 → #GP confirmed (Vol. 1 §10.2.3
  text present locally). DAZ-without-support → #GP confirmed
  (MXCSR_MASK/FXSAVE passage: unsupported DAZ "is a reserved bit",
  write of 1 → #GP). STMXCSR stores reserved as `0s` confirmed.
  "No exception fires at load" confirmed (mask/flag change raises only
  on the next XMM/YMM instruction). Author models exactly this, including
  the FTZ-vs-source-admission split the task demanded
  (`mxcsrPos_ftz_weiter_aber_unzulässig`: hardware kind 0 + word installed,
  `fpEintritt` false via accepted `mxcsr_ftz_verweigert`).
- Faults: LOCK → #UD and register-ModRM → #UD confirmed as the silicon
  rule ("#UD If source operand is not a memory location. If the LOCK
  prefix is used."). Author maps LOCK to `fehlerUD` (planted, decided).
  Register-ModRM and mod 0/1 shapes decode to `none` → `verweigert`
  (refusal, never a wrong success or a wrong fault). This is the safe
  direction for a selected-forms module, is explicitly planted
  (`mxcsrDecode_register_verweigert`, field/opcode/truncation/lone-LOCK
  refusals), and is documented in CUTS ("unsupported encodings refuse
  explicitly"; "no mod 0/1 memory shapes"). No silent trust.
- Gates: SSE / CR0.EM / CR0.TS / CR4.OSFXSR as explicit `MxcsrSteuerung`
  data with the Type 5 class cited. Merging silicon #UD vs #NM into one
  `fehlerUD` is declared in CUTS, not hidden. Guard order (length →
  LOCK → gates → four-byte access → reserved/profile check) matches
  silicon priority; permission failure yields refusal, never a fabricated
  fault, so no #PF/#SS-vs-#GP inversion is claimable.
- Widths: load via `read32`, store via `write32` with the low-16
  word (`mxcsrSpeicherWort`), low-bits preservation and store/reload
  round trip proved. No 8-byte access stands for the 32-bit access
  anywhere. Neighbor-byte, code-byte, permission, flag, GPR and XMM
  frames proved for both successes.
- Masks as profile data: modern `0xFFFF`/DAZ vs legacy `0xFFBF`/no-DAZ
  instances with silicon values deferred to FXSAVE per the manual; the
  reset-word theorem honestly carries its mask premise instead of
  claiming all masks. No universal guessed mask.
- Reuse: every reused name verified present in current master
  (`MXCSR`/`mxcsrBit`, `read32`/`write32`/`write32_rahmen`,
  `effAddr`/`ripNach`/`laengeOk`, `geholt`/`ausfuehrbarN`,
  `fpEintritt`/`kontextReset_gueltig`/`mxcsr_ftz_verweigert`,
  `modrmMem`/`regLow`/`codeReg`/`parseLe32_cons`/`length_leBytes32`,
  `byteNat_natByte_of_lt`, `vecJoin`, `zeugeFlags`). No change to
  `ScalarFloat`, entry profiles, or any source/checker/Spec/goal/emitter
  file; PATCH touches only the new module, one additive umbrella import,
  and the author report. No ExtendedExecution edit; the §6 adapter
  (`mxcsrByteschritt` in, `MxcsrAusgang` + kind/observer accessors out)
  leaves integration to lanes 660/670/672/674, stated on both sides.

## Proof hygiene

- No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (word-boundary grep
  clean; only "admitted" in comments). No Prop-typed premises. No
  source-syntax quantification, so rule 13 needs no `_zeuge`; a joint
  non-degenerate fetched witness is still proved (`mxcsr_gelenk_zeuge`:
  real control change 0x1F80→0x1FBF plus real memory change at 0x2004
  with read-back, neighbor/code frames, past-image refusal).
- Negatives each vary one leg (reserved #GP, LOCK #UD, OS-gate #UD,
  silicon #UD, DAZ #GP, 4th-byte store/load permission refusals) plus
  codec-level malformed refusals; positives cover reset-word admission.
- CUTS block is precise (no VEX/REX/mod-0-1/FXSAVE composition; #NM
  merged; masks are example data; no TSO/tearing/timing/cost/source
  claim; partial save ≠ full context preservation for 672/674/660).
  `#print axioms` for all 82 theorems, all within
  {propext, Classical.choice, Quot.sound} per build evidence.

## Non-blocking observations (not repairs)

- Report says "81 theorems"; the file has 82 `theorem` lines (+33 defs).
  Immaterial.
- One identifier is German with a non-ASCII character
  (`mxcsrPos_ftz_weiter_aber_unzulässig`); the module otherwise follows
  the X86 directory's German naming convention. No semantic effect.
- TSO/tearing granularity of the four-byte access and #AC stay open per
  CUTS; nothing concurrent is claimed, so this is a correct boundary,
  not a gap in a claimed result.

## Result

Exactly one CANDIDATE: 682 ed966d9be411e362a4fbdf602c8d7f92db806004.
Exactly one VERDICT: ACCEPT — bounded to the two selected mod-10 disp32
forms with the documented refusals and open compositions above. No
guarantee weakened, no desired simulation assumed, no fake closure found.
