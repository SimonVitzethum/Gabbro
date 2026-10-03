# MUSE-REPORT-904: Exact review of author 754 (zero idiom XOR reg, reg)

Lane 904, clone `/home/simon/Dokumente/gabbro-muse/a904`, branch `muse/904` (verified via `.git/HEAD`: `ref: refs/heads/muse/904`).
Own file only: `MUSE-REPORT-904.md`. No source, control, or live-queue files touched.

CANDIDATE: 754 51afe820c69e2291dc60463c8096a8adf7bd343e
VERDICT: ACCEPT (bounded; see §6 for the exact scope and non-blocking follow-ups)

## 1. What was reviewed

Exact pinned snapshot from `.tmp/review/SNAPSHOT.json`:

- author 754, head `51afe820c69e2291dc60463c8096a8adf7bd343e`, base `23b9a42fb44f2365b636cf8a9c440a2dfd8cae50`, clean true.
- files: `MUSE-REPORT-754.md`, `grammatik/Grammatik.lean` (+1 import), `grammatik/Grammatik/X86/ZeroIdiomXor.lean` (new, 603 lines per PATCH).
- owner task: `/.tmp/review/author-754/OWNER-TASK.md` (lane 754: 31/r zero idiom ONLY with flag-liveness site proof; ZEUGE `ZeroIdiomXor_verbindung` + companion).
- patch: `.tmp/review/author-754/PATCH.diff` (read in full).
- build evidence: `.tmp/review/author-754/BUILD-EVIDENCE.json` (full lean-probe iteration history + final lean-bau success).
- reference index: `.tmp/HARDWARE-REFERENCES/REFERENCES.json` (Intel SDM combined vols 1-4, edition 325462-093US, Sept 2026) plus the local extracted text `intel-instruction-reference.txt`, checked independently below.

No network, no other clones, no keys. This is a report-only review; no source was modified.

## 2. Architecture verification (independent, not just Lean-green)

Byte forms: author routes `encodeZero r = encode (.xorReg64 r r)` through the accepted pilot. Pilot `Codec.lean` encodes `xorReg64` as `[rexByte, 49, modrmReg]` (opcode 31, decimal 49) and decodes opcode 49 to `xorReg64` only; opcode 33 (RM form) is not a pilot row, so "31/r ONLY" matches the pilot exactly. Pinned bytes `XOR rax, rax = [72,49,192]` (0x48,0x31,0xC0: REX.W + 31 + ModRM C0, register-direct, both fields zero) verified against the local manual text: line 138281 `REX.W + 31 /r  XOR r/m64, r64  MR  Valid  N.E.` (§ "XOR—Logical Exclusive OR", Vol. 2D 6-40 opcode table). Length 3 for every register is proved by `encodeZero_laenge` (case split + decide); pilot bound 1..15 respected.

REX/register/width: 64-bit register-direct only. REX.R/B handling is inherited from the pilot (`rexByte (regHigh src) (regHigh dst)`), round trip proved for all 16 registers. 32/8/16-bit forms, memory operands, and `SUB r, r` are out of scope and explicitly refused (see §4), with CUTS honest. This matches the task's "31/r zero idiom ONLY".

Flag semantics: author reuses canonical `Wort.xor64` and `Ganzzahl.LogikGueltig`, proving `xor_selbst_null` (`x ^^^ x = 0` via `BitVec.xor_self`), `xor_selbst_flags` (CF=false, PF=true, AF=none, ZF=true, SF=false, OF=false for the zero result), and `xor_selbst_gueltig`. Independently verified against the local manual: lines 138320-138321 "The OF and CF flags are cleared; the SF, ZF, and PF flags are set according to the result. The state of the AF flag is undefined." The snapshot `Flags.mk false true none true false false` is exactly (cf=false, pf=true, af=none, zf=true, sf=false, of=false), i.e. parity-even/ZF-set/SF-clear of the zero result. Field order confirmed against `Typen.lean` (`cf pf af zf sf of`). AF=none is the sound abstraction of undefined (per `Typen.lean` CUTS: "AF = none represents an undefined architectural auxiliary flag, not false"). No invented determinism, no zeroed/ignored defined effect.

Source/destination/implicit operands: both operands are the same register; destination receives zero; no implicit operands. `zeroSchritt_fremd` keeps every other register (`regSet_fremd`).

Pre-fault effects and memory access order: register-only step; `zeroSchritt_speicher` proves `s'.speicher = s.speicher` via accepted `schritt_xorReg64_speicher`; `zeroSchritt_ok` shows success implies `laengeOk`. Manual exception lists (lines 138323-138354) confine faults to memory operands (plus LOCK misuse); a 3-byte register-direct row has no fault arm. LOCK-prefixed bytes are not the pinned row and fall into pilot `none`, hence refused. No memory access order or permission change exists by construction.

TSO/atomicity: no memory access, no LOCK, no store-buffer effect. Author claims none and explicitly does NOT claim a TSO/GX bridge (CUTS). Correct bounded treatment; the missing target leg is not assumed (existing source `schwach_ist_gX` untouched).

Feature/MXCSR/interrupt gates: integer XOR needs no SSE/AVX, no MXCSR, no feature gate. Dispatcher link `zeroSchritt_laufAlt` / `zeroSchritt_stepExt` runs the idiom through accepted `laufAlt` and unified `stepExt` pilot arm (`stepExt_pilot`), with XMM/FP untouched and `kern` carrying the zero successor. No second interpreter, no duplicated arithmetic/decoder: `zeroSchritt_ist_schritt` is `rfl`, `decodeZero_ist_pilot` links filter success to pilot decode without re-deciding rows.

Canonical-execution interaction: every admitted final byte executes through the common `Ausfuehrung.schritt`; unsupported neighbours refuse explicitly (see §4).

## 3. Premises, witnesses, mutations

All major premises used: each value/flag/memory/RIP/dispatcher conclusion discharges through the cited accepted lemmas (`schritt_xorReg64`, `schritt_xorReg64_speicher`, `schrittRegister_flags/rip`, `regSet_gleich/fremd`, `roundtrip_xorReg64`, `roundtrip`, `stepExt_pilot`), with no `sorry/admit/axiom/native_decide/unsafe` in the PATCH and no discarded premise pattern visible in the diff. Axioms per `#print axioms` in build evidence are within `[propext, Classical.choice, Quot.sound]` (several depend on fewer).

Target `ZeroIdiomXor_verbindung` (bytes + zero value + clobbered flags with `LogikGueltig` + untouched memory + RIP+3 + live-demand refusal) and companion `ZeroIdiomXor_verbindung_zeuge` present with the exact ZEUGE names. The companion jointly instantiates canonical bytes (`roundtripZero .rax []`), the executed zero step from 42 (`schritt_xorReg64` on `zeroZeugeStart`), ZF-live demand (`zeroBedarfLebendig`), register/flags facts, and a reached three-step run `progZero = [xor rax,rax; mov rbx 7; store [rsp] rbx]` with `(lauf progZero s)` storing byte 7 at 8192 (from 0, permissions kept). Non-degenerate and memory-changing, following the ShiftCodec witness pattern cited in the author report. The source-level "table" wording of HARD RULE 13 has no X86 literal counterpart; the store-changing reached run is the correct analogue and is present.

Negative mutations present: `decodeZero_verweigert_fremd` (distinct-register XOR), `decodeZero_verweigert_nicht_xor` (every non-XOR pilot form, any suffix), `pin_nachbarn_verweigert` (MOV/ADD/SUB/CMP same-register neighbours), `sonde_zero_abgeschnitten` (empty/lone-REX/REX+opcode truncation), `ersetze_verweigert_bei_lebendig` (live demand refuses) with positive twin `ersetze_erlaubt_bei_tot` and `darfNullen_heisst`.

## 4. No weakening, no desired-simulation assumption, precise CUTS

No guarantee weakened: value/flags/memory/RIP/dispatcher facts are equalities over reused canonical operations, not weakenedexistentials; refusal (`none`) is never presented as an architectural fault (CUTS says so explicitly). No desired-correctness premise manufactured: the step IS the pilot step, the dispatcher arm IS the accepted pilot arm. Codec round trip is explicitly NOT presented as hardware fidelity (file header + CUTS).

CUTS block is precise and matches the code: proved (canonical 31/r bytes, filter decoder + filter-correctness link, general refusals + pins, value/flags/validity, length-checked step facts, site liveness admission/refusal, site connection, joint witness, dispatcher link); NOT proved (no silicon correspondence — stated SDM rows only; no 32/8/16-bit, memory-operand, or SUB idiom; no program-wide liveness/optimiser claim; no TSO/GX bridge; no cost/time/source/checker/Spec/goal claim). The author report's "What remains open" matches the file CUTS.

Scope hygiene: PATCH touches only the two owned Lean paths plus the author report; no diagnostic/gift/example/CLI numbers, no MARKE changes, no source/checker/Spec/goal/emitter edits, no friend-reserved optimiser files. `Grammatik.lean` diff is one import line.

## 5. Build status

Author build evidence (`.tmp/review/author-754/BUILD-EVIDENCE.json`): `./lean-probe` ends `== 0 error(s)`, full axiom dump within standard axioms; final `./lean-bau` ends `Build completed successfully (483 jobs).` Two transient apparatus failures preceded it (exit-134 thread creation on aggregation; one stale olean read), both retried clean with no proof change — consistent with the known virtual-address/build-load ceiling, not content.

Own verification in lane 904: full file/PATCH/manual/canonical-interface reads as above. No independent `./lean-bau`/`./lean-probe` run was possible in this session: the `bash` tool (required for `./lean-bau`, `./lean-probe`, `./commit.sh`) returned a permission rejection, so no queued-wrapper execution or commit could be performed here. This report file is written and ready; commit through `commit.sh` is pending a session with build/commit tools enabled. No red or green claim is made for this clone beyond the author's pinned evidence and the read-level verification above.

## 6. Bounded acceptance and non-blocking follow-ups

ACCEPT is bounded to the CUTS: 64-bit register-direct 31/r same-register rows only; flag snapshot exactly as §2; register-only (no memory/TSO/fault) treatment; site demand as data with no program-wide liveness or optimiser claim; no silicon correspondence beyond the stated manual rows.

Two follow-ups, explicitly NOT blockers for this candidate:

1. AF in the site demand: `FlagBedarf` tracks CF/PF/ZF/SF/OF with AF absent by construction. The hardware abstraction (AF=none) is sound, but a future optimiser consumer replacing a flag-preserving op (e.g. `MOV r, 0`) with the idiom where AF alone is live would be admitted by `darfNullen`. Before any optimiser use, add an `af : Bool` demand (refuse where live) or prove AF-unobservability at the use site. Today there is no optimiser claim, so this is latent and bounded by CUTS.
2. Manual citation precision: the file header cites edition 325462-093US and the XOR r/m64 entry/flag chapter without exact heading lines. Independently confirmed here as Vol. 2D 6-40 opcode table (line 138281) and Vol. 2D 6-40 flags paragraph (lines 138320-138321). A one-line citation with those headings would close the task's "exact heading/provenance" wording; substance (bytes/flags) already matches.

Minimal repairs if a future lane wants them: (1) extend `FlagBedarf` with `af`, update `darfNullen`/`Lebendig`/`darfNullen_heisst` and the two `ersetze_*` proofs; (2) add the two heading citations above to the file header. Neither is required to accept the present bounded connection.

## 7. Task remarks

Nothing in the owner task statement is wrong. The 31/r-only scope, canonical-reuse constraint, explicit-refusal requirement, and ZEUGE shape are all met as specified. The inhabitation note from the author report is agreed: the X86 non-degeneracy analogue is the store-changing reached run, which is present.
