# MUSE-REPORT-939: Exact review of author 789 (CVTSI2SD from 64-bit int)

## Task

Lane 939: report-only exact review of author 789 (Hardware completion:
CVTSI2SD from 64-bit int). Own only `MUSE-REPORT-939.md`. Independently
inspect the exact pinned snapshot/task/PATCH and official local reference
manuals. Review architecture, not just Lean green: byte forms,
REX/register/width/flag semantics, source/destination/implicit operands,
pre-fault effects, memory access order, TSO/atomicity, feature/MXCSR/
interrupt enable gates, interaction with canonical execution. Verify all
major premises used, actual non-degenerate reached witnesses and negative
mutations, no guarantee weakening/desired simulation assumption, precise
CUTS/claim boundaries.

## Candidate

CANDIDATE: 789 168e0eb28bfbdc32c7d92373d7cc48867757e7cb

Base from `SNAPSHOT.json`: `56537272a31df3de5d9b7898bbade91c3de817b8`
(which matches this clone's HEAD at review start). Files:
`MUSE-REPORT-789.md`, `grammatik/Grammatik.lean`
(one added import), `grammatik/Grammatik/X86/Cvtsi2sdW64.lean` (new,
324 lines). Snapshot reports `clean: true`.

VERDICT: ACCEPT

Bounded acceptance: integration must confirm a quiet-machine whole-project
`./lean-bau` green after adding the one import. The candidate's own module
is probe-green with standard axioms (evidence below); the author recorded
5 whole-build attempts all failing at the final `Grammatik.lean` link step
(`[484/485]`) with varying resource errors, plus the same failure on an
unrelated large module. No semantic repair is required.

## What was inspected

- `.tmp/review/SNAPSHOT.json`, `.tmp/review/author-789/OWNER-TASK.md`,
  `MUSE-REPORT-789.md`, `PATCH.diff` (full 459-line diff read),
  `BUILD-EVIDENCE.json` (all probe/build entries).
- Snapshot candidate file
  `.tmp/review/author-789/grammatik/Grammatik/X86/Cvtsi2sdW64.lean`
  (all 324 lines read).
- Base foundations in this clone (read-only, no edits):
  `grammatik/Grammatik/X86/ScalarFloatHardwareForms.lean`
  (encode `fpHwEncodeCvtsi`, REX `fpHwRex`, decoder, W0/memory refusal
  pins, pilot pins, fetch `fpHwFetchDekodiert`, gate
  `fpHwCvttZugelassen`, byte step `fpHwByteschritt`, W2 witness
  `fpHwW2T/T1/T2`, `fpHwW2_fetch1`, `fpHwW2_schritt1/2`,
  `fpHwW2_liest/aendert`),
  `grammatik/Grammatik/X86/ScalarFloat.lean`
  (`cvtsiErg`, `fpSchritt`, `fpSchritt_cvtsi2sd*`, `xmmTief/Hoch`,
  `xmmSchreibeTief*`, `fpEintritt`),
  `grammatik/Grammatik/X86/Gleitprofil.lean`
  (`mxcsrRundungRNE`, `mxcsrGueltig`, `FPKontext`).
- Official local manual `.tmp/HARDWARE-REFERENCES/`:
  `REFERENCES.json` (Intel SDM combined Vols 1-4, edition 325462-093US,
  September 2026, sha256 `a4a62e6...`, 26664929 bytes) and
  `intel-instruction-reference.txt` lines 48886-49000 (read directly).
- Forbidden-pattern scan of the candidate file: matches are only English
  prose (`admitted`, `admitted MXCSR`, `never native_decide` in CUTS);
  no `sorry`/`admit`/`axiom`/tactic-`native_decide`/`unsafe`,
  no `intro _` / `have _ :=` in code.

No wrapper re-run of the candidate module was possible in this clone:
this review owns no source and the candidate file is not present in this
tree (base only); applying the patch would violate the own-only rule.
Base-foundation reads plus `BUILD-EVIDENCE.json` probe records plus direct
manual-text reads are the evidence. A `bash` attempt to list lane/task
files beyond `read` was rejected by the permission classifier, so no
`./lean-probe`/`./lean-bau` was launched from this review; this is
recorded as a partial-status limit, not as candidate evidence against.

## Architecture findings

Byte forms (grounded): the claimed 5-byte row is the accepted
`fpHwEncodeCvtsi` (`[242, fpHwRex 1 .., 15, 42, modrmReg ..]`, i.e.
F2, REX.W=1, 0F escape, opcode 2A, ModRM mod=11). Order
mandatory-prefix then REX then escape matches the accepted header comment
(Vol.2A 2-7f). Manual opcode rows verified at txt 48890-48895:
`F2 0F 2A /r` (`r32/m32`) vs `F2 REX.W 0F 2A /r` (`r/m64`). Description
verified at txt 48921-48924 (signed doubleword/quadword to double, low
quadword stored, high quadword unchanged, inexact rounded per MXCSR.RC).
Operation verified at txt 48969-48976 (`DEST[63:0]` 64-vs-32 split,
`DEST[MAXVL-1:64]` unmodified). Provenance lines in report and file
header match the text exactly.

REX/register/width: `fpHwRex` is `0100WRXB` with X=0; W=1 selects the
r64 source the accepted `cvtsi2sd` converts whole (`cvtsiErg w = ofInt
f64 w.toInt`, whole 64-bit register). W=0 refusal
(`cvtsiW64_w0_verweigert` over inherited
`fpHwDecode_cvtsiW0_verweigert`, `rfl`) is the correct doubleword-source
distinction (txt 48890). Memory-source refusal
(`cvtsiW64_speicher_verweigert` over inherited
`fpHwDecode_cvtsiSpeicher_verweigert`) is correct: no `FpBefehl`
constructor and no second evaluator exist. Both are explicit negative
mutations, not silently admitted.

Source/destination/implicit operands: dst XMM, src GPR, ModRM
reg=destination / r/m=source per accepted comment and manual operand
table (txt 48916: `ModRM:reg (w)`, `ModRM:r/m (r)`). No implicit operand
is claimed. Execution projections cover exactly the observables:
low half converted (`cvtsiW64_rechnet`), flags preserved
(`cvtsiW64_flags`), no memory byte changed (`cvtsiW64_speicher`), high
half preserved (`cvtsiW64_hoch`, legacy SSE preserve per txt 48976,
implemented by `xmmSchreibeTief` keeping `xmmHoch`), RIP past decode
length (5th conjunct of `Cvtsi2sdW64_verbindung`). No invented
zeroing of the high half (VEX zeroing correctly not applied to legacy
form).

Pre-fault effects / memory order / TSO / atomicity: register-only
conversion performs no memory access, so the memory-preservation lemma
is the right frame; the second witness step is a separate fetched MOVSD
store with its own permission-gated execution. Fetch travels as an
explicit premise (`hf : fpHwFetchDekodiert t = some (d, rest)`) with
length-consistency and `ausfuehrbarN` guards inside the accepted
definition, so conclusions are reached from bytes in actual memory,
never from a caller-supplied decoder value. Everything is sequential
over one `Speicher`; CUTS explicitly claims no TSO/concurrency,
cost/timing, ABI/loader/entry/budget, or whole-image result. No
conjunction-of-checks is called execution: each §4 lemma runs the
accepted `fpSchritt` equation via the accepted gated byte step
(`fpHwByteschritt_schritt` + `fpSchritt_cvtsi2sd*`).

Feature/MXCSR/interrupt gates: profile admission is the accepted
`fpEintritt` (= `mxcsrGueltig`: RNE + FTZ off + DAZ off + all masks),
`cvtsiW64_profil_rne` projects RNE control out of it (used proof,
no discarded premise). `fpHwCvttZugelassen` is trivially true for
`cvtsi2sd` (only `cvttsd2si` is gated) but is still carried as an
explicit premise and consumed via `fpHwByteschritt_schritt` in every
§4 lemma and the connection, so no gate is bypassed. Sticky MXCSR flags,
DAZ/FTZ execution, SNaN, and unmasked traps are unmodelled; the file
does not conclude anything about MXCSR post-state (the connection has
no MXCSR conjunct) and CUTS books these as inherited gaps of
`Gleitprofil` §7 / not claimed. That is sound abstraction with a
precise boundary, not invented determinism: no defined effect is
asserted falsely, and no undefined state is given a concrete value.

Canonical interaction: no new machine, decoder row, evaluator, or IEEE
arithmetic. All §1-§2 facts are inherited pins (`fpHwLen_cvtsi`,
`fpHwRoundtrip_cvtsi`, `fpHwPilot_weist_cvtsi_zurueck`,
`fpHwDecode_cvtsiW0/Speicher_verweigert`); §3 is definitional `rfl`
links (`cvtsiErg = ofInt`, `ofInt = rundeExakt ⟨z,0⟩`, hence RNE) plus
the profile projection and the inherited `cvtsiErg_42`
(`42 -> 0x4045000000000000`); §4-§5 run accepted step equations. No
duplicated interpreter, no overlapping writer of canonical vocabulary.
Scope discipline holds: no diagnostic/gift/example/CLI numbers, no
`MARKE_EMIT` change, no source/checker/Spec/goal/emitter edit, no
friend-reserved optimiser file (only the one import line added).

Premise use: every premise of `cvtsiW64_rechnet/flags/speicher/hoch`
and `Cvtsi2sdW64_verbindung` is consumed (via `hok`, `hstep`, `heq`
chains; the RIP leg re-derives the step equation rather than assuming
it). No `Prop`-typed premise; no conclusion restates a premise; no
contract quantification issue (hardware lane, no `Vertrag` premise).

Witness (`Cvtsi2sdW64_verbindung_zeuge`, the ZEUGE target): jointly
instantiates ALL connection premises on the accepted W2 image
(`.xmm0`/`.rax`, `fpHwW2T/T1`, `⟨.cvtsi2sd .xmm0 .rax, 5⟩`,
`fpHwEncodeMovsdSpeichere .rbx .xmm0 0`, `fpHwW2_fetch1`, `rfl`,
`fpHwW2Fp`, `fpHwW2Gate1`, `fpHwW2_schritt1`), concludes the converted
value via the connection itself, plus a reached second fetched store
step (`fpHwW2_schritt2`) with a real memory change
(`fpHwW2_liest`: word reads back `0x4045000000000000`;
`fpHwW2_aendert`: top footprint byte changed). Non-degenerate and
memory-changing as required. Verified each reused name exists in base
with the claimed statement. The §2 width refusals are separate pins,
not conjuncts of the witness; the report prose mentioning them
alongside the witness does not overclaim inside the theorem.

Axioms: per `BUILD-EVIDENCE.json` final probe, marker/width/RNE-identity/
42 with no axioms; round trip, pilot/width refusals, profile-RNE with
`[propext]` (plus `[Classical.choice, Quot.sound]` on the memory-decode
refusal via inherited `parseLe32`); step/connection with
`[propext, Quot.sound]`; joint witness with
`[propext, Classical.choice, Quot.sound]`. All within the standard
`gabbro_ziel` set. CUTS + `#print axioms` for every main theorem are
present; file ends with `end Gabbro.Grammatik.X86`.

CUTS precision: proved vs explicitly-not-proved is correctly bounded
(no silicon correspondence; NaN class-only; deliberate W=0/memory/
VEX/EVEX/packed/x87/FMA refusals as incompleteness; no TSO/cost/ABI/
whole-image/source claim; `decide` closed evaluations, never
`native_decide`). The open concrete-inexact (`2^53+1` ties-to-even)
`decide` is honestly booked; the abstract `ofInt IS rundeExakt RNE`
link satisfies the task's RNE requirement without it.

## Verification status

- `./lean-probe grammatik/Grammatik/X86/Cvtsi2sdW64.lean`: per author
  `BUILD-EVIDENCE.json`, final `== 0 error(s) in the COMPLETE output;
  exit 0` with the axiom list above. Not re-run from this report-only
  review (see limit above).
- `./lean-bau` (whole `grammatik/`): NOT green at author report time;
  5 attempts reach `[484/485] Building Grammatik` then fail the final
  import-all link with varying `std::bad_alloc` / `failed to create
  thread` / stale `.olean.private` reads; an unrelated large module
  (`VectorIntegerHardwareForms.lean`) fails the same way, supporting
  machine-wide resource exhaustion under ~15 concurrent models rather
  than a file defect. This review accepts that apparatus reading; the
  quiet-machine re-run remains as the integration bound.
- No guarantee weakened, no desired-simulation premise, no fake closure
  found. Nothing in the owner task is believed wrong.

## What remains open (not this lane)

- Quiet-machine `./lean-bau` confirmation at integration.
- Concrete large-inexact `decide` (booked, optional).
- Silicon correspondence (OPEN by design).
- Inherited gaps: NaN payloads, sticky MXCSR flags, DAZ/FTZ, traps, TSO,
  timing, loader/entry/budget, dispatcher integration.

## Reproduction note

Suspicious-case reproduction via queued wrappers: none required. The two
refusal pins are closed `rfl`/`simp` evaluations over the accepted
decoder; manual text was read directly to confirm the refused shapes
(W=0 doubleword row, memory-source row) are the correct neighbours.
No byte case looked suspicious on independent inspection.
