# Upstream PR-2 ISA review (lane 714)

Review of upstream PR 2 (pinned head `987b286df9d8465714a00bab8226f7b9c7f4afc1`,
base `5d5a72e5889a3063b417b955fa7824e72c52ef7c`) including its dependency
upstream PR 1 (head `5d5a72e5889a3063b417b955fa7824e72c52ef7c`, base
`26c58bd41b2c6ad413b54c08c646c1313e4b297e`). Read from the exact pinned
snapshots under `.tmp/UPSTREAM-PRS/pr-1` and `.tmp/UPSTREAM-PRS/pr-2`
(public PR files copied into this clone, not author clones), plus the
commits themselves where present in local history. No source, import,
witness, test or semantics file was changed by this review.

## 0. Verdict

**REJECT the pinned commit as-is; the content is conditionally acceptable
after repair.** The Lean modules are individually sound, carefully
delegated (no duplicated evaluators) and honestly scoped (CUTS blocks
state exactly what is not proved; no `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe` anywhere in the 27 new files), and the Rust
side is explicitly untrusted with its limits written down. But the
pinned commit **does not build**: the root `Grammatik` target fails on
two exact-name collisions (§8, I0; reproduced in §9 on the exact
snapshot). Per-module builds pass only because the colliding modules
never import each other -- the PR's "full `lake build` fails only in
`Parser/ElementTiefProben.lean`" claim is false for the pinned tree.
On top of that, the PR was built on old master (`26c58bd4`) and does
not know the accepted unified dispatcher (`decodeExt`, lane 575), the
coherent multicore execution (`HardwareExecution`, lane 660), the
integer hardware rows (`IntegerHardwareForms`, lane 666) or the address
encoding (`AddressEncoding`, lane 664) that current master has. Merging
as-is creates two competing unified integer machines side by side. The
MUST-FIX list in §8 is the minimum repair + rebase/unification work;
none of it weakens a guarantee.

Companion dependency verdict (PR 1, optimizer rules): same shape --
technically sound and honestly scoped, but it writes the two
friend-reserved paths (`grammatik/Grammatik/X86/OptimizationRules.lean`,
`OptimizationWitnesses.lean`, AGENTS.md §3). Its own commit message says
it "re-applies the first friend delivery", i.e. it claims to BE the
authorized friend content. Accepting that claim is an owner decision,
not a reviewer grant; do not silently merge over the reservation.

## 1. What was reviewed

- PR 1: 7 commits, 4 files (`Grammatik.lean` +2 imports,
  `OptimizationRules.lean` 1302 lines, `OptimizationWitnesses.lean`
  615 lines, `OPTIMIZER.md` +140/-17). PR-1 optimizer files are
  byte-identical in the PR-2 snapshot (verified with `diff -q`).
- PR 2 on top of PR 1: 55 commits, **27 files, +31296/-0 (purely
  additive)**. Only two existing files are touched, both additively:
  `grammatik/Grammatik.lean` (+18 import lines) and
  `crates/gabbro-check/src/x86/mod.rs` (+12 lines of `pub mod`
  declarations). No existing theorem, definition, test or byte is
  modified.
- New Lean files (lines): `ISA` 1744, `ISAExecution` 593,
  `ISASelect` 1293, `ISARelax` 1211, `CompactForms` 1407,
  `IntegerCore` 1142, `Pipeline` 2478, `PipelineImage` 2167,
  `PipelineEntry` 493, `ExpressionLoweringDeep` (deep lowering) plus six
  witness files (`ISAWitnesses` 690, `ISASelectWitnesses`,
  `ISARelaxWitnesses`, `CompactFormsWitnesses`, `IntegerCoreWitnesses`
  550, `PipelineWitnesses` 936, `PipelineImageWitnesses` 1984,
  `ExpressionLoweringDeepWitnesses`).
- New Rust files: `codec.rs` 772, `opt.rs` 2019, `pipeline.rs` 2119,
  `elf.rs` 257, `lower.rs` 390, goldens `codec_golden.rs` 4372,
  `pipeline_golden.rs` 2037 (total ~12k lines, all additive).
- Local history contains both PR heads and PR-1's base, so every number
  above is measured, not quoted. Current master HEAD here is `011ff474`,
  170 commits ahead of PR-2's base.

## 2. Method

Independent full read of the ISA file family and witnesses; targeted
reads of `Pipeline`/`PipelineImage`/`PipelineEntry` closing theorems,
`ExpressionLoweringDeep` freshness discipline, Rust `codec`/`opt`/
`pipeline`/`elf`/`lower` module docs and golden provenance headers;
mechanical audits over the exact snapshot files (forbidden tactics,
`#print axioms` presence, `CUTS` presence, golden-case counts);
comparison against the accepted baseline in this clone
(`ExtendedExecution`, `HardwareExecution`, `IntegerHardwareForms`,
`AddressEncoding`, pilot `Befehl` in `Typen.lean`, `Bild`,
`EntryExecution`/`EntryState`, `ShiftLogic`, `Ganzzahl`, `NarrowOps`);
disposable-fixture reproduction (`.tmp/fixture-pr2`, ignored scratch):
snapshot trees + copied queued wrappers + warm clone-local
`grammatik/.lake`, full `./lean-bau` run (see §9 for the result log).
No network, no push, no outside-clone reads. Rust was audited
statically only (see §9 for why no fixture cargo run is claimed).

## 3. Reference provenance

Official input Vol. 2 instruction-set facts were checked against the
clone-local snapshot `.tmp/HARDWARE-REFERENCES/`:
`intel-instruction-reference.{pdf,txt}` (273804 text lines),
`REFERENCES.json`: Intel SDM combined volumes 1-4,
edition **325462-093US, September 2026**,
`sha256 a4a62e6a7ba11a76c7753a195b825087306812aac39b930973f9168ee599f321`,
verified 2026-10-02. Scope: Intel-profile architectural evidence only;
AMD retrieval failed upstream and no AMD provenance is available, so no
vendor-difference claim is made. Nothing below claims silicon proof:
the PR's own CUTS blocks say the same ("decoding and stepping agree
with the family models, not with silicon"; "self-consistency (round
trip) only, not verified against silicon").

## 4. Per-area verification

**Decoder disjointness (strongest part).** `familien_disjunkt`
(`ISA.lean:1134`) holds over ARBITRARY byte strings: every accepting
family decoder forces one 3-byte signature `famOf`, and the eight
signatures are pairwise different, so `decodeI`'s priority order is
irrelevant (`decodeI_eindeutig`). Every genuinely shared prefix is
separated at byte 2 or 3 with a boundary probe on each side: REX.W+`0F`
(`AF`=muldiv vs `40..4F`=cmov vs `B6/B7/BE/BF`=core, `grenze_0f`);
`F7` ModRM digit 2/3=core NOT/NEG vs 4/6/7=muldiv (`grenze_f7_ziffer`);
`89`/`8B` ModRM mod 0/1=compact vs 2/3=pilot (`grenze_8b_modus`);
`41 B8`=compact `movImm32Zx r8` vs `41 50`=pilot `push r8`
(`grenze_kopfbyte`); `C7/83/81`=compact; `8D/21/09/85/63`=core;
REX.WX `74..79`=core LEA-with-extended-index only
(`grenze_movsxd_rexx`); `EB/70..7F/B8..BF`=compact first bytes.
Overlapping-prefix refusals are pinned as poison probes
(`gift_rexw_setcc`, `gift_rex40_cmov`, `gift_rex41_imul`,
`gift_rexwr_shift`, `gift_rex_x`, `gift_rex_kern`). The one changed
probe is honest: `48 0F B6 C1` used to be refused and is now
`movzx64From8` (`grenze_rexw_movzx`), recorded as a change, not hidden.
Disjointness is over the eight ADMITTED fragment decoders; bytes no
family accepts are refused, and nothing is claimed about x86 forms
outside the subset (ISA CUTS). The pilot's `89`/`8B` rows genuinely
refuse mod 0/1 (`decodeRex_sig`), so compact memory rows extend rather
than collide.

**Lengths.** Every family proves 1..15 (`encodeI_len`); truncation is
refused per family (`gift_abgeschnitten`, `gift_abgeschnitten2`).
Minor doc fix (§8, M2): `encodeC_len`'s comment says "2..7 bytes" but
proves the loose `1 ≤ len ≤ 15`.

**REX/prefixes/high bytes.** Single-REX rows only; multi-REX and
`66/67/F0/F2/F3` prefixed strings are refused (safe direction:
refusal, never a wrong decode). High bytes (`AH..DH`) are never
produced: encoders emit only REX-aware low-byte mappings. One gap:
no dedicated probe pins the SETcc byte-register mapping under REX
(`rm=4..7` must be `SPL/BPL/SIL/DIL`, never `AH..DH`); the MOVZX
W=0/W=1 split is probed (`grenze_0f`) but SETcc is not (minor, §8 M3).

**Widths and sign extension.** All match the SDM: `B8+rd` without REX
is the 32-bit zero-extending move (compact `movImm32Zx`, correct use
of the bare-`B8` head); `C7/0` sign-extends (`movImm32Sx` via
`dispWort`); `83 /n ib` sign-extends disp8 (`dispWort8_eq_signExtend`
reuses the pilot's own `dispWort`); `81 /n id` takes disp32; LEA
scales are exactly 1/2/4/8 (`scaleFromBits`); `rsp` index is
unrepresentable and its bytes decode as the index-free LEA
(`gift_nicht_kanonisch2` pins both halves); `rbp`/`r13` disp0 is the
RIP-relative row and refused as disp0 (`kanonischI` + decoder agree).

**Flags.** AND/OR/TEST reuse `andW`/`orW` = `(andB/orB, logikFlags)`
(CF/OF cleared, AF=`none`=undefined-never-false, width-correct sign);
NOT preserves flags exactly; NEG reuses `negWf` (`NegGueltig`,
fully defined); MOVZX/MOVSX preserve flags; CMP writes flags only;
shifts mask the count (`%64` full, `%32` narrow), preserve everything
on masked-zero, and define OF exactly for masked-one. All SDM-correct.

**LEA/address/faults.** `coreSchritt` LEA is pure computation
(`base + index*scale + sext32(disp)` mod 2^64, reusing `shlB`/
`dispWort`): no memory access, no fault -- correct, LEA never faults
on its computed address. Compact loads/stores go through the
permission-checked `read64`/`write64`, so faults become `none`.

**CMOV.** Register-only (`dst src : Register`, `cmovSchrittBytes`
reuses accepted `cmovAnwenden`). There is NO memory-operand CMOV in
the model, so the architectural unconditional-read-and-may-fault
hazard class is absent by construction. Correct today; a memory form
must model the unconditional read (future obligation F1, not a bug).

**Multiply/divide.** Register-only (`gift_imul_mod0` pins the mod=0
refusal); memory-operand MUL/IMUL/DIV (which can fault) do not exist
(same F1 class). `stepIE` keeps the `#DE` trap distinct
(`hardwareHalt`, only trapping family per `stepIE_halt_nur_muldiv`)
but `stepI`/`ISAExecution.ausgangVon` collapse trap, page fault and
bad decode into `none`/`verweigert` (CUTS-admitted). Moot for the
pipeline theorems (pilot-only, never emits muldiv) but MUST be scoped
or threaded through at ISA level (§8, MUST-FIX I3).

**Compact equivalence.** `equiv_*` lemmas prove each compact form
equals its pilot long form at step level (moves by computation,
loads/stores via shared `effAddr` arithmetic including the failed-read
case, `jump8` by target equality, `aluImm8` ADD/SUB/XOR/CMP against
two-register pilot rows over a scratch register). AND/OR have no
pilot register form so the ALU rewrite covers ADD/SUB/XOR/CMP only --
a stated coverage boundary, not a bug.

**Selection (peephole).** Input language is pilot+immediate-shift+
SETcc; outputs use core-LEA (`a + (b<<s)` needs shift 1..3),
compact ALU-imm (`passtSx32` checked) and compact data moves. `Gl`
agreement is straight-line only, RIP excluded (`laufI_rip`), flags
all-or-nothing, scratch list `S` is a caller-declared dead-after set
NOT checked against following code (CUTS-honest caller obligation).
Byte-level comparison of the two differently-coded runs exists only
on the witness. No overclaim in the file; the PR body should not cite
"64 to 36 bytes" without the straight-line/scratch qualifiers (M4).

**Relaxation.** `jmp`/`jcc` short/long with whole-layout
revalidation (`layoutOk` re-checked per round, `relax_ok` for any
fuel, no optimality/fixpoint claim); backward jumps covered by the
`loopProg` witness (`loop_waehle/relax/sprung/uebersetze`); rel32
range refused past 2^31 (`passtRel32Wort`); no `LOOP` opcode (there
is no rel8 `LOOP` form in the fragment -- correct to exclude, `call`
stays rel32). Per-block selection keeps all flags live and lets `S`
differ at block entries (`waehleB`); control rows are never `op`
rows. The labelled semantics is parametrised by the layout map and
runs are fuel-bounded -- all stated.

**Pipeline (the actual complete path).** `pipeline_correct_loaded`,
`pipeline_refuses_loaded`, `kompiliert_geladen`,
`pipeline_correct_compiled`, `pipeline_correct_entry` speak over the
REAL `execBlock` of the ORIGINAL block (`hsrc : execBlock ... = .ok`),
with executable decided checks (`validate`, `imageOk`, `weltOk`,
`bauOk`), the pre-existing loader (`bildZustand` over `geladen` in
accepted `Bild.lean`), pre-existing entry admission
(`eintrittZulassung` over accepted `EntryExecution`/`EntryState`),
and deep values/checks/`ite` (`ExpressionLoweringDeep`, register-list
freshness `FrischListe`, no spilling -- refusal, honestly a CUT).
Scope: single-thread `Zustand`, fuel-bounded runs, stop-by-refusal
past the image, no TSO/concurrency/time -- all stated. The fragment
is pilot-only (`List Befehl`); the "later unified ISA replaces
`Befehl`" point is an admitted non-connection (see §6).

**PR 1 optimizer (dependency).** Rules act on the real typed source
(no IR, per decision 594/606); each checker recomputes from source;
refinement is exact-`Ausgang` equality of single-thread `execBlock`.
Honest boundaries: no CSE/LICM/inlining/unrolling/peephole (need
unaccepted lowering rows/effects); decided reads never dropped
(trace/race-freedom legs); strength reduction certifies the WORD op
(`shlW/shrW/maskW` over shared `zahlWort`); no FP rules; NO
concurrency/TSO/time transfer claimed ("the machine-G transfer of
removed checks stays OPEN", also in `OPTIMIZER.md` §13). Poison
probes for signed-division, overflow risk, dropped reads, pass order
(§9 rank table). Sound.

## 5. Adapter, not a duplicate machine (inside the PR)

Inside PR 2, the unified `Instr` WRAPS the existing family types
unchanged and `stepI` DELEGATES to the existing steps (`schritt`,
`mulDivSchritt`, `shiftSchritt`, `stepNarrow`, `setcc/c MovBytes`,
`schrittC`, `coreSchritt`); `encodeI`/`decF` delegate to the existing
codecs. Compact/core reuse `add64/sub64/xor64` (`Wort`),
`and64/or64` (`Ganzzahl`), `andW/orW/logikFlags/negWf` and
`NegGueltig` (`ShiftLogic`), `notB` (`Ganzzahl`), `extendNarrow`
(`NarrowOps`), `read64/write64` (`Speicher`), `regSet/ripNach/
schrittRegister/effAddr`-style helpers (`Ausfuehrung`). The entry,
image and loader are the accepted ones. No evaluator is
re-implemented. This is the requested "one coherent practical
hardware model" construction pattern done right -- WITHIN the PR.

## 6. The real problem: two unified machines after merging to master

The PR predates four accepted master modules that do the same job:

| Master (accepted) | PR 2 (new) | Relation |
|---|---|---|
| `decodeExt`/`stepExt` (`ExtendedExecution`, lane 575): pilot+narrow+muldiv+shift+setcc/cmov+FP-double+packed-int over `FpZustand`, used by `HardwareExecution` (multicore TSO) | `decodeI`/`stepI` (`ISA`): pilot+narrow+muldiv+shift+setcc/cmov+compact+core over `Zustand`, no FP/vector/LOCK | Same producers for the six shared families; disjoint byte claims (PR 2 only accepts bytes `decodeExt` refuses); but TWO canonical entry points and TWO "unified" types |
| `IntHwOp` (`IntegerHardwareForms`, lane 666): AND/OR/TEST/NOT/NEG width-parametric, same `andB/orB/notB/logikFlags/negWf` producers | `CoreBefehl` AND/OR/TEST/NOT/NEG 64-bit-only + LEA/MOVZX/MOVSX | Same value/flag producers (`andW b = (andB b, logikFlags b)` verified); duplicated instruction types and codecs |
| `AddressEncoding` (lane 664): disp0/disp8/disp32 smallest-first, SIB/REX parser, RIP-relative, LEA purity | `IntegerCore.decodeCoreLea` + compact `decodeMemC`: SIB/REX decoding for LEA and disp8/disp0 memory | Different levels (address-FORM parser vs instruction decoders) but both decode SIB bytes with no stated relation |
| `HardwareExecution` (lane 660): multicore TSO over `decodeExt` | `ISAExecution`: single-core over `decodeI` | No conflict today (different scope), but the integer-profile future must pick ONE dispatcher |

Additionally the PR's own three stages do not compose into its
headline path: `Pipeline` emits pilot `List Befehl`;
`ISASelect.waehle` takes `List Instr` (pilot-shaped inputs); `ISARelax`
resolves `LProg` (and runs its own per-block `waehleB` via
`uebersetze`); the image/entry theorems consume `Pipeline` output
only. No theorem feeds pipeline output through select/relax into the
image. The proved complete path is source-optimiser-pilot-image-entry
(which is genuinely complete for its fragment); select/relax/ISA are
proved foundations awaiting connection. The PR body ("The steps work
like this") reads as if they were one path -- scope wording fix (M4).

## 7. Claim-vs-proof table

- Bounded model theorem: YES (`pipeline_correct_compiled/entry`
  over real `execBlock`, fuel-bounded, single thread). Not claimed
  beyond that.
- Rust mirror tested equality: YES, and labelled as test-only
  (`codec_golden` 4059 Lean-generated vectors, 2 tests;
  `pipeline_golden` 8 tests over ~40 named cases incl. refusal twins;
  `lower.rs` one-level fragment superseded by deep lowering, documented
  in `pipeline.rs`). Equality is TESTED, never proved -- stated.
- Executable checker invocation: YES (`validate`/`imageOk`/`weltOk`/
  `bauOk`/`layoutOk` are decided; certificates carry no trusted values).
- Real AST linkage: YES for the pipeline (real `Block`/`Expr`/
  `execBlock`/`World`/`Env`); the Rust input models (`Fragment`,
  `IExpr`, `Block`) are explicitly NOT the typed AST (stated CUTS).
- Final loader/mapping: BYTE-granular loader reused (`Bild.geladen`);
  page-granular OS loading NOT claimed -- `elf.rs` CUTS + `seitentreu`
  say no current image is page-faithful. The PR body says the same.
- Architectural fidelity: family-model fidelity only (shared
  producers, boundary probes); silicon correspondence NOT claimed
  anywhere in the files. Do not cite round trips as hardware proof.
- Concurrency/time: NOT claimed (single `Zustand`, no TSO, no timing;
  optimizer G/GX transfer OPEN). The goal theorem is untouched.

## 8. MUST-FIX before master merge (integration blockers, no weakening)

- **I0. The pinned tree is RED: two exact-name collisions.** Reproduced
  on the exact snapshot (§9): full `./lean-bau` fails the root
  `Grammatik` target, first with
  `import Grammatik.X86.ISASelect failed, environment already contains
  'Gabbro.Grammatik.X86.waehle' from Grammatik.X86.FeatureProfile`,
  then (after renaming that) with
  `import Grammatik.X86.ISARelax failed, environment already contains
  'Gabbro.Grammatik.X86.layoutOk' from Grammatik.X86.TableLayout`.
  (a) `def waehle`: `FeatureProfile.lean:72` (pre-existing in the PR
  base: `waehle (hw : HwProfil) (b : BereitProfil)`) vs
  `ISASelect.lean:703` (new: `waehle (S : List Register) (fe : Bool)`).
  (b) `def layoutOk`: `TableLayout.lean:80` (pre-existing:
  `layoutOk (es : List TabLayout)`) vs `ISARelax.lean:132` (new:
  `layoutOk (ws : List Bool) (p : LProg)`). A namespace-aware scan of
  all fully-qualified `Gabbro.Grammatik.X86.*` definitions over the
  snapshot finds no further cross-file duplicates (the one other hit,
  `MulDivErgebnis`, is `def MulDivErgebnis.nachfolger` -- extending,
  not redefining). Per-module builds stay green because no colliding
  pair ever imports each other, which is how this slipped past the
  PR's own checks -- the PR's "full `lake build` fails only in
  `Parser/ElementTiefProben.lean`" claim is false for the pinned tree.
  Minimum repair (validated in the disposable fixture, §9): rename the
  NEW names -- `ISASelect.waehle` (and its call sites) and
  `ISARelax.layoutOk` (and its uses in `ISARelaxWitnesses.lean`);
  keep pre-existing `FeatureProfile.waehle` / `TableLayout.layoutOk`
  stable. The fixture rebuild with exactly these two renames is
  GREEN (root target built, 476 jobs, 0 errors), so the repair is
  both necessary and sufficient. Correction note: an early draft of this review also listed
  `CodeAt` (`ISAExecution.lean:186` vs `Pipeline.lean:83`); that was a
  namespace-blind false positive -- the latter is
  `Gabbro.Grammatik.X86.Pipeline.CodeAt`, a distinct name, and Lean
  never complained about it. This is the classic AGENTS.md merge-break
  class (two lanes, one name); the merge gate must build the ROOT
  target, never per-module only.
  Side observation from the repair loop: with the collision present,
  Lean's `autoImplicit` turns the unknown `CodeAt` into an implicit
  variable and the resulting `#print axioms` line for `waehle_bytes`
  reports `sorryAx` -- an axiom census is evidence only on a GREEN
  build.

- **I1. Rebase onto current master.** Base `26c58bd4` is 170 commits
  behind `011ff474`. The snapshot lacks `ExtendedExecution`,
  `HardwareExecution`, `IntegerHardwareForms`, `AddressEncoding` and
  the 60+ other X86 modules merged since. Re-run the full build and
  the axiom census after rebasing; expect `Grammatik.lean` import-tail
  conflicts (both sides append) -- union, keep order.
- **I2. One canonical integer dispatcher.** Either extend accepted
  `decodeExt`/`ExtInstr` with the compact+core rows (preferred: keeps
  the FP/vector/TSO path and `HardwareExecution`) and re-point
  `ISAExecution`/`ISASelect`/`ISARelax` at it, or retire `decodeExt`
  with explicit reviewer sign-off and migrate `HardwareExecution`.
  Landing `decodeI` beside `decodeExt` as a second "ONE unified"
  decoder is the exact incompatible-architecture outcome the
  hardware-model priority forbids. Same for `Instr` vs `ExtInstr`.
- **I3. Stop-kind discipline at ISA level.** Thread `MulDivErgebnis`
  (`hardwareHalt` vs `misslungen`) through `ISAExecution` instead of
  `ausgangVon none = verweigert`, or downgrade the ISA-execution
  theorems to refusal-only and say so in their statements (the
  pipeline theorems are unaffected -- pilot-only). A `#DE` trap is
  observably not a `#PF`/`#UD`.
- **I4. Connect or scope the path.** Either prove pipeline-output
  through select/relax into the image (lift + layout + revalidation),
  or state in `Pipeline.lean`'s header and the PR body that the proved
  complete path is the pilot-direct one and select/relax are
  connected foundations. Do not ship the "64 to 36 bytes" example as
  part of the proved path without its straight-line/scratch qualifiers.
- **I5. PR-1 reservation sign-off.** `OptimizationRules.lean`/
  `OptimizationWitnesses.lean` are friend-reserved (AGENTS.md §3).
  The PR-1 commit message claims it re-applies the first friend
  delivery -- that claim needs the handoff owner's explicit
  acceptance, recorded in `OPTIMIZER.md`, before merge. Technical
  review alone cannot clear it.
- **I6. Core-vs-IntHw subsumption.** Prove (or state with direction)
  the relation between `CoreBefehl` b64 rows and `IntHwOp .b64` rows
  over the shared producers, and between `IntegerCore` LEA/SIB
  decoding and `AddressEncoding`; do not land two SIB stories without
  a stated relation.

## 9. Reproduction

Disposable fixture `.tmp/fixture-pr2` (ignored scratch): exact PR-2
snapshot trees + copied queued wrappers + warm clone-local
`grammatik/.lake` (toolchain `v4.33.1` matches snapshot). Two runs:

1. **Exact snapshot: RED.** Full `./lean-bau` (PID 800662) ends
   `== exit 1; 3 error line(s) in the COMPLETE output` with the root
   failure `Grammatik.lean: import Grammatik.X86.ISASelect failed,
   environment already contains 'Gabbro.Grammatik.X86.waehle' from
   Grammatik.X86.FeatureProfile` (full log
   `.tmp/fixture-pr2/leanbau.log`). The `.lake` copy cannot cause a
   source-name collision; both definitions were additionally confirmed
   in the pinned git objects (`git show 987b286d:...`). The PR's
   "full build fails only in `Parser/ElementTiefProben.lean`" is
   therefore false for the pinned tree.
2. **Fixture-only minimum repair: PENDING.** `waehle`->`waehleI`
   (`ISASelect.lean`, `ISASelectWitnesses.lean`) and `layoutOk`->
   `layoutOkI` (`ISARelax.lean`, `ISARelaxWitnesses.lean`) applied with
   `sed` in the fixture ONLY (the clone and the verdict on the pinned
   commit are untouched; an intermediate `CodeAt` rename was reverted
   after the namespace-aware scan proved it a false positive); full
   `./lean-bau` re-run (PID 851671, log
   `.tmp/fixture-pr2/leanbau4.log`). RESULT: **GREEN** --
   `== exit 0; 0 error line(s) in the COMPLETE output`,
   `✔ [475/476] Built Grammatik`, `Build completed successfully
   (476 jobs)`, zero `sorryAx` anywhere. This proves the two renames
   are sufficient: no further collision or error hides behind them,
   and every `#print axioms` line and `decide` witness kernel-checks
   on the repaired tree. The repaired tree is fixture-only evidence;
   the pinned commit itself stays RED as reported in run 1.

Mechanical audits over exact files (no build needed): zero matches
for `sorry`/`admit`/`native_decide`/`^axiom`/`unsafe` in all 27 new
Lean files; 470 `#print axioms` lines present in the 10 core files;
`familien_disjunkt`/`decodeI_eindeutig`/`decF_*`/`decodeC_sig`/
`decodeCore_sig`/`decodeC_verbraucht`/`decodeCore_verbraucht`
verified present with the stated arbitrary-input generality;
witness families (`isaProg` pilot/muldiv/shift/cond/narrow run,
`isaProg2` compact/core run, `isaJeFamilie` per-family round trips,
`loopProg` relax loop, golden-case twins) verified present.
No fixture cargo run: even this clone has no warm
`programmlogik/.lake`, and the full suite runs `gabbro prove`
(needs `lake`, i.e. network for a cold cache), which is forbidden
here; the merger's `./cargo-pruef` gate covers it. Rust findings are
static and labelled as such.

## 10. Minor fixes and future obligations (not blockers)

- M1 (fix): `opt.rs`/`pipeline.rs` constructor-mapping tables and
  golden provenance headers are excellent; keep the scratch harness
  note (`GoldenSweep.lean` uncommitted) -- consider committing the
  generator so the 4059 vectors are reproducible in-tree.
- M2 (fix): `encodeC_len` comment ("2..7 bytes") vs proved `1..15` --
  tighten the comment or the bound.
- M3 (probe): add one `decide` probe for SETcc byte-register mapping
  under REX (`rm=4..7` = SPL/BPL/SIL/DIL).
- M4 (wording): PR body "Programs placed in memory run exactly like
  their instruction list" needs the straight-line qualifier
  (`laufBytesI_layout` needs `faelltDurchI`; control flow goes
  through `laufBytesI_spur` with an underived `SpurAn` premise); same
  for the "64 to 36 bytes" example (straight-line + scratch-list
  qualifiers).
- M5 (hygiene): `lower.rs` `senk_frag`/`senk_atom` have their own unit
  tests but are superseded by `pipeline.rs` deep lowering (only
  `int_wort` is reused, and `pipeline.rs` says so) -- mark the module
  header as legacy/test-only so the unused producer cannot silently
  drift from the deep lowering.
- F1 (future): memory-operand CMOV (unconditional read + fault even
  when untaken), memory-operand MUL/IMUL/DIV, `LOOP`/`JCXZ`, LOCK
  rows, FP/vector/LOCK membership in the unified decoder, TSO
  membership of the unified step, cross-block liveness for select,
  optimality/fixpoint for relax, page-faithful images
  (`seitentreu`-passing layout), committing the golden generator.
  None is claimed; none blocks.

## 11. Bottom line

PR 2's modules are the best-constructed large contribution this
reviewer has read in the X86 tree: delegation-only semantics,
arbitrary-input disjointness with boundary probes for every shared
prefix, joint witnesses with real fetched-byte runs, refusal probes
for every new refusal class, and CUTS blocks that name every open leg
including the ones a casual reader would miss (stop-kind collapse,
straight-line layout scope, scratch-list caller obligation,
unconnected pipeline). PR 1 is of the same quality at smaller scope.
But the pinned commit is RED at the root target and predates the
accepted dispatcher/hardware-row/address work -- repair I0, then
rebase and unify per I1--I6, with fresh `./lean-bau`, `./cargo-pruef`,
emission and key gates on the rebased tree. Do not reinterpret this
review as silicon validation: it validates stated-conformance of a
fragment model, and that is what the files claim.
