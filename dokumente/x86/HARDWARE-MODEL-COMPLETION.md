# Hardware-model completion matrix — selected x86-64 architectural model

*Owner: lane 678 (organisation/audit only). Owned file per `lanes/678.md`.
Status: PROPOSED organisation, not an implementation or a proof.
Nothing here claims any source-to-final-bytes chain is closed.
Central progress record: `DIRECT-COMPILER.md`.
This matrix is the hardware basis for `COMPILER-SCHLUSSPLAN.md` §§1/4;
in-flight lists below are snapshots at write time, not registry state.*
Design scope: `DIRECT-COMPILER-DESIGN.md`. Emitter scope:
`dokumente/x86/EMITTER-INVENTAR.md`.*

## 0. Claim boundary and method

This document is productive closure management, not a proof claim:

- Every classification below is grounded in files read in this clone
  (exact paths named per row). No percentage, no ETA, and no proof
  closure is inferred from declarations, codec round trips, or `Bool`
  enable bits alone.
- In-flight producer lanes 660/662/664/666/668/670/672/674/676 are
  known only through their committed task prompts (`lanes/660.md`
  … `lanes/676.md`). Their candidate modules and reports are NOT in
  this clone, and no live control directory or other clone was
  accessed. Nothing below calls an in-flight candidate merged, accepted,
  or hardware-correspondent.
- "Complete/proved" is used only where a closed generic theorem with
  independent review exists in the tree. Every other row is `partial`,
  `unimplemented`, or carries a named `proved obstruction` with file
  evidence. An obstruction is a proved fact that blocks a stronger
  claim — it is not a defect assertion about silicon.
- Manual provenance for NEW ISA details: producers read the local
  snapshot `.tmp/HARDWARE-REFERENCES/REFERENCES.json` (Intel SDM
  combined volumes 1–4, edition 325462-093US, September 2026) plus the
  extracted `intel-instruction-reference.pdf/.txt`. No AMD snapshot is
  available (AMD URLs returned 404, per the JSON scope note). Each
  producer records the exact manual heading/page it checked in its own
  report; this matrix does not re-assert any manual fact.
- Trust rule throughout (goal `Spec.lean` header, design §§1/5,
  `EMITTER-INVENTAR.md` §12 item 7): only named silicon/device/timing
  behaviour is a hardware assumption; OS, kernel, scheduler, runtime,
  loader and binding bodies are user logic with checked contracts.

## 1. Accepted ground truth in this clone

- **Pilot vocabulary** (`grammatik/Grammatik/X86/Typen.lean`, 87 lines):
  16 GP registers in architectural encoding order, `Breite`
  (b8/b16/b32/b64), `Flags` with `af : Option Bool` (undefined, not
  false), byte-addressed `Speicher` with per-address R/W/X bits, and
  exactly 14 `Befehl` constructors, all 64-bit only. No other width,
  form, decoder, TSO rule, ABI fact or cost fact is in the pilot.
- **Abstract execution** (`Ausfuehrung.lean`): one proved step equation
  per pilot form over shared `Wort`/`Speicher` helpers; `Decodiert.laenge`
  is checked input data (1..15), not decoded bytes. Bounded abstract
  helpers, not chain correspondence.
- **Canonical codec** (`Codec.lean`): canonical bytes plus generic
  round trip `roundtrip` / `roundtrip_len_ok` for all 14 forms, with
  explicit refusals of truncated, non-canonical and corrupted inputs.
  Self-consistency only, not hardware correspondence.
- **Fetched execution** (`Byteschritt.lean`): executable-prefix fetch of
  actual memory bytes capped at 15, fetch-to-decoder correspondence,
  byte-step-to-`schritt` correspondence (`byteschritt_weiter`, both
  `verweigert` directions).
- **Unified dispatcher** (`ExtendedExecution.lean`, 828 lines): `ExtInstr`
  (`:38`) = pilot plus one family per accepted helper (narrow,
  muldiv, shift, SETcc/CMOVcc, scalar SSE2 double, packed integer);
  `decodeExt` (`:64`, sequential fallback, pilot never shadowed, pinned
  per family with pilot-refusal evidence), `stepExt` (`:305`, old
  evaluators lifted, never redefined), `extZugelassen`, `fetchExt`
  (`:576`), `extByteschritt` (`:616`), joint mixed pilot/FP reached
  memory-changing run with planted refusals. CUTS: no hardware
  correspondence (canonical subsets with self-consistency only), no
  LOCK prefix, no SIMD beyond PXOR/PADDQ and four scalar double byte
  rows, no source/IR correspondence, no TSO/W/GX bridge, no
  ABI/loader/entry/budget connection; high XMM and REX-extended
  FP/vector forms refused by absence; the divide `halt` is a carried
  named hardware outcome, not proved silicon behaviour.
- **Scope inventory** (`EMITTER-INVENTAR.md`, measured at `09eed365`):
  every reachable emission path read off `emit.rs` (19250 lines,
  259 `weigere(` sites), `ast.rs`, `treiber.rs` (`treiber-gen-10`),
  `bau.rs`. Unbounded/foreign paths named (`asm`, `extern`, loader,
  `LibraryCall` N057, manifest rules). §12 records open
  exhaustiveness gaps (no machine-checked AST-to-emitter arm
  enumeration; C-census tools measure the C backend, not x86 bytes;
  hand-maintained width/trap/port/order/intrinsic tables need
  totality or refusal-completeness checks).

## 2. Completion matrix

Columns per row: selected forms/widths; canonical state; fetched-byte
path; register/flag/FP effects; address/access/fault rules;
TSO/atomicity/interrupt/control gates; generic witness + independent
review evidence; classification.

### A. Pilot integer/control/memory (14 forms)

Forms: `movImm64`, `movReg64`, `addReg64`, `subReg64`, `xorReg64`,
`cmpReg64`, `load64`/`store64` (base + sign-extended disp32, mod=10
always), `jump32`, `jumpIf32` (16 `Bedingung` codes), `call32`,
`push64`/`pop64`, `ret`. Canonical encodings in
`DIRECT-COMPILER-DESIGN.md` §2 table. State: `Zustand` + `Flags`
(`af : Option Bool`). Fetch: `Byteschritt.fetchDekodiert` discipline.
Effects: per-form step equations (`Ausfuehrung.lean`); XOR leaves
`af = none` (undefined, never false; toolchain struct-update note
`Ausfuehrung.lean:845-846`). Access: permission-checked, `OhneUmbruch`
(`Speicher.lean:160`), region extents. Witnesses: store-changing
reached runs, branch/call/return probes, realised-footprint coverage
(`AccessExecution.lean`: six `gefunden` + six `fuss` lemmas, generic
`realisiert_fuss_abdeckung` over all 14 forms). Classification:
**partial (proved)** — vocabulary, abstract steps, codec round trip and
fetched execution are proved; per-form execution correspondence
against silicon, the per-access TSO bridge, and the full
source-to-final-bytes chain remain OPEN (design §2 says this
explicitly; do not cite the pilot as hardware fidelity).

### B. Address encodings (producer 664; prompt `lanes/664.md`)

Selected: base+index*scale+disp with REX high registers, absent
base/index cases, disp0/disp8/disp32 choice, RIP-relative for image
data, short rel8 branches, LEA as pure address arithmetic.
Evidence in tree: pilot has disp32-only memory and rel32-only
branches; `EffectiveAddress.lean` proves disp sign-extension pins,
modular-wrap separation, `OhneUmbruch` admission and region-extent
admission (`:147-174`); `BranchLayout.lean` proves exact rel32
lengths and the layout certificate with revalidation. Per-access
canonical-form check: NOT found — `Speicher`/`EffectiveAddress`/
`Ausfuehrung` gate on `OhneUmbruch` + extents + permissions; the only
canonical-address rule is image-level `kanonischBereich`
(`Bild.lean:43`, profiles 48/57 only, `kanonisch_tief_48` /
`kanonisch_hoch_48` / `kanonisch_loch_48` / `kanonisch_57_weiter_als_48`
at `:99-115`). Required API: one generic selected address-form
parser/encoder with consumed lengths, sign-extension/effective-address
equality, compact-encoding choice, refusal of unsupported/noncanonical
forms, plus a fetched load/store-or-LEA connection to real
memory/evaluator effects. Classification: **unimplemented** (pilot
rows stay; no second decoder for accepted pilot forms; old pilot
unchanged per prompt).

### C. Practical integer widths and compact encodings (producer 666; prompt `lanes/666.md`)

Selected: MOV/MOVZX/MOVSX/MOVSXD (8/16/32→16/32/64),
LEA (pure, no flags, no memory event, disp-fits-signed-32),
ADD/SUB/AND/OR/XOR/NOT/NEG + CMP/TEST at 8/16/32/64 with immediates
(imm8/imm32, sign extension), SHL/SHR/SAR (+ROL/ROR if cheap) with
masked counts, IMUL (incl. 3-operand imm) / MUL / IDIV/DIV (#DE on
zero/overflow = `hardware` stop, never speculated), SETcc, CMOVcc
(register-only first; memory-source refused until the unselected-side
fault proof lands), indirect CALL/JMP (validator-tracked target set,
every target a decoded start or listed entry; M140, N575–N577).
Evidence in tree: `NarrowCodec` (959 lines, 75 decls), `MulDiv` +
`MulDivCodec`, `ShiftLogic` + `ShiftCodec`, `ControlFlow` +
`ControlCodec` (register-only SETcc/CMOVcc byte shapes, faulting
CMOVcc-memory with the no-speculation fact), all wired into the
`ExtendedExecution` dispatcher with pilot-refusal pins. Omission
inspected — **defined AF**: `Typen.lean` models `af : Option Bool`
(undefined, not false); the 666 prompt states AF=none is an
abstraction, NOT proof of a defined hardware AF result, and requires
either a proved observation-abstraction or the defined flag in each
new admitted row. 32-bit zero-upper vs 8/16-bit partial-register
behaviour, signed immediate extension, and masked shift counts are the
producer's proof load. Classification: **partial (proved helpers,
byte-connected through the dispatcher; hardware correspondence and
defined-flag rows OPEN)**.

### D. LOCK atomics and fences (producer 662; prompt `lanes/662.md`)

Selected: LOCK XADD and LOCK CMPXCHG word forms plus MFENCE, with
canonical byte parsing/encoding and real fetched execution; effective
address, implicit accumulator, old-value destination, flags,
success/failure distinctness, actual R/W permission requirements and
buffer ordering. Evidence in tree: `LockedOps.lean` (521 lines) adds
`SperrBefehl` (XADD-shape RMW, MFENCE) and `casSchritt` — success
installs, **failure is a stutter returning the unchanged state**
(`cas_fehlschlag_stottert`: memory bytes, buffers and flag record
unchanged; safety-only, no progress/cost). Omission inspected —
**failed-CAS writes**: the 662 prompt explicitly does NOT accept the
simplified false-path stutter as the complete ISA and requires write
permissions/access on a failed comparison to be resolved per the
manual (evidence: `cas_fehlschlag_stottert` in `LockedOps.lean`;
`WordAtomicity.lean` CUTS: `WortGuard` groups accepted LOCK
preconditions only). `FenceDrain.lean` iterates the one canonical
flush; `TSO.lean` CUTS disclaim aligned multi-byte single-copy
atomicity (`paket_reisst`). Classification: **partial with a proved
obstruction** — the stutter theorem is proved and correctly blocks any
claim that `LockedOps` alone is full LOCK correspondence; full
forms, flag/register/RIP effects, failed-path access rules and the
drain/barrier witnesses belong to 662 with exact missing-width/
address/control CUTS.

### E. Scalar FP operations and conversions (producer 668; prompt `lanes/668.md`)

Selected (SSE2 binary64 baseline, design §4): ADDSD/SUBSD/MULSD/DIVSD,
MOVSD (incl. RIP-relative loads), CVTSI2SD (width-selected),
UCOMISD + SETcc/Jcc with JP row, `gleitNarrow` (two-UCOMISD AND shape;
finite = exponent-field test), `gleitRoh` = CVTTSD2SI + saturation
wrapper (bare CVTT alone is NOT `gleitRoh`). Control state:
RNE (RC=00), no-x87/no excess precision, no contraction (encoded FMA
refused), no fast-math, FTZ=0/DAZ=0, all exception masks set, sticky
flags RESERVED. Evidence in tree: `ScalarFloat.lean` (1508 lines)
reuses the accepted IEEE kernel; `ScalarFloatCodec.lean` (710 lines);
`FloatEntryState`, `FloatExceptions`, `FloatSourceObservations`;
four scalar double byte rows in the dispatcher. Omissions inspected
with evidence: **NaN payloads** — class-level only, payload equality
never concluded (`ScalarFloat.lean:1013,1022,1259-1462`; `CUTS:1459`);
**sticky MXCSR flags (bits 0–5)** — unchecked and unmodelled
(`ScalarFloat.lean:1467`); `FloatExceptions.lean` proves
`guard_sticky_offen` (`:51-54`: sticky set does not close the slot)
with accumulation/observation OPEN (`:182-186`). **f32**: source-width
model extension or proved fragment refinement required; every `float`
node refused until then (design §4; 286 f32 evidence merged).
Classification: **partial (proved)** — kernel reuse, decoder rows and
dispatched fetched execution proved; raw-bit hardware fidelity,
payload/control observations, MXCSR establishes/preserves per context
and the f32 bridge remain OPEN. Codec plus class-level agreement is
NOT silicon fidelity (668 prompt).

### F. Faults and exceptions (producer 670; prompt `lanes/670.md`)

Selected: illegal encoding, overlong/truncated fetch, noncanonical
addresses, instruction/data permissions, divide zero/overflow,
enabled-state/alignment faults — as precise admitted-profile
architectural faults and stopped observations on actual
decoded/fetched executions, with pre-fault register/memory/RIP
effects exactly where the manual guarantees them and explicit
nondeterminism elsewhere. Evidence in tree: `DecodeFault.lean`
(276 lines) fault-preservation catalogue over reused evaluators
(unsigned/signed div-by-zero and quotient overflow, CMOV-memory
no-speculation); `OverlapRefusal.lean` decided admission
(`zugriffOk`/`aliasZulassen`); decode-side length soundness
(`DecodingCoverage`, `DecoderSoundness`) from the decoder side only,
never from encoder round trips. Required distinction: compiler
admission refusal (`Option.none`) is NOT a hardware fault claim
(#UD/#GP/#PF); fault delivery stack/handler rules stay with 672.
Classification: **partial (proved catalogue over admitted rows;
fault-priority/privilege details and per-access canonical-form faults
OPEN)**.

### G. Interrupts, entries, masking, trap forms (producer 672; prompt `lanes/672.md`)

Selected: long-mode interrupt/exception entry, masking and interrupt
shadow, SYSCALL and return/entry rules for the freestanding/binding
forms actually driven by the emitter (`GateStub`, `EntryState`,
`EntryExecution`, `StackUnwind`, `StackExecution`, source interrupt
rules/handlers from Syntax/Semantik/goal scheduling). Evidence in
tree: `EntryState.lean` (553 lines; single-probe guard page, one-word
stack discipline + 16-alignment, MXCSR/guard findings as `Bool`);
`EntryExecution.lean` (375 lines) joint admission over actual
`Bild.wohlgeformt`/`geladen`, `eintrittOk`, `torOkB`, fetched steps,
duty/call-site bindings; `GateStub.lean` caller half
(IMAGE-ABI §7 caller half). Rules: named hardware interrupt selection
separate from checked user handler/kernel/OS contracts; nested
delivery and mid-sequence interruption retain memory/TSO/FP
obligations or are refused by a checked profile gate; no Linux/POSIX;
OS configuration and context preservation are user logic, never
assumed. Classification: **partial (admission proved; architectural
async transition rules for the selected forms unimplemented)**.

### H. SIMD and enabled-state gates (producer 674; prompt `lanes/674.md`)

Selected tiers (design §6): Tier 1 scalar SSE2-adjacent (no vector
instructions); Tier 2 SSE2 packed-integer XMM (PADDB/W/D/Q, PADDQ,
PXOR, PAND/POR, PSLLQ/PSRLQ, MOVDQA/MOVDQU, 128-bit loads/stores,
element widths 8–64, lane count × width = 128); Tier 3 optional AVX2
VEX/YMM per NAMED CPU profile (CPUID AND OSXSAVE+XCR0 XMM+YMM proved
as entry-established facts, re-checked per image). Evidence in tree:
`VectorCodec.lean` — **two register forms only** (PXOR `66 0F EF /r`,
PADDQ; CUTS); `Vektor.lean` data/operation foundation, explicitly NOT
validated vectorisation; `VectorFootprints.lean` — 16-byte footprints
only, concatenated halves; `ExtendedExecution` wires PXOR/PADDQ.
Omission inspected — **XCR0/OSXSAVE context**: `FeatureProfile.lean`
carries control-state readiness as an MXCSR word plus ONE `osXmm :
Bool` (`:42-63`; baseline `hat`-lemmas at `:112-138`); a repository
search for XCR0/xcr0/OSXSAVE/CPUID/cpuid/AVX finds only those `osXmm`
uses — no CPUID/XCR0/XGETBV model exists. The 674 prompt states a
bare `osXmm` Bool is not completion evidence. Further gates:
lane-separation lemma, 128-bit access NOT single-copy atomic (shared
vector stores refused until the TSO bridge rules), aligned/unaligned
faults, full per-access footprint/tearing, fault order, per-lane FP
status; Tier 3 needs upper-YMM state in the relation and
call-preserved ABI discipline. Classification: **partial with a
proved obstruction** — Tier 1 selected scalar plus two proved
packed-integer register rows; enabled-state completion is blocked
until CPUID/XCR0/context proofs land (674); AVX2/VEX/raw-bit/fault/
context rows explicitly unimplemented, never marked done.

### I. Ports and device memory (producer 676; prompt `lanes/676.md`)

Selected: exact port IN/OUT byte encode/decode/fetched execution over
canonical registers (implicit accumulator width/partial-register or
zero-upper effects, immediate-port vs DX-port forms, privilege/IOPL/
TSS permission outcomes, ordered IO events) plus a generic
hardware device-response interface and a typed finite
admission/profile memory-kind interface. Evidence in tree:
`EMITTER-INVENTAR.md` §10 — `at port` (in/out widths 8/16/32,
`arch x86_64` required), `at mmio` (lowered address access),
`at dma` refused (barrier is a model statement). Omission inspected —
**device-memory ordering**: `TSO.lean` CUTS models no interrupt,
device, MMIO or DMA behaviour (handler-entry drains cut of lane 567
in the TSO wave); `BridgeRead.lean:450` cuts device/MMIO/DMA;
MMIO must NOT inherit write-back RAM TSO ordering. No
number-to-source-pointer conversion (M140); no Linux/POSIX or
fabricated C wrapper. Classification: **unimplemented** (emitter rows
exist in C; no architectural port/device execution in Lean; MMIO/DMA
stay refused until their memory-type/order rules are modelled).

### J. TSO → W → GX per-access bridge (producers 567/573/574; design §5, `TSO-GX-BRUECKE.md`)

Strategy: per-access forward simulation x86-TSO → W, then the existing
`schwach_ist_gX` into `SchwachX`. No blanket "x86 is W/DRF-SC"; no
G-step-as-transaction. Evidence in tree: `TSO.lean` (real canonical
byte memory, per-core FIFO buffers, forwarding, issue, flush; per-byte
facts do NOT establish aligned whole-word atomicity); `TSOHistory` /
`TSOTrace` (address/byte intermediate layer, no typed-carrier W/GX);
`WordAccessGrouping` (whole-word grouping over actual per-byte TSO);
`BridgeRead` / `BridgeWrite` (admitted-profile fragments: one
`.int lo hi` slot as one LE 8-byte word under `WortGuard`; sums,
floats, bools, globals, statics, arenas, atomics, gates and fn
pointers unrepresented; torn/foreign footprints refused);
`SourceMemory` (bounded integer fragment); `SourceAccessCompleteness`
(one `assignSlot` step fragment). Documented limits: aligned 32/64-bit
MOV single-copy atomic needs the O-align proof (natural alignment,
single-carrier containment, non-overlap, little-endian agreement)
else refusal; `seq_cst` lowers to LOCK/MFENCE-bracketed MOV and stays
modelled as release/acquire in W (sound over-approximation, no total
order claimed); CAS loops need a static attempt bound or recorded
DIVERGENCE (no invented termination/constant cost); a fence is never
removed on race-freedom alone. Classification: **partial (machine and
fragments proved; complete per-access typed-carrier simulation OPEN —
that simulation is 6B item 1, consuming the 6A item 4 facts)**.
The existing source `schwach_ist_gX` result is preserved; the missing
target leg is not assumed.

### K. Image, ABI, entries, runtime, budget (producers 558–561/569/570–572/575)

Evidence in tree: `Bild.lean` (`kanonischBereich` 48/57; CUTS: no
decoder/encoding/boundary proof, no relocation correspondence);
`BranchLayout.lean` (rel32 lengths, layout certificate, patched
re-decode, `layoutOk` revalidation); `RelocatedExecution` (site
vocabulary over the canonical encoder); `LoadedExecution`
(loaded-image execution); `StackExecution` (fetched-window decoding
of canonical stack bytes); `BudgetExecution` (`Deckung` carried
data; lowering correspondence with the IR producer OPEN);
`SourceValidatorConnection`, `ValidationBudget`, `ValidatorSkeleton`
(`valX86` checks image mapping and decode coverage, NOT complete
source refinement — `valX86_sound` and the source-to-final-loaded-byte
closing theorem OPEN); `ContractSites`, `RegionFresh`,
`PayloadResidue`, `DecodeFault`-adjacent entry predicates.
Classification: **partial (proved components; loaded-mapping +
relocation-followed-by-re-decoding + source-memory + duties +
runtime/entry + budget-stop ordering connections OPEN — those
connections are 6B item 2, not part of the 6A hardware milestone)**. All reachable final code (emitted unit, generated driver,
compiled-in binding, runtime, handwritten entry paths per
`IMAGE-ABI.md` §10) must be covered or refused; `GENERATOR_KENNUNG`
pins `treiber-gen-10`.

## 3. Coherence and composition duties across in-flight producers

- **Umbrella (660)** owns the single coherent composition: canonical
  per-core integer/FP state, shared canonical memory, per-core TSO
  buffers, checked core/control profile. Duties: data state separated
  from well-formedness; all core-memory projections agree; step
  preservation proved, not assumed; SC word effects never substituted
  for concurrent buffered accesses; byte-vs-carrier atomicity guarded
  (unsupported cases refused); embeddings preserve existing canonical
  pilot/extended execution where exact admissible conditions hold,
  including stopped outcomes; stable adapters for 662/666/668/670/672
  without importing or guessing unmerged source; sequential
  integration order documented. Its skeleton alone claims no
  completion.
- **Shared vocabulary, no duplication**: canonical
  `Zustand`/`FpZustand`/`Speicher`/`TSO` and the accepted
  `ExtendedExecution` byte-facing dispatcher are reused by every
  producer. No competing IR: accepted decision 594/606 uses the
  existing typed Syntax/`exec` source as reference with direct
  lowering to checked machine blocks/bytes (lane 287 IR draft is
  preserved design input, NOT an accepted interface; reviewer 303
  waits for a clean committed candidate). No overlapping writers of
  canonical vocabulary; central fixes need an explicitly assigned
  follow-up.
- **Producer boundaries**: 664 exports the common address API for
  662/666/668 and leaves the old pilot untouched (no second decoder
  for accepted pilot forms); 662 exports the LOCK/fence API for 660
  and typed W/GX consumers; 666 exports admitted-row adapters for 660,
  664 and branch/validator consumers; 668 exports the scalar-FP API
  for 660 and FP-validator consumer 658; 670 exports the generic
  classification adapter for 660 (delivery with 672); 672 exports the
  async/entry adapter for 660 and 670; 674 exports the vector/enabled-
  state adapter for 660 and validator consumers; 676 exports the
  port/device adapter for 660 and profile/validator, avoiding
  syscall/interrupt scope owned by 672.
- **Anti-patterns that reject a candidate** (from all nine prompts):
  manufacturing a desired simulation premise; duplicating an
  interpreter; counting a conjunction of checks as execution; claiming
  the full bridge from a byte-level projection alone; codec round trip
  presented as hardware fidelity or a complete family; silent trust
  assumptions where a producer abstracts an observable effect; new
  model competing with the canonical vocabulary; touching
  friend-reserved optimiser files
  (`X86/OptimizationRules.lean`, `X86/OptimizationWitnesses.lean`)
  or source/checker/Spec/goal/emitter files.

## 4. Named assumptions versus user contracts (preserved)

- `assume`/`axiom` items carry named HARDWARE behaviour only
  (silicon/device/timing — never OS/kernel behaviour); gate/binding
  contracts (`requires`/`ensures`/`effects`/`costs`, total `errors`
  decode) are user logic with checked proofs at actual parameters and
  results (`EMITTER-INVENTAR.md` §§2/9/10, design §1).
- Two recorded pre-existing gaps stay gaps, not architecture
  (`EMITTER-INVENTAR.md` §12 item 7): (a) `assume os_bindung_null`
  (`bibliothek/linux/linux.gab:54`) carries the binding's
  reserve/commit/page-return zero-read promise as a named assume —
  intended: covered by the binding library's checked gate contracts;
  (b) the Linux `-4095` errno decode fence is hardcoded in the emitter
  (`syscall_stumpf`) — intended: derived from each gate's declared
  `errors` map, naming only silicon trap semantics.
- FP/time: named conservative hardware assumptions plus the separate
  cost transfer (design §9, `FLOAT-ZEIT.md` §8); microarchitectural
  tuning is measured (§10), never guaranteed maximal; CAS attempt
  bounds are static-from-contention or recorded DIVERGENCE.

## 5. Essential SIMD versus deferred last-mile (design §2D)

Non-demotion rule (root review repair): the AGREED ESSENTIAL families
of design §2D — scalar arithmetic/bit/shift/multiply/divide/check
lowering (§3); efficient immediates/address modes/short branches
(§2B); the IEEE binary64 scalar baseline (§4); language-needed
concurrency/atomics/fences (§5); emitter-driven calls/ABI/runtime/
entry/hardware forms; the SIMD baseline Tiers 1–3 (§6) — together
with ALL of their observable/fault/TSO/async/control obligations
(register/flag/FP effects, address/access/fault rules, atomicity and
tearing, interrupt/masking interaction, FP control state,
enabled-state gates) can NEVER become complete through refusal,
through a move to CUTS, or through unilateral deferral. Only families
ALREADY agreed as deferred by the design (listed below), or later
explicitly changed by Simon, may remain deferred. An unsupported
encoding OUTSIDE selected scope may refuse at decode; but missing
ESSENTIAL supported-source behaviour — a selected form, width,
observable effect, fault, TSO/atomicity fact, async/control
interaction, or required profile gate — keeps the milestone OPEN.
A DONE condition that lets arbitrary missing rows or effects escape
into §5 with a dated refusal is a scope shrink and is rejected.

Essential (implemented first and completely): scalar
arithmetic/bit/shift/multiply/divide/check lowering (§3); efficient
immediates/address modes/short branches (§2B); IEEE binary64 scalar
baseline (§4); language-needed concurrency/atomics/fences (§5);
emitter-driven calls/ABI/runtime/entry/hardware forms; SIMD baseline
SSE2 selected integer/scalar-FP + AVX2 integer as optional CPU tier
(§6 Tiers 1–3, each gated; scalar remains if a tier gate does not
close). Deferred (optional, later; absence affects only code quality,
never construct support — every accepted construct keeps a certified
translation): selected BMI/POPCNT/bit-scan/shuffle-permutation;
AVX-512, matrix/AMX, APX, crypto accelerators; aggressive FP fusion
(FMA-as-fusion), exotic gather/scatter/compress, cache hints,
non-temporal stores, string specialisations. Stop rule: stop adding
broad profile complexity or compile/validation latency when no
demonstrated worthwhile benefit remains; tuning uses already-proved
translations and measured trait tables, never trusted correctness
premises.

## 6. Finite auditable DONE conditions (root review repair: two milestones, not one)

The previous revision mixed the hardware model with the future
compiler chain in a single DONE list, and its items 1/3 let missing
essential rows escape into §5 by refusal. This revision separates
them. Neither milestone is a percentage or ETA.

### 6A. HARDWARE-MODEL DONE (the immediate goal)

The agreed selected x86-64 architectural hardware model is DONE when
ALL of the following hold on checked master (each item names its
file/theorem/probe):

1. **Selected-form enumeration closed — no escape by refusal**:
   every row of design §§2B/3/4/5/6 Tiers 1–3 has its Lean execution
   semantics + encoder row + decoder refusal of neighbours +
   correspondence lemma. Per the §5 non-demotion rule, an AGREED
   ESSENTIAL row or observable/fault/TSO/async/control obligation
   cannot be closed by moving it to §5-deferred, to CUTS, or to a
   refusing gate — only families ALREADY agreed as deferred by the
   design (or later explicitly changed by Simon) may stay deferred.
   An unsupported encoding outside selected scope refuses at decode;
   missing essential supported-source behaviour keeps this milestone
   OPEN. No `C001`-without-family-proof regression
   (`EMITTER-INVENTAR.md` §11: a disappearing `weigere(` site
   without its family proof is a regression).
2. **Fetched-byte execution through the common architecture**: every
   admitted form executes through the 660 composition over canonical
   state — decode from actual bytes, length/permission/fault checks,
   register/flag/FP effects, address/access rules,
   TSO/atomicity/interrupt/control gates. Unsupported encodings refuse
   explicitly (`decodeExt`-style fallback + planted malformed-byte
   refusals).
3. **Omission ledger proved, not parked**: defined-AF rows (666),
   failed-CAS access rules (662), per-access canonical-form faults
   (670), FP sticky/payload observations incl. MXCSR
   establishes/preserves per context (668), CPUID/XCR0/OSXSAVE context
   (674), device-memory ordering (676) are each PROVED for every
   selected form that needs them. None may be closed by deferral,
   CUTS, or a silent `none`: any still-open item keeps this milestone
   OPEN by name.
4. **Model-side TSO/atomicity facts proved** (prerequisite for the
   6B bridge, not the bridge itself): per-access TSO machine facts
   over canonical byte memory and per-core FIFO buffers
   (forwarding, issue, flush); the aligned-word single-copy atomicity
   table (which widths/alignments are one event: aligned 32/64-bit
   MOV; wider/misaligned/cross-carrier access tears and has no single
   W message); LOCK RMW as one atomicity unit with success/failure
   distinctness; fence drain semantics (MFENCE orders + drains own
   buffer; SFENCE/LFENCE narrower; no fence drains another core's
   buffer); 128-bit vector access NOT single-copy atomic; fault order
   vs concurrent observers. These facts BELONG TO the model: the 6B
   source W/GX refinement consumes them but does not re-prove them.
5. **Assumption ledger clean**: only named silicon/device/timing
   behaviour is assumed; gate/binding/OS contracts are user logic
   with checked proofs (§4, including the two §12 item 7 gaps closed
   or dated with owners); `gabbro_ziel` axioms exactly
   `propext, Classical.choice, Quot.sound`.
6. **Negative hardware evidence**: joint memory-changing fetched runs
   plus planted malformed-byte/fault/control-state/overlap/privilege
   refusals per producer, with poison + positive probes for every new
   checker-side refusal.
7. **Exact independent review evidence** (assigned pairs from the
   committed prompts `lanes/660.md`–`lanes/677.md`; pairing only, no
   verdict claimed here): 661 reviews 660, 663 reviews 662, 665
   reviews 664, 667 reviews 666, 669 reviews 668, 671 reviews 670,
   673 reviews 672, 675 reviews 674, 677 reviews 676 (677's prompt
   text repeats the 660 title in parentheses after "author676" —
   recorded as written; nothing inferred). An earlier draft of this
   matrix wrote "reviewer = author + 18"; that arithmetic described a
   different wave and is WRONG for this one — struck and replaced by
   the pairs above. DONE requires each reviewer's committed VERDICT on
   its exact candidate; number arithmetic never constitutes
   acceptance. Green `./lean-bau` and standard axioms per candidate
   before any merge.
8. **Portability preserved**: no implicit Linux/POSIX/libc/ELF
   dependency; freestanding has no mandatory host runtime or dynamic
   loader; every selected profile retains final-byte, entry,
   support-code and mapping validation (AGENTS §3).

What 6A does NOT require: the future complete compiler theorem, the
Rust backend, or measured performance. Defining the hardware-only
milestone as requiring `valX86_sound`, the source-to-final-loaded-byte
closing theorem, or the Rust backend would hold hostage a model that
must stand on its own feet first.

### 6B. REQUIRED FOLLOW-ON DONE (mandatory, OPEN — not discarded)

Generic source-to-binary validation remains mandatory and OPEN. The
6A/6B split must NOT be read as dropping the per-access TSO/source
obligations the compiler needs — they live here, as requirements:

1. **Per-access TSO → W → GX bridge**: forward simulation x86-TSO → W
   per access (O-align/O-access lemmas, atomicity/tearing table
   consumed from 6A item 4, SB and forbidden-outcome probes failing
   closed), composed with the preserved `schwach_ist_gX`. The
   `seq_cst`-as-release/acquire modelling stays a documented sound
   over-approximation (no total order claimed); CAS loops need a
   static attempt bound or recorded DIVERGENCE; a fence is never
   removed on race-freedom alone. Owners: TSO-wave bridge lanes
   (567/573/574 pattern); consumers must not re-abstract what 6A
   proved.
2. **Image/ABI/entry/budget connection**: actual loaded mapping,
   relocations followed by re-decoding, source-memory representation,
   source duties, runtime/entry bodies, budget-stop/work ordering;
   `valX86_sound` and the source-to-final-loaded-byte closing theorem
   proved; every layout change revalidated (`layoutOk`).
3. **Full publication**: integrated master with green `./lean-bau`,
   zero-failure `./cargo-pruef`, emission and key-scan gates; Rust
   backend against reviewed interfaces; §10 measurement baselines
   published in `DIRECT-COMPILER.md`. No push past a red gate; no
   weakening of verifier verdicts on resource failure.

Classification rule for atomicity/per-access facts: target hardware
facts (single-copy atomicity table, LOCK unit, fence drain effects,
tearing, fault-vs-observer order) belong to 6A; the simulation that
maps each target access onto W messages and GX runs, with its
alignment/containment/non-overlap proofs, belongs to 6B.

## 7. Follow-up tasks (exact NEW paths, dependencies, sketches, witnesses, rejection criteria)

Each task owns ONLY its named NEW module (+ additive umbrella import
+ its `MUSE-REPORT-NNN.md`); source/checker/Spec/goal/emitter files
and friend-reserved optimiser files stay untouched. F1–F6 close 6A
(hardware model); F7–F8 are the mandatory 6B follow-on (bridge and
closing validator) — required, not optional, and not a parking lot
for essential model obligations.

- **F1 — Locked forms completion** (6A; depends on accepted 664 address
  API, 660 adapters): `grammatik/Grammatik/X86/LockedFormsFull.lean`.
  Sketch: LOCK XADD/CMPXCHG word rows with flag/register/RIP effects,
  failed-path access rule from the manual, fence drain/barrier
  witnesses. Negative: failed-comparison permission mutation, LOCK on
  register-only form, truncation, unsupported alignment. Reject:
  stutter re-presented as full ISA; unbounded CAS progress; silent
  trust in the old false-path equation.
- **F2 — Canonical-form faults** (6A; depends on 664, 660): extend the
  670 module or a named follow-up with per-access noncanonical
  (#GP) classification tied to real fetched execution. Negative:
  bit-47-violating effective address admitted. Reject: image-level
  `kanonischBereich` cited as per-access proof.
- **F3 — Defined-AF rows** (6A; depends on 666): per admitted integer row,
  either the defined auxiliary-carry value or a proved
  non-observability lemma consumed by every flag consumer. Negative:
  AF-observing sequence across an `af = none` row claimed equal.
  Reject: weakening a flag consumer to make the row fit.
- **F4 — FP observation closure** (6A; depends on 668, IEEE kernel):
  payload/payload-signalling and sticky-flag accumulation rules, or
  proved non-observability through every program-observable channel;
  MXCSR establishes/preserves per context. Negative: NaN-payload-
  distinguishing store-load, SNaN-quieting observation, sticky-flag
  survival across a claimed reset. Reject: class-level agreement
  cited as raw-bit fidelity; fast-math/FMA fusion smuggled in.
- **F5 — Enabled-state proofs** (6A; depends on 674): CPUID/XCR0/XGETBV
  model with entry-established facts re-checked per image; Tier 3
  AVX2 rows gated per named CPU profile. Negative: AVX2 bytes
  admitted with XCR0 YMM clear; context-switch clobber of upper YMM
  across a call-preserved boundary. Reject: `osXmm : Bool` cited as
  completion evidence.
- **F6 — Device-memory ordering** (6A; depends on 676, TSO bridge):
  memory-type/order rules for admitted MMIO (and DMA if ever
  admitted), generic device-response interface, typed admission
  memory-kind profile. Negative: MMIO access reordered as WB-RAM;
  DMA access through the RAM rule. Reject: RAM/TSO inheritance for
  device memory; Linux/POSIX assumption; fabricated C wrapper.
- **F7 — Typed-carrier TSO bridge** (6B follow-on; depends on 6A item 4
  facts and accepted TSO-wave bridge interfaces): per-access x86-TSO → W
  simulation with O-align/O-access, atomicity/tearing table (consumed
  from 6A item 4), SB/forbidden-outcome probes.
  Negative: torn 128-bit shared store claimed atomic; misaligned
  word claimed single-copy. Reject: byte-level projection cited as
  the full bridge; SC word effects substituted for buffered accesses.
- **F8 — Closing validator** (6B follow-on; depends on 6A DONE plus F7):
  `valX86_sound` + source-to-final-loaded-byte theorem with full
  negative-probe suite. Reject: `valX86` mapping/decode checks cited
  as source refinement; any layout change without revalidation.

## 8. What this document does and does not claim

It claims: the scope above was read off the implementation and
accepted Lean modules named, with classifications per the stated
evidence rule, and every unbounded/foreign path named instead of
hidden. It does not claim: any x86 correspondence, any TSO/ABI/layout
proof, any accepted byte chain, or any performance figure. There is
no completed direct-x86 chain (plan §4 measurement); the two closed
C chains remain legacy evidence only. Counts (94 X86 modules, 50,368
physical lines, measured in this clone at this revision — the older
handoff snapshot said 62 modules / ~26,300 lines) are not completion
evidence. No in-flight candidate state is claimed: producer lanes
660–676 and reviewer 679 work in their own clones, and no VERDICT on
this matrix exists here — lane 679 (`lanes/679.md`, exact review of
author 678 with `CANDIDATE: 678 <HEAD>` and `VERDICT: ACCEPT or
REPAIR`) is pending at the time of writing.

*CUTS (organisation lane 678): no Lean theorems; no decoder/memory/ABI/
TSO/float/cost proofs; no per-access mapping; no image contract. All
producer states are prompt-level except where the accepted tree
proves otherwise. The 6B follow-on (typed-carrier TSO→W/GX bridge,
image/ABI/entry/budget connection, closing validator, Rust backend)
remains OPEN and mandatory; it is separated from 6A, not dropped.*
