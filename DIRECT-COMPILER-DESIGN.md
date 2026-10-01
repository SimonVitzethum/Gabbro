# Direct compiler detailed design: generic source-to-final-bytes compilation with fast validation

*Lane 323, 2026-10-01. Status: PROPOSED design, not an implementation or a proof.
Nothing here claims any source-to-x86 chain is closed. Central progress record:
[DIRECT-COMPILER.md](DIRECT-COMPILER.md). All source-to-executed-final-binary
claims remain OPEN.*

## 0. Reading guide and claim boundary

This document is a plan. Every section marked PROPOSED needs Lean modelling,
generic proofs and review before any Rust part is built. Existing helpers are
bounded foundations, not implemented native compilation. No new mini-model is
proposed; all names refer to the canonical vocabularies below.
## 1. Objective and trust chain (PROPOSED)

The compiler accepts EVERY full source unit the Lean checker accepts and
produces a final relocated executable image whose every executed byte refines
the source model. Lean first, then Rust: the IR, lowering, optimisation rules,
encoder/decoder, image layout, ABI, TSO bridge and validator are modelled and
proved generic in Lean 4; the Rust backend (optimiser, allocator, encoder,
layout, certificate emitter) is untrusted and its output is re-checked by the
Lean validator. Target quality is `-O3`-like scope (constant/copy propagation,
DCE/CSE, selective inlining, register allocation with private spills, peephole
selection, LICM, bounded unrolling, selective SIMD after its correspondence is
proved) plus invariant-derived extras (redundant-check removal, strength
reduction, alias separation, protected-load reuse at proved locations). No GCC
parity promise. Runtime, bindings and OS surfaces are user-logic bodies with
checked contracts; only named silicon, device and timing behaviour are
hardware assumptions ([Spec header](grammatik/Grammatik/Zielsatz/Spec.lean),
[QUELLBRUECKE §2](dokumente/x86/QUELLBRUECKE.md)).

Chain (see [plan §§0–5](dokumente/PLAN-UEBERSETZUNGSVALIDIERUNG.md)):

```
source text -- Lean uebersetzeAllg --> P over declOf u, duties, checker Bool
   |  (T3 parse fidelity, Pflichten/src, PrueferX AkzeptiertSpecX)
   +-- untrusted Rust backend --> final image bytes + certificate hints
            |  (source -> IR -> opts -> allocation -> machine instr
            |   -> FINAL relocated bytes -> loader -> fetched decoded steps)
            Lean decoding and validation (valX86 E bild = true, decided)
            |  generic refinement per-access x86-TSO -> W -> GX
            existing gabbro_ziel over GX (premises (a)(b)(c)(d) unchanged)
```

Obligations are source-computed in Lean from the source (`DutyExport`,
`EffectExport`, `AtomicExport`, `FpExport`, `CostExport`, `LowerMap` per
[IR-VALIDIERUNG §5.1](dokumente/x86/IR-VALIDIERUNG.md)); actual parameters,
results and simulation are proved, never assumed. The delivered closing
theorem `schluss_x86` takes NO independent refinement premise: refinement is
DERIVED via generic `valX86_sound` ([QUELLBRUECKE §4](dokumente/x86/QUELLBRUECKE.md)).
Default is refusal: any unproved form, failed check, or missing proof refuses
the image. A refused OPTIONAL optimisation falls back to another certified
translation of the same source (cheaper route, re-validated); a MANDATORY
validation failure (decode, permission, relocation, entry, refinement,
duty/effect mismatch) refuses outright — never a warning, never silent skip.
`gabbro_ziel` keeps exactly `propext`, `Classical.choice`, `Quot.sound`.

## 2. EXACT current pilot (CHECKED against tree)

Canonical vocabulary: [Typen.lean](grammatik/Grammatik/X86/Typen.lean)
(`Gabbro.Grammatik.X86`); canonical encoding contract:
[BYTE-PILOT](dokumente/x86/BYTE-PILOT.md); scope inventory:
[EMITTER-INVENTAR](dokumente/x86/EMITTER-INVENTAR.md). All 14 `Befehl`
constructors, all 64-bit only, all PROVED as vocabulary (no execution proof
claimed at pilot):

| # | Constructor | Mnemonic | Operands / form | Canonical encoding (BYTE-PILOT) | Length |
|---|---|---|---|---|---|
| 1 | `movImm64 dst v` | MOV | reg64 dst, imm64 | REX.W + B; B8+rd; imm64 LE | 10 |
| 2 | `movReg64 dst src` | MOV | reg64, reg64 | REX.W R=rB B=rB; 89; ModRM C0+8rs+rd | 3 |
| 3 | `addReg64 dst src` | ADD | reg64, reg64 | as above, opcode 01 | 3 |
| 4 | `subReg64 dst src` | SUB | reg64, reg64 | as above, opcode 29 | 3 |
| 5 | `xorReg64 dst src` | XOR | reg64, reg64 | as above, opcode 31 | 3 |
| 6 | `cmpReg64 lhs rhs` | CMP | reg64, reg64 | REX.W; 39; rhs in reg, lhs in r/m | 3 |
| 7 | `load64 dst base d` | MOV | reg64, [base+disp32] | REX.W; 8B; ModRM 80h; SIB 24h iff base%8=4; disp32 LE | 7–8 |
| 8 | `store64 base src d` | MOV | [base+disp32], reg64 | as above, opcode 89, src in reg | 7–8 |
| 9 | `jump32 d` | JMP | rel32 | E9 disp32 | 5 |
| 10 | `jumpIf32 c d` | Jcc | cond, rel32 | 0F (80+code(c)) disp32 | 6 |
| 11 | `call32 d` | CALL | rel32 | E8 disp32; return addr = addr after insn | 5 |
| 12 | `push64 src` | PUSH | reg64 | 50+r low; 41 50+r high | 1–2 |
| 13 | `pop64 dst` | POP | reg64 | 58+r low; 41 58+r high | 1–2 |
| 14 | `ret` | RET | — | C3 | 1 |

Registers: 16 GP `rax rcx rdx rbx rsp rbp rsi rdi r8–r15` (codes 0–15), no
high-byte legacy forms (`ah/bh/…` refused). Conditions: 16 `Bedingung` codes
`o no b ae e ne be a s ns p np l ge le g` (order 0–15). Memory: byte-addressed
`Speicher.bytes` with per-address R/W/X bits; loads/stores base+sign-extended
disp32, mod=10 always, `rbp/r13` real bases (never RIP-relative). Fault model:
permission-checked access (lane 271); flag model: `Flags` with
`af : Option Bool` (undefined, not false); fault/flag preservation per form is
lane-272 work, OPEN. Planned extended forms (widths, LOCK, fences, FP/SIMD,
indirect control — §§3–6) and bounded accepted helpers (`Wort.lean` modular
ops, `Speicher.lean` LE access, width `Breite`) are NOT pilot vocabulary: a
width helper or SIMD helper does not mean ISA support, and any byte outside
the canonical subset is explicitly refused (non-canonical but architecturally
valid alternatives are outside the pilot).

## 2A. Selective hardware model and why 14 forms are not maximal performance (PROPOSED)

Feasible and intended: the hardware model covers EXACTLY the emitted
instruction forms the backend can produce — no more, no less. For each
selected form it models every architecturally observable state, effect and
interaction: general registers and flags read/written, memory permissions and
alignment checked per access, decode/fetch boundaries and lengths from the
bytes, fault delivery (permission, alignment, divide error, illegal encoding),
and — for the selected concurrent/FP forms — the TSO store-buffer interaction,
interrupt/masking interaction and FP control state (MXCSR scope, masks,
sticky-flag reservation). Selection is driven by generic source emitter
construct needs ([EMITTER-INVENTAR](dokumente/x86/EMITTER-INVENTAR.md) §§2–10:
which widths, aggregates, calls, gates, entries the language lowers), never by
particular programs or names. A whole-hardware model — internal pipeline,
caches, branch predictors, transistor behaviour — is NOT needed for functional
translation validation and is explicitly out of scope: functional correctness
needs the retired-instruction semantics plus its asynchronous interactions,
not cycle mechanics. Execution-time guarantees are a separate matter: they
still need named conservative hardware assumptions plus the separate cost
transfer of §9/[FLOAT-ZEIT §8](dokumente/x86/FLOAT-ZEIT.md); microarchitectural
tuning (layout, alignment, scheduling) is MEASURED per §10, never guaranteed
maximal globally — no numerical instruction-count target and no
maximal-performance claim appear anywhere in this design.

Coverage rule ("only reachable software bodies?"): ALL reachable final code
must be covered — emitted unit, generated driver, compiled-in binding code,
runtime and every handwritten entry path ([IMAGE-ABI §10](dokumente/x86/IMAGE-ABI.md));
anything reachable but unmodelled (unsupported data form, unselected encoding,
illegal entry) is precisely REFUSED by decode/validator, never silently
assumed. Plainly: 14 is a proof pilot, inadequate for high performance across
Gabbro — it lacks multiply/divide, shifts, all sub-64-bit forms, all FP, all
atomics/fences, CMOV/SETcc and indirect control, while forcing needlessly long
encodings (always-10-byte `movImm64`, disp32-only memory forms, no short
branches). The planned practical scalar profile (§3) closes the everyday gap;
feature-gated tiers (§6) carry SIMD/BMI/AVX separately. Even so, the exact
selected-forms model remains nontrivial: every added form multiplies the
interactions with asynchronous events (interrupts landing mid-sequence,
another core's access between a step's accesses, faults on unselected CMOV
operands) that the per-access refinement (§5) must survive. Proof boundaries
are unchanged: only named silicon/device/timing behaviour is a hardware
assumption; OS, runtime, loader and binding bodies stay user logic with
checked contracts; the goal statement and all guarantees stay unchanged.

## 3. PLANNED ISA table: minimal practical-performance profile (PROPOSED)

Not Turing-completeness alone: the profile must compile ordinary integer
code, calls, position-independent images and concurrent atomics at acceptable
quality. Each row: PROPOSED until its Lean execution semantics, encoder row,
decoder refusal of neighbours, and correspondence lemma close (owner lane 272
for execution, 279 for codec, 274 for concurrency rows). References below are
design inspiration only (Intel SDM <https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html>,
AMD APM vol.3 <https://docs.amd.com/v/u/en-US/24594_3.37>,
Intel optimisation manual <https://www.intel.com/content/dam/doc/manual/64-ia-32-architectures-optimization-manual.pdf>):
they fix future exact modelling targets, they prove nothing about the Lean
model matching hardware. No exotic opcode/flag detail is asserted here.

| Mnemonic group | Operand forms / class / width | Reason (performance) | Priority | Semantic obligations / status |
|---|---|---|---|---|
| MOV / MOVZX / MOVSX / MOVSXD | reg, [base+disp]; r/m 8/16/32 -> reg 16/32/64, zero/sign extend | narrow carriers, struct fields, ABI args without 64-bit widening lies | P0 (first extension) | width-exact value + fault preservation; narrow shared access needs O-align single-event proof; OPEN |
| LEA | reg64, [base+index*scale+disp] | address arithmetic for aggregates, arrays, spill slots without flag clobber | P0 | pure (no memory event, no flags); displacement-fits-signed-32 side condition; OPEN |
| ADD/SUB/AND/OR/XOR/NOT/NEG | reg/r/m 8/16/32/64 + imm | ordinary integer code; pilot has only 64-bit add/sub/xor | P0 | per-width CF/OF/SF/ZF/PF identity (`Wort.lean` keeps CF distinct from OF); AF stays `none`; OPEN |
| CMP/TEST | reg/r/m, reg/imm; TEST r/m, reg/imm | branches, `narrow`, loop conditions at every width | P0 | flag identity per width; NaN-style unordered rows belong to FP (§4), not here; OPEN |
| SHL/SHR/SAR (+ROL/ROR if cheap) | reg/r/m 8–64 by imm/CL | scaling, field packing, hashing loops | P1 | shift-count masking semantics proved per width; checked-arithmetic stop point preserved; OPEN |
| IMUL (r64,r/m; 3-operand imm) / MUL | 16/32/64-bit forms | ordinary multiply without library call | P1 | overflow (CF/OF) + signedness per width; strength-reduction rules cite this row; OPEN |
| IDIV/DIV | fixed RDX:RAX dividend, divisor r/m | remainder, bounds, hashing | P1 | divide-error (#DE on zero/overflow) = `hardware`-stop preserved exactly; LICM/DCE may never speculate it; OPEN |
| ADC/SBB | reg/r/m + CF | only if multi-precision integers enter the language | P2 (optional) | carry threading lemma; admit only when a source form needs it; else refused |
| Jcc/JMP (near, rel8+rel32 canonical choice) | cond + rel | dense branches, loop closings | P0 | target = virtual next-RIP + sign-extend(disp), decoded-start check ([IMAGE-ABI §6](dokumente/x86/IMAGE-ABI.md)); short/long choice is layout-level, re-validated; OPEN |
| SETcc | r/m8, cond | branchless compares, bool materialisation | P1 | byte result 0/1 exact; no flag leak; OPEN |
| CMOVcc | reg, r/m | branchless selects in hot paths | P1 | PROVED FIRST before lowering: unselected memory operand may still fault (page fault on the unselected side is architecturally real). Generic proof obligation, not a peephole. Until proved, CMOV with a memory source is refused; register-only CMOV first |
| CALL direct / RET | rel32 / — | calls today | in pilot | caller/callee ABI proof ([IMAGE-ABI §§7–8](dokumente/x86/IMAGE-ABI.md)); OPEN |
| CALL/JMP indirect | r/m64 target | function pointers, dispatch, `entry fn` values (N575–N577) | P1 | checked provenance: validator-tracked target set (jump-table/data-flow certificate or refusal); every indirect target a decoded start or listed entry; no forged pointer (M140); OPEN |
| LOCK CMPXCHG / LOCK XADD (/XCHG) | r/m + reg, explicit ordering | atomics/RMW lowering (§5) | P0 for concurrency | full-barrier + single atomicity unit; success/failure distinctness; maps to W `rmw` field; pilot has NO LOCK form — every exchange lowering unmapped until this lands; OPEN |

Call stack and ABI profile: 16-byte call alignment, red-zone rule per image,
callee/caller-saved discipline stated per image and checked per call/return,
private spill slots disjoint with permissions checked, guard pages on thread
stacks ([IMAGE-ABI §§5,8](dokumente/x86/IMAGE-ABI.md)). No integer-to-pointer
or integer-to-function-pointer conversion enters the language (M140); code
addresses travel as `entry fn` values under the N575–N577 discipline.

## 4. FP scalar baseline SSE2 binary64 (PROPOSED)

Source surface is binary64 throughout (`GFloat = GBits f64`,
[Typen.lean](grammatik/Grammatik/Typen.lean); full map in
[FLOAT-ZEIT §§1–4](dokumente/x86/FLOAT-ZEIT.md)). Baseline target: scalar
SSE/SSE2 only. Native `f32` and its conversion bridge are NOT closed: the
model computes every `Ty.fl` node in binary64, so genuine `f32` single-rounding
differs numerically — every `float` node is REFUSED until path (a)
source-width model extension or path (b) proved fragment refinement closes.

| Source form | Machine form (PROPOSED) | MXCSR / obligation |
|---|---|---|
| `GleitOp.add/sub/mul/div` f64 | ADDSD/SUBSD/MULSD/DIVSD xmm, xmm/m64 | RNE (RC=00); class-level result incl. ±0; `0*inf` NaN, `0/0` NaN preserved; float ops are faulting (invalid/div0/overflow/underflow/inexact flags + `logik bereich`), never DCE/CSE-eligible as pure |
| literal / `gleitLit` | correctly-rounded build-time decimal→binary + MOVSD / RIP-relative load | one rounding only; `f`-suffix rule becomes a validator encoding check after the f32 bridge |
| `gleitVon` (int→float) | CVTSI2SD (operand-width-selected 32/64) | width obligation per source int width |
| `fllt/flle` (+ swapped ge/gt) | UCOMISD + SETcc/Jcc with JP row | NaN unordered → `false` for both `<` and `<=`; ordered-vs-unordered branch selection is correspondence, not folklore |
| `gleitNarrow` range | two UCOMISD + integer AND (`narrowCondF_ge_le` shape) | check STAYS; removal breaks `KeinLogikHaltG` |
| `gleitNarrow` finite | exponent-field bit test (`cFloatEndlich` shape) | agrees on inf AND NaN (both non-finite) |
| `gleitRoh` (float→int) | CVTTSD2SI + saturation wrapper | bare CVTT alone is NOT `gleitRoh` (indefinite `0x8000…` on invalid) |

Control state (validator-checked establishes/preserves per execution
context, never a bare stability assumption): RNE, SSE2/no-x87/no excess
precision, no contraction (encoded FMA refused; micro-op fusion is not
modelled, encoded fusion is refused), no fast-math (reassociation,
distribution, `x-x→0`, `0*x→0`, RCPSS-for-DIV, width promotion all refused),
FTZ=0/DAZ=0, all exception masks set (traps off — unmasked traps are outside
the model, refused), sticky flags RESERVED (unobserved-or-matched; SNaN
quieting needs bits lemma + flag reservation jointly). NaN payloads: relaxation
to class-level only via PROVED non-observability lemma (NaN never inhabits
`Gleit lo hi`; `flt/fle` false on NaN; no bit-observing form admitted).
AVX/FMA/packed forms are future hardware features with their own exact FP
rules (§6), never silent upgrades of this baseline.
## 5. Concurrency: reuse GA/GX/W via actual TSO refinement (PROPOSED)

Strategy per [TSO-GX-BRUECKE](dokumente/x86/TSO-GX-BRUECKE.md), confirmed by
[REVIEW-TSO](dokumente/x86/REVIEW-TSO.md): per-access forward simulation
x86-TSO → W (`x86 behaviours ⊆ W`), then `schwach_ist_gX` into the existing
`SchwachX` leg. No blanket "x86 is W/DRF-SC" (store buffering refutes it:
`sb_erlaubt` vs `sb_sc_verboten`); no G-step-as-transaction (one G step holds
several accesses — `blatt`/`dannBlatt` whole-leaf, `dannExchange` reads
`g` + update carriers and writes `g` — so lowering interleaves strictly
inside the block). Ordinary width/alignment accesses and shared atomics need
an actual per-width atomicity table: aligned 32/64-bit MOV are single-copy
atomic; anything wider, misaligned or cross-carrier tears and has no single W
message — the lowering must prove natural alignment, single-carrier
containment, non-overlap and little-endian agreement (O-align), else refuse.
An aligned word must NOT be serialised into eight observable byte writes just
because a helper is bytewise: the access-to-bytes mapping proves one event.

Planned forms: LOCK CMPXCHG (success = THE RMW access, failures = stutter),
LOCK XADD for fetch-add (constant cost, preferred over CAS loops), XCHG where
the source order needs it; MFENCE/SFENCE/LFENCE with distinct semantics
(MFENCE orders + drains own buffer; SFENCE/LFENCE narrower; none drains
another core's buffer — "MFENCE everywhere" does not discharge assumption
(5)). Release/acquire need no fence on TSO (plain aligned MOV already
orders); `seq_cst` lowers to LOCK/MFENCE-bracketed MOV and stays modelled as
release/acquire in W (sound over-approximation, documented limit, no total
order claimed). Orders are parametric (`SchwachX` quantifies over ALL `ord`):
every shared access justifies at least release behaviour. No invented CAS
termination or constant cost: a CAS loop is unbounded retries vs one source
step — static bound `k` from contention structure or DIVERGENCE recorded per
program (cost-bound claim refused); `FortschrittG` is enabledness only and
needs no spin-termination proof, but work bounds need the attempt bound.

Invariant facts permit optimisations ONLY at source-guaranteed locations:
entry ranges do not travel to loop heads or across calls; lock invariants
hold at returns, quiescence/observers and lock moves — never inside a running
writer or an arbitrary held section ([REVIEW-QUELLE-INVARIANTEN §§2,5](dokumente/x86/REVIEW-QUELLE-INVARIANTEN.md)).
A fence is never removed on "race freedom alone": race freedom is about
non-atomic carriers; fences order atomic/shared accesses, and only an exact
per-access concurrent-equivalence theorem moves them.

## 6. SIMD and performance tiers (PROPOSED)

Default: scalar only. The packed-integer helper (`X86/Vektor.lean`, lane 290,
candidate) is NOT validated vectorisation. Tiers, each gated separately:

- Tier 1 (starter, with O3 package): scalar SSE2 integer-adjacent work only —
  no vector instructions. Performance comes from §§7–8 (folding, CSE, LICM,
  allocation, layout), not lanes.
- Tier 2 (PROPOSED, first vector candidate): selected SSE2 packed-integer XMM
  forms (e.g. PADDB/W/D/Q, PADDQ, PXOR, PAND/POR, PSLLQ/PSRLQ, MOVDQA/MOVDQU,
  128-bit loads/stores), element widths 8–64 with lane count × width = 128.
  Gate: proved lane-separation lemma (lane `i` = scalar op on lane `i`, no
  cross-lane flag/exception interference) + alignment/tearing table (128-bit
  access NOT single-copy atomic — shared vector stores refused until the TSO
  bridge decides the rule) + private-or-immutable memory proof + tail loop
  preserved. Fault order (lane `i+1` never visible ahead of lane `i`),
  visibility order vs concurrent observers, tearing equivalence, per-lane
  FP-status identity where FP lanes exist — each independently refusing.
- Tier 3 (PROPOSED, later, optional): AVX2 VEX/YMM (VPADDB/…256-bit,
  VEX scalar VADDSS/VADDSD zeroing upper lanes — architecturally stated
  because XMM sharing across calls makes it observable). Prerequisite:
  CPUID AND enabled extended state (OSXSAVE + AVX bits, XCR0 XMM+YMM);
  setup/context-switch save/restore is user/binding logic with contracts —
  no OS assumption. Upper-YMM state in the relation, entry-established,
  call-preserved per proved ABI discipline.
- Optional, feature-gated + proved only: BMI1/2 (ANDN, BLSI, PDEP/PEXT),
  POPCNT, TZCNT/LZCNT — each with CPUID premise and its own correspondence;
  absent bit = refused encoding. AVX-512 deferred entirely; no
  maximal-performance universal promise is made.

Excluded from the ordinary profile (refused, not silently dropped): 16/32-bit
execution modes, segmentation, x87/MMX, BIOS/far transfers, arbitrary inline
`asm` (unbounded by construction — only enumerated proved templates from the
template register). Hardware-profile instructions (SYSCALL trap, IN/OUT,
CPUID/XGETBV, privileged IRQ/control forms) only where the source permits
(`at port` with `arch x86_64`, gates, entries): each separately proved and
hardware-scoped, never bulk-included, never dismissed as "legacy".
SSE2/TSO remain architectural long-mode instructions; "no legacy" in roadmaps
means the selected long-mode profiles above.

## 7. Optimisation inventory with premises and failure cases (PROPOSED)

Rule register design per [IR-VALIDIERUNG §3](dokumente/x86/IR-VALIDIERUNG.md):
one shared SCFG (SSA + explicit memory token), layer-A local rewrites (rule
lemma over arbitrary values + re-decided side conditions), layer-B
dataflow/CFG certificates (validator recomputes avail/liveness/dominators,
checks block maps), layer-C duty binding (writes, locks, atomics, FP modes,
costs from source exports). Phase/cost column: E = early canonicalise, M =
mid global, L = late layout/alloc; certificate size O(window) local,
O(sites) global; validator work linear in graph + recomputed analyses.

| Optimisation | Local premise (validator-decided) | Certificate | Failure case (refuse) | Phase/cost |
|---|---|---|---|---|
| Constant folding / SCCP | operands literal, width exact, no FP width change, `bruch` = `rundeBruch` | A+B avail facts | fold `float` via host `strtod` (double rounding); fold across MXCSR scope | E / O(sites) |
| CFG simplification | unreachable edge proof (decided const cond), exit edges preserved | B block map | delete a `narrow`-else edge ("unreachable" by range hope) | E / O(blocks) |
| CSE/GVN pure | identical expr, avail recomputed, same width/mode | A+B | CSE `a+b` across different `lo..hi` gates (one site's range fails) | M / O(sites) |
| CSE redundant loads | + same object/width/align, token order, AND ownership ∨ held-lock stability ∨ immutability | B+C | hoist above publishing acquire; reuse across unlock; local-disjointness alone for shared | M / O(sites+exports) |
| DCE / dead stores | pure (no token/atomic/call/check/stop/trap-capable FP) + dead confirmed | A+B | remove `0.0/0.0` ("unused" NaN hides `logik bereich`); remove spin load | M / O(sites) |
| Range/bound/overflow-check elimination | source extent proof AT the site (N571/N463/N506: gate ensures over once-bound name; constant fixed-size) | B+C | entry invariant removes check inside writer's own mutating loop; entry range across a writing call | M / O(sites) |
| Alias/access commutation | disjoint objects + same interleaving evidence as load-CSE | B+C | reorder across fence/lock/acquire-release on token evidence alone | M / O(pairs) |
| Strength reduction | per-width flag/fault identity lemma (CF vs OF distinct) | A register rule | `imul r,8 → shl r,3` with live CF; signed-divide rounding via shift; `a*2.0 → a+a` (rounding/NaN) | L / O(window) |
| LICM | invariance recomputed (exact-value, not rounded-value), non-faulting over hoisted inputs from rechecked source facts | B+C | hoist `x/n` above `n!=0`; hoist token op on shared access on local evidence | M / O(sites) |
| Inlining | block map + fresh renames + callee duties ⊆ caller site + depth discipline + GHOST call/return events (actual values, reason channel, order) | B+C | identical contracts without ghost events (`FolgeG` order lost); inline across lock floor | M / O(callee size, bounded fuel) |
| Loop unroll (bounded) | explicit `k` + trip evidence + remainder path in map; token ops duplicated, never fused | B | fuse two token ops into one wide access (tearing/visibility change) | M / O(k·body) |
| Vectorisation (future) | §6 tier-2 gate: lane separation + atomicity table + privateness + tail | A+B+C | lane-disjoint but shared-observable order inversion; all refused until vector rule proved | M / gated |
| Flags-aware peepholes | rule in register, flag-liveness, disp-fits-i32, no token op in pure window | A | `x-x → 0` dropping invalid flag; FMA fusion of mul+add; UCOMI→ordered-compare NaN swap | L / O(windows) |
| Layout / allocation | colouring vs recomputed liveness; spills fresh private frame slots, token-threaded, save/restore on all paths | B+C map | fused 16-byte spill over two live carriers; spill slot overlapping neighbour frame; address-taken spill via call arg | L / linear scan + bounded improvement |

Proof required for: source fault/refusal/stop order (faults never
"optimised"), contracts/invariants at their place, call-log `Folge` (ghost
events), execution budget (ghost source-budget correspondence — re-summing
declared costs is bookkeeping, exhaustion-timing is OPEN), actual machine work
(separate transfer). Range `x`, safe `x*8 → x<<3` never justifies signed
divide rounding or shift-count semantics. Entry invariant ceases during a
writer; lock invariant observed only in protected allowed locations; repeated
shared reads eliminated only under immutable/continuous-exclusive/held-lock
proof — a local token never suffices. Never derive `ensures`; never turn a
refusal into a warning.

Concrete generic examples (no program-name rules):

1. Copy folding: `v1 = add w64 a b; v2 = copy v1; v3 = add w64 v2 c` → drop
   the copy, use `v1` (premise: avail + dominance + width; see IR §6 worked
   certificate). Counterexample: `v1` redefined between — recomputed avail
   refuses.
2. Guard preservation: `narrow x to lo..hi else` stays even when entry says
   `x in lo..hi` if a call that may write `x`'s carrier intervenes — delete
   refused (C5 shape, review §10).
3. Hoist refusal: `wenn n != 0 { y = x / n }` — hoisting `x/n` above the
   branch turns untaken path into `hardware` stop — refused without
   non-faulting evidence (CE-2).
4. Strength-reduction refusal: `imul r,8 → shl r,3` with live CF — same
   value, different flags — refused without flag-identity lemma (CE-6).
5. Shared-load refusal: `lock L { v = *p }; …; use v` after unlock with
   another writer under `L` — reuse refused; needs continuous holding plus
   whole-unit writer discipline (CE-3).
## 8. FAST compilation architecture (PROPOSED)

Inspiration (not dependency): LLVM pass-manager discipline
<https://llvm.org/docs/NewPassManager.html> (explicit analyses, invalidation,
on-demand queries) and ThinLTO <https://clang.llvm.org/docs/ThinLTO.html>
(function summaries, independent backends, deterministic import) — no LLVM
code or library is committed; the compiler is Lean-modelled, Rust-built.

- One compact typed IR: the SCFG of [IR-VALIDIERUNG §1](dokumente/x86/IR-VALIDIERUNG.md)
  (SSA values versioned, memory token threading, closed op set, types on every
  value, source anchors required on memory/call/check/atomic/lock/stop).
  Shared effects/footprints travel with the graph; IDs interned (`v<n>`,
  block labels), blocks/ops in contiguous arenas — cache-friendly linear
  walks, no pointer chasing per query.
- Deterministic bounded passes: each pass declares required analyses and
  preserved facts; invalidation is explicit (pass drops only what it moves).
  Dataflow facts computed by bounded worklists over finite block/name sets
  with cached results keyed by graph revision; Rust hints seed check order
  only — the validator recomputes. No unbounded fixpoint: every iteration
  carries fuel (function-size + constant factor); exhausted fuel stops the
  pass with the certified unoptimised graph, never a half-rewrite.
- Bounded heuristics everywhere: inlining budget (call-site fuel × callee
  size, recursion guarded by decreases/depth), unroll factor `k` with trip
  evidence, pass-iteration caps. No exponential global search (no
  backtracking superoptimiser in the default path; any search lives in an
  optional offline pass whose result still needs a certificate).
- Fast allocation: linear-scan over live intervals (recomputed liveness,
  one sorted walk) as default — no costly graph-colouring default. Bounded
  local improvement after (spill-weight passes with small fuel, coalescing
  window) each emitting its colouring/spill certificate (§7); improvement
  that exhausts fuel keeps the valid scan result.
- Optional analyses on demand: alias/footprint answers, range facts and
  vector-legality computed per query with memo tables; valid results reused
  across passes via revision keys, stale entries discarded, never trusted.
- Parallelism: module/function-independent passes run in parallel with
  deterministic merge (sorted unit order, fixed renaming seeds); layout is
  deterministic given the same inputs (same accepted bytes cold or warm).
- Incremental: dependency hashes cover source declarations, contracts,
  effects, ABI/target data, callee summaries, hardware profile, proof
  schema and compiler version; a change re-lowers, re-optimises and
  re-checks the affected unit plus cross-unit obligations (footprints,
  lock discipline, call-log shape) and final image obligations (layout,
  relocations, entries). Caches are untrusted: a hash hit skips work, not
  checking — the validator still decides `valX86 E bild = true` on the
  final bytes. Hashing alone is no theorem.
- No guarantee dropped for speed: exhausted optional-optimisation budget →
  certified cheaper route (less inlining, no unroll, scalar); validator
  failure → refusal. Compilation work budget (fuel, caps) is distinct from
  source run budget (`passes`/`kostenTief`): the first bounds the compiler,
  the second is the proved program property. Determinism: same source +
  profile ⇒ same accepted image.

## 9. FAST validation (PROPOSED)

Proved once, checked per image: executable local certificate checkers
(`lowerOk`, per-step `check_C`, `layoutOk` — structural, `decide`-settled,
`korrOk` discipline) with generic soundness lemmas (`valX86_sound` over every
`E`/`bild`; per-rule lemmas over arbitrary operands; spill-freshness against
the TSO relation; vector rule when it lands; ghost budget correspondence).
Per image the backend ships source-derived obligations (exports of §1.3),
sharing/subproof structure (common footprints, callee summaries cited once),
and block/edge maps; the validator walks blocks/windows, re-decides side
conditions, re-threads the token, re-sums declared costs as a mismatch check.

No massive bespoke Lean textual proof per program and no constant-step trace:
certificates are data (rewrite records, avail/liveness citations, maps), not
tactic scripts; checking is kernel reduction, not search. No `native_decide`
or trusted Rust verdict: the Boolean checker must be PROVED sound and the
actual kernel-accepted result is what counts (`check_C … = true` by `decide`
inside Lean, soundness by induction at every call depth). No assumed linear
total time for dominance/solving/symbolic work: validator algorithms are
structural (dominators via standard iterative sets over the finite block
list, token threading single-pass); expensive optional transformations are
capped so their certificates stay small — a certificate that would need
superlinear checking is refused in favour of the cheaper route.

Pipeline proposal (batch kernel checking, warm workers): one worker pool type-
checks `DutyExport`/`EffectExport` summaries per function once and reuses
them; function certificates checked independently then linked by the
whole-unit map (footprints, lock floors, call logs); final global image
revalidation runs on every layout change (displacement resolution, patched
re-decode, entry predicates) — layout change without revalidation is refused.
Wallclock to produce UNVALIDATED bytes (Rust backend time) is reported
separately from wallclock to deliver an ACCEPTED image (backend + validator +
kernel); the user-facing default ships only fully accepted images.

## 10. Measurement protocol (PROPOSED — numbers UNKNOWN)

No speed is claimed: no milliseconds promised, no observed throughput cited.
First baseline is measured after the minimal lowering + validator close; the
target curve is defined after that baseline.

- Dimensions: cold / warm / incremental full compilation + validation;
  latency p50/p95 over the workload mix; throughput (IR nodes/s, source
  nodes/s); split times (analysis, optimisation, allocation, emission,
  certificate check, kernel check); certificate size; peak RSS; output binary
  size; runtime cost of the produced binary (cycles on the profile machine).
- Workloads: generic scalable GENERATED programs (nesting depth, function
  count, loop trip counts, table sizes swept parametrically) PLUS the actual
  emitter construct inventory ([EMITTER-INVENTAR](dokumente/x86/EMITTER-INVENTAR.md))
  as coverage — corpus examples alone are not scope evidence.
- Change classes: body edit, contract edit, ABI/target-data edit, profile
  edit, layout-affecting edit; parallel scaling (1/2/4/8 workers) with
  determinism check (cold vs warm identical accepted semantics);
  invalid-cache and negative-certificate probes (corrupted cache entry,
  wrong avail citation, forged spill freshness — all must refuse, timed as
  refusal latency).
- Optimisation budgets benchmarked per knob (inline fuel, unroll `k`, pass
  caps, improvement fuel): quality (binary cycles/size) vs compile time
  curves; defaults picked from the knee, exposed as a FEW stable build
  modes (e.g. `schnell` minimal-opt + full validation, `optimiert`
  full-package + full validation) with identical acceptance — no broad
  user-facing flag API. No mode skips validation.

## 11. Implementation sequence and acceptance gates (PROPOSED)

Order follows [DIRECT-COMPILER.md](DIRECT-COMPILER.md) Lean-first sequence
(§§1–9 there); no Rust part before its Lean phase is reviewed. Gates per
step: exact-candidate independent review (ACCEPT or REPAIR), green
`./lean-bau`, standard `gabbro_ziel` axioms, joint non-degenerate witnesses
for syntax-quantified theorems, poison + positive probes for checker-side
refusals, no `sorry/admit/axiom/native_decide/unsafe`.

1. Vocabulary + integers/flags + byte memory (lanes 269–271 merged; 272
   execution, 279 codec pending review). Gate: canonical encoding + round-trip.
2. Decoder + checked image/relocation/loader contract (283 merged; 279/291
   pending). Gate: altered-byte refusal witness.
3. Typed IR + source lowering + duty exports (287/288 working; 277 bridge
   design merged). Gate: `lowerOk` + full-unit identity.
4. Local/CFG optimisation rules + certificates (275 design; 288/289 partial).
   Gate: per-rule generic lemma + planted-defect refusal probes.
5. Per-access TSO refinement into W/GX (274 design; 284 TSO machine merged).
   Gate: SB/forbidden-outcome probes fail closed; O-align/O-access lemmas.
6. Stack/ABI/entries/regions/runtime/binding bodies + all reachable code
   (276 contract; 309–312 working). Gate: entry-predicate + spill-privacy + template
   x86 instances proved.
7. IEEE/control correspondence + budget/work transfer (278 design; 286 f32
   evidence merged). Gate: RNE/NaN/±0 witnesses; cost-summary soundness.
8. Closing validator soundness + finite/infinite coverage + witnesses +
   negative probes. Gate: `valX86_sound` + `schluss_x86` proved, axioms clean.
9. Rust backend against reviewed interfaces; integrated validation +
   performance measurement per §10. Gate: §10 baseline published in
   [DIRECT-COMPILER.md](DIRECT-COMPILER.md).

Open obligations (all OPEN until proved): every PROPOSED row of §§3–6; the
f32 bridge; NaN non-observability; control-state establishes/preserves;
per-access atomicity/tearing table; OBS-5 foreign-footprint/publication
chain; CAS attempt bounds; ghost source-budget correspondence; vector rule;
linking (`GabbroZielVerbund` image step); unbounded-region opt-in (finite
physical machine cannot implement unbounded memory — the opt-in loses the
static whole-program bound by design, every allocation may fail and must be
handled; a core minimal Turing-complete abstract operation set is no
implementation claim). All new files English; central progress stays primary
in [DIRECT-COMPILER.md](DIRECT-COMPILER.md) — this design is a plan, not a
progress table.

*CUTS: no Lean definition, lemma, checker Bool, decoder, validator,
refinement, cost-transfer or acceptance theorem is proved here. Profile
decisions are PROPOSED with prerequisites explicit. No runtime or compiler
speed was measured. Primary references are modelling targets, not evidence
the Lean model matches hardware.*
