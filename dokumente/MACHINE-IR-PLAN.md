# GIR: the IR of the full Gabbro compiler (design, 2026-11-10)

**Status: design for review. Nothing here is implemented.** It is the IR of the later compiler written in Gabbro,
not a change of Stage 0: `S0IR` stays the small interpreted IR of Stage 0 and its runner
([PLAN-SELF-HOSTING.md](PLAN-SELF-HOSTING.md) §2.1). Work on GIR starts after Stage 0 covers the forms the
compiler's own source uses.

**Fixed by the owner (2026-11-10).** No refinement and no translation validation. Every optimisation is proved with
GabbroV as user logic of the compiler. GabbroV is independent of M and N. M proves that the compiler emits correct
machine code. Extreme optimisations are planned, on every CPU architecture, including special instructions.

## 1. The shape in one table

| Stratum | What it is | Who carries its correctness |
|---|---|---|
| **GIR-H** | target-independent SSA over typed values and region memory | lowering theorem source → GIR-H (generic, Lean) |
| **GIR-M** | the same graph, but every operation is an instruction form of ONE target | each pass GIR-H → GIR-H → GIR-M: a GabbroV proof `Beh(pass P) = Beh(P)` |
| **bytes** | GIR-M with physical registers, encoded form by form | the encoder is form-wise (shape contract) + M on the CPU |

One semantic framework serves both strata: GIR-M is GIR-H with a different operation table. A pass never leaves
the framework, so every pass statement is the same sentence, `Beh(P') = Beh(P)`.

**The design rule that makes special instructions cheap:** the meaning of every machine instruction form is
*defined* as a GIR-H term (its *expansion*). So an instruction is never a new primitive of the semantics; it is a
named abbreviation with an encoding.

## 2. No undefined behaviour, facts instead

LLVM-style optimisation power comes from undefined behaviour (`undef`, `poison`, signed overflow, aliasing rules).
That is what makes its proofs hard, and Gabbro does not need it: the source checker and GabbroV already *prove* what
C compilers *assume*.

- **Every operation is total or traps.** Division by zero, a failed bound and a failed contract are explicit
  `trap k` terminators with the stop code of machine G. There is no `undef`, no `poison`, no `unreachable`.
- **Facts** are the optimiser's licence. A fact is a ghost annotation on a value, an access or a loop:
  range (`lo ≤ v ≤ hi`), no wrap, alignment, non-aliasing of two accesses, trip-count bound, purity of a call.
  A program is well-formed only if every fact holds in every run (`FaktenGueltig`, a Lean `Prop`).
- **Where facts come from:** the source certificate (`Akzeptiert`, ranges, `decreases`, region disjointness,
  ownership, race freedom from `RennfreiBis`, user logic from GabbroV) and proved analyses. A pass may use a fact
  and must preserve `FaktenGueltig`; a pass that cannot keep a fact drops it.
- **FREE values** are the only nondeterminism besides scheduling: a result the vendor leaves undefined (flags
  after `bsf` on zero, `AF` after a shift) is a fresh `free` value. The GIR-M checker (a Lean `Bool`) refuses a
  program in which an observable result depends on a `free` value. This is the vendor-neutrality rule of AGENTS.md
  §3 as an IR rule.

## 3. GIR-H

**Values.** `iN` for every width (legalised later), `f32`/`f64` (native, `RootNativeFloat.Hardware`), fixed vectors
`vK×T`, mask vectors `mK`, length-parametric vectors `v[vl]×T` with an explicit length value (SVE, RVV), aggregates
only as SSA tuples. An address is `addr⟨R⟩`: a byte offset inside a named region `R`, never a bare integer, so
"memory comes as a region, never from a number" survives lowering.

**Graph.** Functions of basic blocks with block parameters (no phi nodes). Terminators: `jump`, `branch`, `switch`,
`call`, `tailcall`, `ret`, `trap k`. A call carries its contract and effect summary, so inlining and
interprocedural passes read the same contracts the checker read.

**Memory.** Byte-addressed, little- or big-endian by target profile; an address is the pair (space, byte) of the
goal theorem's `speicherAdressen`. Memory is in SSA form *per region*: every load and store names its region and
threads that region's memory token. Two accesses to different regions are independent by construction, so
reordering across regions needs no alias analysis and no proof beyond the token structure.

**Access classes.** `plain` (race-free by the goal theorem, so sequential reasoning is valid for it),
`atomic ord` (explicit ordering, a barrier for reordering), `device` (volatile register access, never duplicated,
removed or reordered), `stack`.

**Observable events** are system calls, atomic and device accesses, stores into shared regions, traps and the
function result. `Beh(P)` is the set of event traces. Pure computation may move freely between events; a trap may
not cross an event.

**Cost.** Every function carries its bound from `ZeitAb`. A pass proves `cost(P') ≤ bound` in the abstract cost
model, so the time guarantee of the language survives optimisation instead of being re-measured.

## 4. Target tables

A target is data in Lean, not code in the compiler:

```
Target  = { word, endian, registers, classes, forms : List Form, abis, features, memoryModel }
Form    = { name, operands : List OperandClass, fixed : implicit registers made explicit,
            expansion : GIR-H term over operands, flags and memory,
            free      : results the vendor leaves undefined,
            encode    : Operands → Option Bytes,   -- with decode ∘ encode = id
            features  : ISA extensions required,
            privilege, cost }
```

- **Flags are values.** A form returns its flags as a second SSA result of type `flags⟨T⟩`; a conditional branch,
  `cmov`, `adc` or `csel` consumes one. Flag reuse and compare elimination are then ordinary SSA rewrites.
- **Implicit operands are explicit.** x86-64 `mul` has `rdx:rax` as operands with a fixed-register constraint;
  `rep movsb` has `rcx`, `rsi`, `rdi` and a memory effect over two region ranges; `cmpxchg16b`, `pdep`, `pext`,
  `popcnt`, `lzcnt`, `crc32`, `aesenc`, `vpternlog`, AArch64 `madd`/`csel`/`ldp`, RISC-V `Zb*` are each one table
  row.
- **Hardware oracles** (`rdtsc`, `cpuid`, `rdrand`) return `free`-like oracle values under a named assumption, as
  `AxVertragO` does at source level.
- **Features.** A form names the extensions it needs. A function compiled for a feature set carries that set as a
  requirement of its profile; multi-versioning is several variants plus a dispatcher that is ordinary GIR code.
- **Memory model.** `memoryModel` (x86-TSO, the Arm and RISC-V weak models) matters only for `atomic` accesses:
  each target states which form implements which ordering.

**Source intrinsics.** A Gabbro binding may name a form. On a target without it the compiler emits the expansion,
which is ordinary GIR-H. A special instruction is therefore portable by definition.

## 5. Optimisation classes and what carries them

| Class | Stratum | IR feature it relies on |
|---|---|---|
| inlining, specialisation, devirtualisation | H | calls with contracts and effect summaries |
| GVN, PRE, SCCP, LICM, strength reduction, dead store | H | SSA, per-region memory tokens, facts |
| loop unrolling, interchange, fusion, fission | H | trip-count and disjointness facts |
| loop and SLP vectorisation | H | vector, mask and length-parametric types |
| instruction selection, addressing modes, fused and special forms | H → M | expansions (§6) |
| compare elimination, flag reuse, `cmov`/`csel` formation | M | flags as values |
| register allocation, spilling, coalescing, rematerialisation | M | virtual then physical registers, register classes |
| scheduling, block layout, hot/cold splitting, alignment | M | events fix the order that must stay; layout is not semantics |
| peephole | M | forms and expansions |

**The engine: rules proved, choice free.** A rewrite is a rule `pattern, condition, replacement`. Its soundness is
one theorem. Which rule fires, where and in what order is heuristic and needs no proof, because every step goes
through the proved rule gate. Equality saturation (an e-graph over the pure part of a region) fits this exactly:
saturation and extraction are free, each rewrite is a proved equation.

## 6. The generic theorems (Lean first)

1. **`gir_sem`**: the small-step semantics of GIR, parametric in the target table, over GX for concurrency.
2. **`lower_ok`**: source → GIR-H preserves behaviour, generic over programs (the Stage-0 lowering theorem for the
   larger IR).
3. **`select_ok`**: replacing a matched GIR-H subgraph by a form whose expansion equals it preserves behaviour.
   Proved once. A selection rule is then an *equation between two GIR-H terms*, and a new special instruction
   needs its table row and its equations, no new semantics.
4. **Pass theorems** `Beh(pass P) = Beh(P)` and `FaktenGueltig` preserved: stated in Lean, proved with GabbroV for
   the Gabbro implementation of each pass.
5. **`encode_ok`**: `decode (encode i) = i` for every form and operand class (as `decode_enc` of the runner), and
   the machine step of a decoded instruction is the form's expansion.
6. **`m_vollstaendig`**: M is complete for the encoder (§7).

## 7. M over instruction forms

Only the encoder must be form-wise, and it is by nature: one instruction after the other. So the cells of M are
`form × operand class`, not source forms.

- **Complete** means: every form the encoder can emit occurs in M, in every operand class (register class,
  immediate width, addressing mode, short and long branch) at the class boundaries.
- **What M proves:** the compiler's bytes equal the reference's bytes on M, hence everywhere (shape contract of
  the encoder); and every form of the table was measured on the CPU against its expansion.
- **What stays a named assumption:** `Hardware T`, the statement that the CPU implements the table's expansions
  for all operand values and independent of the surrounding code. M is its evidence, not its proof. The table
  holds only the forms the compiler uses; no full CPU model is built.
- **M grows with the instruction set, not with the optimisations.** A new pass needs a GabbroV proof and no new
  test unless it introduces a new form.

## 8. What is hard

- **Register allocation** without a per-compilation check is a direct correctness proof; it is the largest
  single pass proof (CompCert chose validation here).
- **Equations for selection rules** over bit vectors: `bv_decide` is on the guardian's forbidden list, so they are
  proved by hand or by a reflective procedure with its own soundness theorem.
- **Vector and loop passes** need invariants over memory; the region tokens and facts are meant to make them
  local, which is unproved until one such pass is done.
- **Weak memory** beyond DRF-SC stays NOT CLAIMED as in `Spec.lean`; `plain` accesses avoid it, `atomic` accesses
  are barriers.

**Recommended first step:** GIR-H semantics plus one medium pass (GVN with per-region memory) proved with GabbroV,
to measure what a pass proof costs before the other passes are planned.

## 9. Owner questions

1. **AGENTS.md §11 says the pipeline has no persistent SSA IR.** This design contradicts it. Recommended: replace
   that sentence; extreme optimisation without an SSA IR has no proof route here.
2. **Register allocation and scheduling: a proved in-compiler gate that checks the result and refuses otherwise?**
   It is a check per compilation, not a validation of the binary. Recommended: allow it for these two passes only;
   otherwise the direct proof is on the critical path.
3. **Length-parametric vectors (SVE, RVV) in the first version?** Recommended: types in the design from the start,
   forms and passes after the fixed-width ones.
4. **Privileged and boot forms** belong to [LOW-LEVEL-SYNTAX-PLAN.md](LOW-LEVEL-SYNTAX-PLAN.md); the table has the
   `privilege` field for them. Recommended: same table, later.
