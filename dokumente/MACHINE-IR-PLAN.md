# GIR: the IR and the verification route of the full Gabbro compiler

**Status (2026-11-10): approved design, nothing implemented.** GIR is the IR of the later compiler written in
Gabbro. It does not change Stage 0: `S0IR` stays the small interpreted IR of Stage 0 and its runner
([PLAN-SELF-HOSTING.md](PLAN-SELF-HOSTING.md) §2.1). The order of work is §12.

## 1. What the owner fixed (2026-11-10)

1. **No refinement and no translation validation.** Nothing is checked per compilation and refused. Every pass,
   register allocation and scheduling included, has a logic proof.
2. **Every optimisation is proved with GabbroV**, as user logic of the compiler.
3. **GabbroV is independent of M and N.** Its own correctness comes from a Lean proof.
4. **M proves that the compiler emits correct machine code.**
5. **Extreme optimisations on every CPU architecture**, special instructions included.
6. **A GIR operation is not a real instruction.** GIR is one powerful, architecture-neutral IR that expresses
   nearly every real instruction by several of its own operations. Real instructions are assigned to *cells* of
   GIR, and M is formed over the cells.
7. **An SSA IR is allowed** (AGENTS.md §11 says so since this date).
8. **Length-parametric vectors** (SVE, RVV) are in the types from the start; their cells and passes follow the
   fixed-width ones.
9. **Privileged and boot instructions** use the same mechanism, later, with
   [LOW-LEVEL-SYNTAX-PLAN.md](LOW-LEVEL-SYNTAX-PLAN.md).

## 2. The pipeline

| Stage | What happens | Who carries its correctness |
|---|---|---|
| source → **GIR** | lowering into neutral SSA micro-operations | `lower_ok`, generic over programs (Lean) |
| GIR → GIR | every optimisation | one GabbroV proof per pass: `Beh(pass P) = Beh(P)` |
| GIR → **tiled GIR** | the program is cut into cells; values get abstract locations; cells get an order | `tile_ok`, `assign_ok`, `schedule_ok`, generic in the target table |
| tiled GIR → bytes | each cell is replaced by the bytes the target table assigns | the emitter's shape contract, M, and the assumption `Hardware T` |

There is ONE IR and ONE semantics. No operation, no pass and no proof is specific to an architecture. An
architecture is a table of data (§7) plus a run of M on its CPUs (§9).

**Three things are kept apart** and must never be mixed:

| Question | Answered by | Never by |
|---|---|---|
| Is this transformation of the program right? | a logic proof with GabbroV | tests, M, a per-compilation check |
| Are these bytes the cell they stand for? | M on the CPU, under `Hardware T` | a CPU model, a proof about instructions |
| Is GabbroV itself right? | a Lean proof | M or N |

## 3. No undefined behaviour, facts instead

C compilers get their optimisation power from undefined behaviour (`undef`, `poison`, signed overflow, aliasing
rules). Gabbro does not need it: the source checker and GabbroV *prove* what a C compiler *assumes*.

- **Every operation is total or traps.** Division by zero, a failed bound and a failed contract are explicit
  `trap k` terminators with the stop code of machine G. GIR has no `undef`, no `poison`, no `unreachable`.
- **Facts** are the optimiser's licence. A fact is a ghost annotation:

  | Fact | On | Typical source |
  |---|---|---|
  | range `lo ≤ v ≤ hi`, no wrap | a value | the checker's range analysis, `narrow` |
  | alignment, validity of an address | an address | region and table declarations |
  | non-aliasing of two accesses | a pair of accesses | region disjointness, ownership |
  | trip-count bound, measure | a loop | `decreases`, loop bounds |
  | purity, effect set | a call | `effects` clauses |
  | invariant | a region or table | proved invariants, user logic from GabbroV |

- **`FaktenGueltig P`** (a Lean `Prop`): every fact of `P` holds in every run of `P`. A program with a false fact
  is not ill-behaved, it is not well-formed; no pass may produce one.
- **Every pass preserves `FaktenGueltig`.** A pass that cannot keep a fact drops it. A pass that adds a fact
  proves it.

## 4. GIR

### 4.1 Values and types

| Type | Meaning |
|---|---|
| `iN` | bit vector of any width `N ≥ 1`; `i1` is the Boolean |
| `f32`, `f64` | native floats under `RootNativeFloat.Hardware` |
| `vK×T` | fixed vector of `K` lanes |
| `mK` | mask of `K` bits, one per lane |
| `v[vl]×T`, `m[vl]` | length-parametric vector and mask; `vl` is an explicit `iN` value |
| `addr⟨R⟩` | a byte offset inside the named region `R`; never a bare integer |
| tuple | several SSA results of one operation |

Wide integers are ordinary `iN`; cutting them into machine words is a pass, not a property of the IR.

### 4.2 Micro-operations

The primitives are small and orthogonal, chosen so that a real instruction is a *term* of several of them.

| Group | Operations |
|---|---|
| bits | `and`, `or`, `xor`, `not`, `shl`, `lshr`, `ashr`, `rotl`, `rotr`, `extract hi lo`, `concat`, `zext`, `sext` |
| arithmetic | `add`, `sub`, `mul`, `udiv`, `sdiv`, `urem`, `srem` at any width (division traps on zero) |
| comparison | `eq`, `ult`, `slt` returning `i1`; `select c a b` |
| float | `fadd`, `fsub`, `fmul`, `fdiv`, `fneg`, `fcmp`, conversions, `widen`, `narrow` |
| vector | lane-wise forms of all of the above under a mask and a length; `shuffle`, `broadcast`, `reduce` |
| memory | `load ty a`, `store a v`, each with region, alignment and access class |
| control | block parameters; `jump`, `branch`, `switch`, `call`, `tailcall`, `ret`, `trap k` |

GIR has **no flags, no registers, no addressing modes, no instruction mnemonics**:

- carry is bit `N` of an `N+1`-bit sum; `x86-64 adc` is "add three values at 65 bits, extract 64 and 1";
- a widening multiply is `mul` on the doubled type followed by two `extract`s;
- an addressing mode is an address computation followed by a `load`;
- `popcnt`, `clz`, `pdep` are terms over bits (a fold, a search, a scatter).

### 4.3 Graph, memory and events

- **Graph.** Functions of basic blocks with block parameters. A call carries its contract and effect summary, so
  inlining and interprocedural passes read what the checker read.
- **Memory.** Byte-addressed; endianness from the target profile; an address is the pair (space, byte) of the goal
  theorem's `speicherAdressen`. Memory is in SSA form **per region**: every access threads its region's memory
  token. Accesses to different regions are independent by construction and need no alias analysis.
- **Access classes.** `plain` (race-free by `RennfreiBis`, so sequential reasoning is valid), `atomic ord` (a
  barrier for reordering), `device` (never duplicated, removed or reordered), `stack`.
- **Observable events:** system calls, atomic and device accesses, stores into shared regions, traps, the function
  result. `Beh(P)` is the set of event traces of `P` over GX. Pure computation moves freely between events; a trap
  does not cross an event.
- **Cost.** Every function carries its bound from `ZeitAb`. A pass proves `cost(P') ≤ bound` in the abstract cost
  model, so the time guarantee survives optimisation.

## 5. Optimisation

**Rules proved, choice free.** A rewrite is a rule `pattern, condition, replacement`, and its soundness is one
theorem: an equation between two GIR terms under the condition. Which rule fires, where and in what order is
heuristic and needs no proof, because every step goes through the proved rule gate. Equality saturation over the
pure part of a region fits exactly: saturation and extraction are free, each rewrite is a proved equation.

| Class | What it relies on in GIR |
|---|---|
| inlining, specialisation, devirtualisation | calls with contracts and effect summaries |
| GVN, PRE, SCCP, LICM, strength reduction, dead-store elimination | SSA, per-region memory tokens, facts |
| loop unrolling, interchange, fusion, fission | trip-count and non-aliasing facts |
| loop and SLP vectorisation | vector, mask and length-parametric types |
| wide-integer and aggregate legalisation | `iN`, `extract`/`concat` |
| idiom formation (recognising a library cell in the graph) | cells are GIR terms, so recognition is matching |
| tiling, location assignment, scheduling, block layout | §6 |

## 6. Cells, tiling and locations

A **cell** is a GIR term pattern with typed holes: a small subgraph of micro-operations whose inputs and outputs
are *operand classes*. Cells are defined in GIR alone. Nothing in a cell names an architecture.

**Operand classes** (neutral): a location of a class (integer, vector, mask, float), a constant of a width class
(the widths are a parameter of the class, the table picks the ones it encodes), a memory operand (region, access
class, an address shape: base, base + constant, base + scaled index).

**The cell library** is one neutral list:

- **Base cells:** one per micro-operation and operand-class combination. They suffice to cut every GIR program
  into cells, so every target that has a row for each base cell can emit every program.
- **Idiom cells:** carry chain, multiply-high, multiply-add, rotate, count leading/trailing zeros, population
  count, bit deposit/extract, byte swap, CRC step, AES round, saturating arithmetic, compare-and-branch,
  compare-and-select, load-operate-store, block copy and fill, vector shuffle, masked load/store, gather/scatter,
  fused multiply-add, compare-and-swap.
- **Cell families:** a pattern with a size parameter (an `n`-limb carry chain, a `k`-byte copy) is one family.
  Statements about it are by induction on the parameter; its tests take the parameter at class boundaries.

**How the library grows.** When an architecture has an instruction worth using, one asks which neutral
computation it performs and adds that *computation* as a GIR term. The library grows by computations, never by
instructions: `pdep` enters as "bit deposit", any target with a matching instruction may use it, and on every
other target the cell is ordinary GIR that tiles into smaller cells.

**Tiling** cuts a program into library cells whose union is the program. Every tiling is correct, because a cell
*is* the subgraph it covers. Which tiling is chosen decides speed only.

**Locations.** Values that cross cell borders live in abstract locations `L0 … Ln` per class and in stack slots.
The counts come from the target table. Location assignment maps SSA values to locations; scheduling orders the
cells of a block. Both are passes over neutral data and are proved once for every table.

**Machine state never crosses a cell border.** Flags, partial results and implicit registers exist only inside a
row's bytes. Reusing them across two computations is possible only through a larger cell or family.

## 7. The target table

```
Target = { word, endian, locations : class → count, abi, features, memoryModel, rows : List Row }
Row    = { cell        : a library cell with its operand classes,
           constraints : tie(a, b) | fixed(a, location k) | clobbers(set) | scratch(count),
           bytes       : an encoding template: fixed bits and operand fields,
           features    : ISA extensions required,
           privilege, cost }
```

- A row says: "on this target, this cell with these operand classes is these bytes". The bytes may be one
  instruction, several, or a loop. GIR does not know and no proof looks inside.
- **`TargetOk T`** is decidable: every base cell has a row; every encoding template is a well-formed field
  layout; constraints name existing locations; `clobbers` and `scratch` stay inside the location counts.
- **Examples.** `x86-64 mul` is the row of "multiply at double width" with two `fixed` constraints. `adc` appears
  inside the row of the carry-chain family. `lea` is a row of an address-computation cell. AArch64 `madd` is the
  row of multiply-add; a target without it has no such row and tiles `mul` then `add`.
- **Features.** A row names the extensions it needs. A function compiled for a feature set carries the set as a
  requirement of its profile; multi-versioning is several variants and a dispatcher written in GIR.
- **ABI.** Calls, returns and system calls are cells whose rows carry `fixed` constraints from the checked ABI
  profile; nothing about a calling convention is in GIR.
- **Oracles and atomics.** `rdtsc`, `cpuid`, `rdrand` are rows of oracle cells under a named assumption, as
  `AxVertragO` at source level. `memoryModel` matters only for `atomic` cells: the table states which row
  implements which ordering.
- **Vendor neutrality.** A row may use only behaviour that every CPU of the architecture defines. M runs on
  several vendors for that reason.

**Adding an architecture** is: write the table, decide `TargetOk`, run M on its CPUs. No semantics, no pass and no
proof is added.

## 8. The generic theorems (Lean first)

| Name | Statement | Proved |
|---|---|---|
| `gir_sem` | the small-step semantics of GIR over GX, with `Beh` | definition, with witnesses |
| `lower_ok` | `Beh(lower S) = Beh(S)` for every accepted source program `S` | Lean, generic |
| pass theorems | `Beh(pass P) = Beh(P)`, `FaktenGueltig` preserved, cost bound kept | stated in Lean, proved with GabbroV on the Gabbro code |
| `tile_ok` | every tiling of `P` denotes `P` | Lean, generic |
| `assign_ok`, `schedule_ok` | location assignment and scheduling preserve `Beh` for every `T` with `TargetOk T`, respecting every row's constraints | GabbroV, generic in `T`, no per-compilation check |
| `encode_inj` | a well-formed field layout encodes injectively | Lean, generic |
| `emit_ok` | under `Hardware T`, the bytes of a tiled program behave as the program | Lean, generic in `T` |
| `m_vollstaendig` | M is complete for the emitter of `T` | Lean, generic in `T` |

Every theorem with a ∀-over-syntax premise gets its `_zeuge` on a non-degenerate fixture (AGENTS.md §12).

## 9. M and the hardware assumption

- **M is a set of GIR programs, the same for every architecture.** For each library cell it holds programs that
  exercise the cell at the boundaries of its operand classes and of its family parameter. A target runs the part
  of M whose cells have rows in its table.
- **Expected results** come from the GIR semantics in Lean, never from another compiler or CPU.
- **Complete** (`m_vollstaendig`): every row the emitter can use occurs in M in every operand class. The emitter
  only concatenates rows, so this covers every byte sequence a user binary can contain.
- **The emitter's shape contract** (a logic proof with GabbroV): the bytes of a tiled program are the
  concatenation of its rows' encodings, with branch targets as operand fields. It is the only place where a
  cell-wise shape is required, and the emitter has it by nature.
- **What M proves:** (a) the Gabbro emitter's bytes equal the Lean reference's on M, hence on every program;
  (b) every row was measured on silicon against its cell.
- **`Hardware T`, the one named assumption:** every row's bytes compute its cell for all operand values, touching
  only the locations its constraints declare, in any surrounding code. It speaks about cells in neutral GIR terms
  and contains no instruction semantics. M is its evidence, not its proof.
- **M grows with the tables, not with the optimisations.** A new pass needs a proof and no new test; a new row
  needs tests and no new proof.
- **N has no role here.** Refusals belong to the checker.

## 10. GabbroV in this route

- GabbroV derives, from the compiler's Gabbro source, the proof duties of every pass; the duties are Lean
  statements, so they use `gir_sem` directly as the specification.
- **Bootstrap.** The first GabbroV written in Gabbro is proved once in Lean (the initial Lean proof); afterwards
  GabbroV derives its own duties. Stage 0 compiles it.
- **Missing today:** the duty derivation in Lean. The printer was part of the Rust tool deleted on 2026-11-10; the
  five duty files the bridge imports are tracked inputs. A derivation computed in Lean from the source is the first
  work item of the GabbroV side.

## 11. What is hard

| Point | Why | What limits the damage |
|---|---|---|
| location assignment as a direct proof | the largest single pass proof | proved once, generic in the table |
| machine state across cells | flag or partial-result reuse needs a larger cell | idiom cells and families; measured against C before more are added |
| rule equations over bit vectors | `bv_decide` is on the guardian's forbidden list | hand proofs, or a reflective procedure with its own soundness theorem |
| long rows | a row whose bytes are a loop is a larger assumption than one instruction | long rows stay few; what short rows can build is built in GIR |
| vector and loop passes | invariants over memory | region tokens and facts keep them local; unmeasured until one is done |
| weak memory beyond DRF-SC | NOT CLAIMED in `Spec.lean` | `plain` accesses avoid it, `atomic` accesses are barriers |
| the 100 % target against `-O3` | every optimisation costs a proof | measure pass by pass; no speed claim before measurement |

## 12. Order of work

1. **Stage 0 complete** for the forms the sources of GabbroV and of the compiler use (the current work).
2. **Duty derivation in Lean**, then **GabbroV written in Gabbro** with its initial Lean proof.
3. **`gir_sem`** with witnesses; the base cells; `tile_ok`; `encode_inj`.
4. **`lower_ok`** for the fragment Stage 0 covers, then form by form.
5. **One small target table** and its `TargetOk`; the emitter with its shape contract; M for the base cells;
   `emit_ok` and `m_vollstaendig`; the first measured run on a CPU.
6. **One medium pass proved with GabbroV** (GVN with per-region memory) to measure what a pass proof costs. The
   plan for the remaining passes is written after this measurement, not before.
7. **Location assignment and scheduling**, generic in the table.
8. **Idiom cells and optimisation passes**, each chosen by a measurement against C.
9. **Further tables** (AArch64 first as the target direction, x86-64, RISC-V), length-parametric vector cells,
   privileged and boot cells.

Steps 3 to 5 have no proof by GabbroV and can start in Lean as soon as step 1 allows; steps 6 to 8 need step 2.
