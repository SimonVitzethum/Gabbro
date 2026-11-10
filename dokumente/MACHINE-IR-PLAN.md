# GIR: the IR of the full Gabbro compiler (design, 2026-11-10)

**Status: design for review. Nothing here is implemented.** It is the IR of the later compiler written in Gabbro,
not a change of Stage 0: `S0IR` stays the small interpreted IR of Stage 0 and its runner
([PLAN-SELF-HOSTING.md](PLAN-SELF-HOSTING.md) §2.1). Work on GIR starts after Stage 0 covers the forms the
compiler's own source uses.

**Fixed by the owner (2026-11-10).**
- No refinement and no translation validation. Nothing is checked per compilation and refused; every pass,
  register allocation and scheduling included, has a logic proof.
- Every optimisation is proved with GabbroV as user logic of the compiler. GabbroV is independent of M and N.
- M proves that the compiler emits correct machine code.
- Extreme optimisations on every CPU architecture, special instructions included.
- A GIR instruction does NOT correspond to one real instruction. GIR is one powerful, architecture-neutral IR that
  expresses nearly every real instruction by several of its own operations; real instructions are assigned to
  *cells* of GIR, and M is formed over the cells.
- An SSA IR is allowed (AGENTS.md §11 is changed accordingly). Length-parametric vectors are in the types from the
  start. Privileged and boot instructions use the same mechanism, later.

## 1. The shape in one table

| Stage | What it is | Who carries its correctness |
|---|---|---|
| source → **GIR** | lowering into neutral SSA micro-operations | lowering theorem (generic, Lean) |
| GIR → GIR | every optimisation | a GabbroV proof `Beh(pass P) = Beh(P)`, generic in the target table |
| GIR → **tiled GIR** | the same program, cut into cells and with locations assigned | GabbroV proofs, generic in the target table |
| tiled GIR → bytes | each cell replaced by the bytes its target table assigns | the emitter is cell-wise + M on the CPU |

There is one IR and one semantics. No stratum, no operation and no proof is specific to an architecture; an
architecture is a table of data (§5).

## 2. No undefined behaviour, facts instead

LLVM-style optimisation power comes from undefined behaviour (`undef`, `poison`, signed overflow, aliasing rules).
Gabbro does not need it: the source checker and GabbroV *prove* what C compilers *assume*.

- **Every operation is total or traps.** Division by zero, a failed bound and a failed contract are explicit
  `trap k` terminators with the stop code of machine G. There is no `undef`, no `poison`, no `unreachable`.
- **Facts** are the optimiser's licence: ghost annotations on a value, an access or a loop: range, no wrap,
  alignment, non-aliasing of two accesses, trip-count bound, purity of a call. A program is well-formed only if
  every fact holds in every run (`FaktenGueltig`, a Lean `Prop`).
- **Where facts come from:** the source certificate (`Akzeptiert`, ranges, `decreases`, region disjointness,
  ownership, race freedom from `RennfreiBis`, user logic from GabbroV) and proved analyses. A pass may use a fact
  and must preserve `FaktenGueltig`; a pass that cannot keep a fact drops it.

## 3. GIR

**Micro-operations.** The primitives are small and orthogonal, chosen so that a real instruction is a *term* of
several of them, never one of them: bit-vector arithmetic and logic at every width, `extract`/`concat`/`extend`,
shifts and rotates, `select`, comparisons that return `i1`, widening multiply as `mul` on a wider type,
carry as bit `N` of an `N+1`-bit sum, float operations (native, `RootNativeFloat.Hardware`), lane-wise vector
operations with masks and an explicit length, `load`/`store`. There are no flags, no registers and no addressing
modes in GIR: `x86-64 adc` is "add three values at 65 bits, extract sum and carry", an addressing mode is an
address computation, `popcnt` is a fold over bits.

**Values.** `iN` for every width, `f32`/`f64`, fixed vectors `vK×T`, mask vectors `mK`, length-parametric vectors
`v[vl]×T` with an explicit length value (SVE, RVV), SSA tuples. An address is `addr⟨R⟩`: a byte offset inside a
named region `R`, never a bare integer.

**Graph.** Functions of basic blocks with block parameters. Terminators: `jump`, `branch`, `switch`, `call`,
`tailcall`, `ret`, `trap k`. A call carries its contract and effect summary.

**Memory.** Byte-addressed, endianness from the target profile; an address is the pair (space, byte) of the goal
theorem's `speicherAdressen`. Memory is in SSA form *per region*: every access threads its region's memory token,
so accesses to different regions are independent by construction.

**Access classes.** `plain` (race-free by the goal theorem, sequential reasoning is valid), `atomic ord` (a barrier
for reordering), `device` (never duplicated, removed or reordered), `stack`.

**Observable events** are system calls, atomic and device accesses, stores into shared regions, traps and the
function result. `Beh(P)` is the set of event traces. Pure computation moves freely between events.

**Cost.** Every function carries its bound from `ZeitAb`; a pass proves `cost(P') ≤ bound`.

## 4. Cells: the architecture-neutral unit

A **cell** is a GIR term pattern with typed holes: a small subgraph of micro-operations whose inputs and outputs
are *operand classes* (a location, a constant of a width class, a memory operand of a region). Cells are defined in
GIR alone. Nothing in a cell names an architecture.

- **Base cells:** one cell per micro-operation and operand-class combination. They suffice to cut every GIR
  program into cells.
- **Idiom cells:** larger patterns kept in one neutral **cell library**: add-with-carry chain, multiply-high,
  multiply-add, rotate, count leading/trailing zeros, population count, bit deposit/extract, byte swap, CRC step,
  AES round, saturating arithmetic, compare-and-branch, compare-and-select, load-operate-store, block copy and
  fill, vector shuffle, masked load/store, fused multiply-add.
- **Where an idiom cell comes from:** whenever some architecture has an instruction worth using, one asks which
  neutral computation it performs and adds that computation to the library as a GIR term. The library grows by
  *computations*, never by instructions; `pdep` enters as "bit deposit", usable by any target that has it, and
  meaningful on every other target because it is ordinary GIR.
- **Cell families:** a pattern with a size parameter (an `n`-limb carry chain, a `k`-byte copy) is one family; its
  proof is by induction on the parameter, its tests take the parameter at its class boundaries.

**Tiling** cuts a GIR program into cells of the library such that the cells' union is the program. Any tiling is
correct: a cell *is* the subgraph it covers, so tiling changes nothing in the semantics. Which tiling is chosen is
heuristic and free; it decides speed only.

**Locations.** Values that cross cell borders live in abstract locations: `L0 … Ln` per class (integer, vector,
mask) and stack slots. Location assignment and scheduling are GIR → tiled-GIR passes over these abstract
locations.

## 5. The target table: all that is architecture-specific

```
Target = { word, endian, locations : class → count, abi, features, memoryModel,
           rows : List Row }
Row    = { cell        : a cell of the neutral library, with operand classes,
           constraints : tie(a, b) | fixed(a, location k) | clobbers(set) | scratch(count),
           bytes       : an encoding template: fixed bits and operand fields,
           features    : ISA extensions required, privilege, cost }
```

- A row says: "on this target, this cell with these operand classes is these bytes". The bytes may be one
  instruction, several, or a loop; GIR does not know.
- `TargetOk T` is a decidable predicate: every base cell has a row (so every program can be emitted), every
  encoding template is a well-formed field layout, constraints name existing locations.
- x86-64 `mul` is the row for "multiply at double width" with `fixed` constraints on two locations; `adc` appears
  inside the row of the carry-chain family; flags exist only inside a row's bytes and never between cells.
- A target without an idiom's instruction simply has no row for that cell; the tiler uses smaller cells there.
- Hardware oracles (`rdtsc`, `cpuid`, `rdrand`) are rows of oracle cells under a named assumption, as `AxVertragO`
  at source level. `memoryModel` matters only for `atomic` cells.

**Adding an architecture** is writing a table, deciding `TargetOk`, and running M on its CPUs. No semantics, no
pass and no proof is added.

## 6. The generic theorems (Lean first), each proved once for every target

1. **`gir_sem`**: the small-step semantics of GIR over GX.
2. **`lower_ok`**: source → GIR preserves behaviour, generic over programs.
3. **Pass theorems** `Beh(pass P) = Beh(P)`, `FaktenGueltig` preserved, cost bound kept: stated in Lean, proved
   with GabbroV for the Gabbro implementation. Optimisation rules are equations between GIR terms; which rule
   fires where is heuristic and free.
4. **`tile_ok`**: every tiling of a program denotes the program.
5. **`assign_ok`** and **`schedule_ok`**: location assignment and scheduling preserve behaviour for every table
   with `TargetOk`, respecting every row's constraints. Direct logic proofs, no per-compilation check.
6. **`emit_ok`**: under `Hardware T` (§7), the bytes emitted for a tiled program behave as the program.
7. **`encode_inj`**: a well-formed field layout encodes injectively, so operand values are recoverable from bytes.
8. **`m_vollstaendig`**: M is complete for the emitter (§7).

## 7. M over cells, and the one hardware assumption

- **The cells of M** are `row × operand-class boundary values`. M is a set of *GIR programs*, the same for every
  architecture: for each library cell, programs that exercise it at the boundaries of its operand classes and of
  its family parameter. A target runs the part of M whose cells have rows in its table.
- **Expected results** come from the GIR semantics in Lean, never from another compiler.
- **Complete** means: every row the emitter can use occurs in M in every operand class. Since the emitter only
  concatenates rows, this covers every byte sequence a user binary can contain.
- **What M proves:** the Gabbro emitter's bytes equal the Lean reference's on M, hence on every program (the
  emitter's shape contract is "bytes of a tiled program = concatenation of row bytes"); and every row was measured
  on silicon against its cell.
- **The named assumption `Hardware T`:** every row's bytes compute its cell for all operand values, touching only
  the locations its constraints declare, in any surrounding code. This is the whole hardware model: it speaks
  about cells in neutral GIR terms, it contains no instruction semantics, and M is its evidence. It must hold on
  all CPUs of the architecture, so M runs on several vendors.
- **M grows with the tables, not with the optimisations.**

## 8. What is hard

- **Location assignment** (register allocation) as a direct proof, generic in the table. It is the largest single
  pass proof, paid once for all architectures.
- **Cross-cell machine state.** Reusing flags or a partial result across two cells is only possible through a
  larger cell or family. Some hand-tuned sequences will need new idiom cells before the compiler finds them.
- **Rule equations over bit vectors:** `bv_decide` is on the guardian's forbidden list, so they are proved by hand
  or by a reflective procedure with its own soundness theorem.
- **`Hardware T` is per cell, not per instruction:** a row whose bytes are long (a block copy loop) is a larger
  assumption than a single instruction. Long rows should be few; what can be built from short rows is built in GIR.
- **Weak memory** beyond DRF-SC stays NOT CLAIMED as in `Spec.lean`.

**Recommended first step:** `gir_sem`, the base cells, one small table, and one medium pass (GVN with per-region
memory) proved with GabbroV, to measure what a pass proof costs before the other passes are planned.
