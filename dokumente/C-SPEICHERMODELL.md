# The C memory model — measured inventory and design (plan step 1)

*Written 2026-09-13. This is step 1 of `PLAN-UEBERSETZUNGSVALIDIERUNG.md` §3: the memory
model is decided before any of the hard C forms gets a semantics. The Lean core is
`grammatik/Grammatik/CSpeicher.lean`; it supersedes the memory of `CSemantik.lean`
(lane 128) and carries lane 128's results over as a refinement.*

## 0. The decision in five lines

1. **Block-offset memory in the style of CompCert, restricted to what the emitter creates.**
   One block per C object. A pointer is a block plus an offset. Pointer arithmetic moves the
   offset and never the block, and that is the whole provenance rule.
2. **Typed cells, not bytes.** Each block has a layout taken from the emitter's own
   declarations: `count` records of scalar fields at byte offsets. A load or store must hit a
   cell of exactly its type (the C11 effective-type rule). That is enough because the emitter
   never reinterprets ordinary memory (measured, §2).
3. **UB means stuck.** Every access checks block, lifetime, kind, bounds and cell type. The
   inventory (`AccUB`, `PtrUB`, `LoadUB`, `StoreUB`, `OrdUB`) is complete for the check
   (`accOk_iff`).
4. **A separate observation trace.** Volatile device accesses, atomic operations with their
   memory order, and port I/O append events to the trace. A volatile read takes its value
   from an environment oracle. This is the handle for relating machine G later.
5. **No `malloc`, no bytes, no unions (yet), no weak memory.** Each of these is named in the
   CUTS, together with the extension that would lift it.

## 1. What was measured

**Method.** `/home/simon/Dokumente/Gabbro/target/debug/gabbro emit` was run once per
versioned `.gab` file. That is single runs of an already built binary, with no `cargo`
involved. Units that exit 0 with non-empty output count as emitting, which is the census's
criterion (`zaehle-c-formen.py: korpus()`). The output was lexed with the census's own lexer
(`entkommentiere`, `lies_tokens`, `zaehle`: comments and literals removed first), and then
classified with patterns over the comment-free code. The scratch scripts are not part of
the tree.

**Denominator.** 227 of 924 versioned `.gab` files emit, giving 15,199 lines of C.

**Staleness, named.** The binary dates from 2026-09-11 17:58. `crates/` has commits after
that (lanes E4–E7, 2026-09-12/13). As a result, **arena storage** (`emit.rs` line 3697,
`static A_arena A_arena_speicher;`) does **not** appear in this measurement; it is read off
the emitter source. A fresh binary moves the counts, not the kinds.

### 1a. The C objects the emitter creates

| C object (emitted shape) | sites | units | block in the model |
|---|---:|---:|---|
| table type `typedef struct { T_slot slots[N]; } T;` | 114 | 98 | layout `RecLay` (count N) |
| table storage `static T T_speicher;` (table addressed by name) | 26 | 21 | `CBlk.tab t`, plain |
| table behind `T *restrict t` (parameter) | 225 params | — | the same `CBlk.tab t` |
| file-scope scalar `static uintN_t g __attribute__((unused)) = …;` | 124 | 65 | `CBlk.glob g`, plain, 1 cell |
| file-scope `_Atomic T g;` | 74 | 36 | `CBlk.glob g`, atomic, 1 cell |
| per-core atomic cells `static _Atomic T g_zellen[NKERNE];` | 8 | 4 | `CBlk.glob g`, atomic, N cells |
| file-scope array `static uintN_t a[N] = {0};` | 4 | 4 | `CBlk.glob g`, plain, N cells |
| file-scope struct `static S s = { … };` | 4 | 3 | `CBlk.glob g`, record |
| `static const uintN_t c … section(".rodata")` | 4 | 4 | `CBlk.ro c`, read-only |
| arena storage `static A_arena A_arena_speicher;` (`buf[hi]`, `used`) | 0 (binary predates E4) | — | `CBlk.arena a` |
| stack scalar locals | 826 | — | environment (no address taken) |
| stack struct locals (`Dma g = (Dma){ … };`, `ObjektArt_marke m;`) | 109 | — | environment or `CBlk.stk` if address-taken |
| stack locals whose address is taken (`&e`, `&n`, `&k`, `&v`) | 61 sites | — | `CBlk.stk fr x` |
| CAS expected locals `&_cxN` | 26 call lines | — | `CBlk.stk fr x` |
| stack arrays (`uint8_t bytes[KAP]`, scalar arrays) | 12 | — | `CBlk.stk fr x` |
| pointer-typed locals (`const Pte *it = &k->eintraege[…]`) | 10 | — | a `ptr` value |
| device handle type `typedef struct { volatile uint8_t *basis; } D;` | 47 | 43 | a record with one `ptr` cell |
| device handle from an integer `(volatile uint8_t *)(uintptr_t)BASE` | 9 | 5 | `devHandle` → `CBlk.dev d` |
| byte view `typedef struct { uint8_t *bytes; uint32_t len; } V;` | 28 | 18 | a record `{ptr, u32}` into a byte block |
| foreign function returning `T *` (`Region * belegen(uint64_t)`) | 7 | 5 | `CBlk.ext n` (foreign provenance) |
| traversal callbacks `bool (*knoten_zu)(uint64_t, const N **)` | 12 | 7 | `CBlk.ext n` |
| const function pointers `static void (*const w)(void) = f;` | 30 | 18 | not memory (a named function) |
| null object pointer `(Platz *)(uintptr_t)0` | 1 | 1 | **stuck**, see §6 |

**There is no heap.** No `malloc`, `free`, `calloc`, `realloc` or `alloca` occurs. Arenas
are static arrays. The six-plus-one block kinds of `CBlk` cover every row: `tab`, `glob`,
`arena`, `ro`, `stk`, `dev`, and `ext` for foreign objects.

### 1b. Pointer shapes, and what they compute

| shape | sites | what it computes | model primitive |
|---|---:|---|---|
| `t->slots[i].f` | 263 | table block, `i·sizeof(T_slot) + offsetof(f)` | `slotAt` / `EmitLay.slotPtr` |
| `T_speicher.slots[i].f` | 60 | the same, by name | same |
| `->` overall | 944 | 284 `->slots[`, 142 `->basis`, 421 `->bytes`, 39 `->len`, others | load of a `ptr` cell + offset |
| **pointer arithmetic** (census `zeigerarithmetik`) | **598** | 419 `v->bytes + K` (byte-view field offset), 155 `d->basis + K` (device register offset), 22 `p + 4` inside `gabbro_le64`, **2 misclassified** by the census (`m->a + m->b`, `e += 1`: integer arithmetic on a name declared as a pointer elsewhere in the unit) | `ptrAdd` (element size 1) |
| **index on a pointer** (census `index auf zeiger`) | **192** | 182 `p[i]` in the byte helpers (`gabbro_le32` etc.), 10 `index[e]` on `const uint32_t *index` in tree descents | `ptrAdd` + load |
| **dereference** (census `dereferenz *`) | **227** | 153 `*(volatile uintN_t *)(…)` register cells, 32 stores through out-parameters `*p = v`, **42 misclassified** (function-pointer declarators `(*const name)` counted as dereference) | `vLoad`/`vStore`; `bStore` via a `ptr` |
| **address-of** (census `adresse &`) | **199** | 107 `&A` as operand of `atomic_*_explicit`, 26 `&A, &_cxN` in compare-exchange, 61 `&x` of a whole local (out-parameters, method receivers), 5 `&k->eintraege[…]` | `addrOf`, `slotAt` |
| pointer → integer `(uint16_t)(d->basis + K)` | 12 | port number for `inb`/`outb` | `portOf` |
| pointer casts | 163 | 153 `(volatile uintN_t *)` on a `volatile uint8_t *` device base (the register cells), 9 `(volatile uint8_t *)(uintptr_t)`, 1 `(Platz *)(uintptr_t)0`. **None on ordinary memory.** | typed MMIO cell; `devHandle` |

**Why typed cells suffice** comes out of the last row. Every pointer cast in the emitted C
either targets a device window, which is not memory in the model because its accesses are
observations, or it is the null constant, which is stuck. The byte views read `uint8_t`
cells only; endianness is composed in C arithmetic (`(uint32_t)p[3] << 24 | …`), not by
reinterpreting a buffer. So no emitted access reads a cell at a type other than the one it
was written with. The model then needs no byte encoding. If the emitter ever reads a
`uint32_t` through a `uint8_t` buffer, the model must get CompCert's byte fragments, and
the census should ratchet exactly this row.

### 1c. Volatile and atomic accesses

| | sites | units |
|---|---:|---:|
| volatile register cells `*(volatile uintN_t *)(base + off)` | 153 (w8 26, w16 18, w32 81, w64 28) | 29 |
| `atomic_load_explicit` | 61 | 34 |
| `atomic_store_explicit` | 46 | 34 |
| `atomic_compare_exchange_weak_explicit` | 7 | 4 |
| `atomic_compare_exchange_strong_explicit` | 6 | 5 |
| `atomic_exchange`, `atomic_fetch_*`, `atomic_thread_fence` | 0 | 0 |
| `memory_order_*` tokens: relaxed / acquire / release / seq_cst | 48 / 44 / 75 / 6 | — |
| `__asm__ __volatile__` blocks: 14 port I/O (6 `inb`, 8 `outb`), 2 `mfence`, 1 `sfence`, 1 `invlpg`, 1 syscall stub | 19 | 6 |

Every atomic access goes through an explicit `atomic_*_explicit` call. None is a plain
access to an `_Atomic` object, so the model makes a plain access to an atomic block stuck
(`plain_on_atomic_stuck`). This rule restricts the subset; it is not a C rule.

## 2. The model (Lean: `CSpeicher.lean` §1–§10)

```
CTy   := int (sgn : Bool) (w : CWidth) | ptr                    -- cell types
CBlk  := tab t | glob g | arena a | ro c | stk fr x | dev d | ext n
CPtr  := { blk : CBlk, off : Int }                              -- Int so that leaving is representable
CVal  := int v | ptr p | undef
RecLay := { count, nf, fty : Nat → CTy, off : Nat → Nat, ssize } -- count records of nf fields
BKind := plain | readonly | atomic | mmio
BlkLay := { lay : RecLay, kind : BKind, base : Nat }
CLayout := CBlk → Option BlkLay                                 -- from the emitter's declarations
CSt   := { mem : CBlk → Nat → CVal, live : CBlk → Bool, obs : List CObs }
CObs  := vrd p τ v | vwr p τ v | ard p o v | awr p o v | acas p os of seen des ok | pin n v | pout n v
```

**The access check** (`accOk L st p τ md`): the block exists, it is alive, its kind admits
the mode (`rd`/`wr` on plain, `rd` on read-only, `atom` on atomic, `vol` on MMIO), the
offset is non-negative, and `lay.cell off = some τ`. `cell o` is the field whose offset is
`o mod ssize`, inside `count · ssize`. Padding, the middle of a field, one past the end and
a type mismatch all give `none`.

**The UB inventory**, each item stuck (`*_stuck`), with the check complete (`accOk_iff`):

| constructor | C11 | `BEWEIS.md` §2 row |
|---|---|---|
| `AccUB.noBlock` | pointer derived from no object | 2 |
| `AccUB.dead` | lifetime ended, dangling (6.2.4p2) | new (stack frames) |
| `AccUB.mode` | plain access to `_Atomic`/MMIO, store to `const` (6.7.3p6) | new |
| `AccUB.negOff`, `AccUB.pastEnd` | outside the object (6.5.6p8, J.2) | 2 |
| `AccUB.noCell` | effective type / misalignment (6.5p7, 6.3.2.3p7) | 5 |
| `LoadUB.uninit` | uninitialised automatic object (6.7.9p10) | 8 |
| `StoreUB.range` | value outside the declared type (the emitter's range guarantee) | 1 |
| `PtrUB.below`, `PtrUB.above` | arithmetic leaves `[0, size]` (6.5.6p8) | 2 |
| `OrdUB.load`, `OrdUB.store`, `OrdUB.casFail` | forbidden memory orders (7.17.7) | new |

Lane 128's operator inventory (`ABinUB`, rows 1, 3 and 4) is unchanged. It is reused.

**Operations:** `bLoad`, `bStore` (plain); `ptrAdd` (arithmetic, with provenance
`ptrAdd_blk` and composition `ptrAdd_add`); `addrOf`, `enterFrame`, `leaveFrame` (stack);
`vLoad`, `vStore` (volatile, observation, oracle `DevOrc`); `aLoad`, `aStore`, `aCas`
(atomic, observation carrying the order); `devHandle` (integer → device pointer, only at the
declared base); `portOf`, `portIn`, `portOut` (port I/O).

**Layouts from the emitter.** `natLay count fields` is the x86-64 SysV rule: natural
alignment and tail padding to the strictest field. `RecLay.wf` (fields fit, are aligned and
do not overlap) is a `Bool`, so a certificate's layout is checked by `decide` per program.
From `wf` follow `RecLay.pos_inj` (a byte position is one record and one field) and
`RecLay.cell_pos` (the emitted address of a field is a cell of the field's type). For
`Konto`, `kontoLay_werte` computes offset 0, `sizeof(Konto_slot) = 4` and
`sizeof(Konto) = 8`.

## 3. The refinement of lane 128 (`CSpeicher.lean` §11)

The five forms keep their syntax (`CExpr`, `CStmt`) and get a second semantics `bEval`/
`bExec` on `CSt`. A slot read or store is a typed load or store at `slotAt TL t k f`, which
is block `tab t`, offset `k·ssize + off f`. The old memory is a **projection**:

```
projMem TL st t k f := if k < count ∧ f < nf then (st.mem (tab t) (k·ssize + off f)).toInt else 0

bEval_refines : (∀ t, (TL t).wf) → e.fieldsOk TL → Good TL st →
    bEval TL e st ρ = aEval e (projMem TL st) ρ (geomOf TL)
bExec_refines : (∀ t, (TL t).wf) → s.okB TL → Good TL st →
    RelOut TL (bExec TL s st ρ fuel) (cExec s (projMem TL st) ρ (geomOf TL) fuel)
```

`RelOut` means that both runs are stuck, or both finish with `projMem` of the new state
equal to the old state, the same environment, and a good state. The refinement therefore
runs in both directions: stuck for stuck. It holds for every statement of the five forms,
including loops (`forRun_refines`). `Good` says that tables are alive and their cells hold
integers. `okB` says that every store names its field's declared C type, which is what the
emitter writes.

`cCorr_assignSlot_blk` is **derived from** `cCorr_assignSlot`. The block correspondence
projects to lane 128's (`corrMemB_proj`), the old theorem gives the old step, the
refinement gives the new step, and the projection comes back (`corrMemB_of_proj`). The
geometry is lane 128's own: `refTL_geom : geomOf refTL = cGeomRef`.

## 4. Correspondence to Gabbro's memory (`CSpeicher.lean` §12)

`EmitLay D` is the emitter's layout of a declaration, given **as data** together with the
facts a certificate carries:

- table → block number (injective) and record layout (well-formed, `count = D.count t`);
- field → position in `T_slot` (in range, injective), with a C type that holds the Gabbro
  type (`tyFits`);
- global → block number (injective), one cell whose type fits, `_Atomic` exactly when the
  global is `atomic`.

`encW` is the value encoding: numbers, `0`/`1`, the index or the sentinel `N` (`T_NONE`),
and the case number.

```
corrW EL σ st :=
  (∀ t, ¬ghost t → live (tab (tnr t)) ∧ ∀ k f, 0 ≤ k < count t →
      st.mem (tab (tnr t)) (k·ssize + off (fnr t f)) = int (encW (σ.slots t k f)))
  ∧ (∀ g, ¬ghost g → live (glob (gnr g)) ∧ st.mem (glob (gnr g)) 0 = int (encW (σ.globs g)))

corr_schreibSlot : corrW EL σ st → ¬ghost t → 0 ≤ k < count t →
  ∃ st', bStore EL.lay st (EL.slotPtr t k f) (EL.slotTy t f) (int (encW v)) = some st'
       ∧ corrW EL (σ.schreibSlot t Λ k f v) st' ∧ st'.obs = st.obs
corr_leseSlot    : … → bLoad EL.lay st (EL.slotPtr t k f) (EL.slotTy t f) = some (int (encW (σ.slots t k f)))
corr_schreibGlob / corr_leseGlob                  (plain globals)
corr_schreibGlob_atomar / corr_leseGlob_atomar    (atomic globals: same memory effect, one observation with the order)
corrW_lese       : corrW EL (σ.lese Λ orte) st ↔ corrW EL σ st
```

This generalises lane 128's single theorem to every table, field and global of every
declaration that has an `EmitLay`. The emitted store cannot get stuck: the range follows
from `encW_fits`, the cell from `RecLay.cell_pos`.

**The witness** is `refKonto_zeuge`, on `refD` (`beispiele/104-referenz.gab`). `refEL` is
the emitted layout (`Konto` is block 0, `stand` is field 0 at `uint32_t`), with every
certificate fact discharged by `decide` or `rfl`. On the reached run's pre-write world
(`refM1B`, thread 1), the Gabbro store `konto[0] := 100` and the emitted store at offset 0
reach related states. The emitted load then reads 100, and memory moved from 0 to 100 on
both sides. As in lane 128, `einzahlen` writes `konto` and `refSchrittB` fires exactly this
write. `refEL_adressen` pins `k->slots[0].stand` at offset 0 and `k->slots[1].stand` at
offset 4.

**Two hard forms, expressed end to end** (§14). `geraet_zeuge` covers the device access:
integer → pointer at the declared base, a pointer stored in and loaded back from
`d.basis`, `+ 8` inside the window, a volatile store that is exactly one observation and
changes no memory, `+ 17` stuck, and a 32-bit access at offset 2 stuck. `ausgabe_zeuge`
covers the out-parameter: a fresh local is uninitialised, `*p = 7` through `p = &e` makes
`e` read 7, and after `leaveFrame` the pointer dangles.

## 5. The forms against the model

The task names 64 forms, from `BEWEIS.md` §1a (2026-08-31: 34 allowed and used, 30 used
but not allowed). The census tool's current marks are `MARKE_TABELLE = 67` and
`MARKE_UNERLAUBT = 32`. This lane's measurement with the 2026-09-11 binary finds **65**
(35 + 30). `unary -` came back to life; `void*` (1) and the comma operator (4) appear;
`while` and `__typeof__` do not appear. The table below covers the union of all of these.

**Memory role.** "—" means the form has no memory role: it belongs to the statement or
expression semantics of plan step 2. "cells", "pointer" and "trace" name the model feature
that expresses the form. **NOT** means the core does not express it.

| group | form | memory role |
|---|---|---|
| preprocessor | `#include`, `#define`, constant `#define`, `#if` on `__GNUC__`, `#endif`, `#else`, `#elif`, `#if` from `when` | — (before semantics) |
| declarations | `static` | cells: static blocks are always alive |
| | `extern` | — (foreign prototypes; foreign objects are `ext` blocks) |
| | struct definition | cells: `RecLay` (with padding) |
| | **union definition** | **NOT**: overlapping fields (see CUTS) |
| | `typedef`, `enum` | — |
| types | `uintN_t`, `intN_t`, `bool`, `_Bool`, `true`/`false` | cells: `CTy.int` (`bool` as `uint8_t`) |
| | pointer type `T*` | pointer: `CTy.ptr`, `CVal.ptr` |
| | array type `T[N]` | cells: `RecLay.count` |
| | `struct` | cells: `RecLay` |
| | **`union`** | **NOT** |
| | `void` | — |
| | **`void*`** (1 site, the foreign `write(int32_t, const void *, uint64_t)`) | **NOT**: a pointer handed to foreign code, whose memory effect is assumption A_n |
| | **`float`, `double`** | **NOT** in the core: no floating cell type (a one-constructor extension, `CTy.fl`) |
| statements | assignment | cells: `bStore` for memory lvalues |
| | `if`/`else`, `switch`/`case`, `for`, `while`, `break`, `continue`, `return` | — |
| | `goto`, label | — (continuations; memory-independent) |
| | call | pointer: frames `enterFrame`/`leaveFrame`; parameter passing is step 2 |
| expressions | literal, identifier, unary `!` `-` `~`, `&&`/`||`, `?:`, comma, `++`/`--`, compound assignment | — (a compound assignment on a volatile cell is two observations) |
| | field access `.` | cells: offset in `RecLay` |
| | field access `->` | pointer: load a `ptr` cell, then offset |
| | index `[]` | cells: `slotAt`, with the index bound |
| | **pointer arithmetic** | pointer: `ptrAdd` (provenance, bounds) |
| | **index on a pointer** | pointer: `ptrAdd` + load |
| | **address-of `&`** | pointer: `addrOf`, `slotAt` |
| | **dereference `*`** | pointer: `bLoad`/`bStore` through a `ptr`; trace for volatile |
| | cast | — for integers; pointer: `(volatile uintN_t *)` is a typed MMIO cell, `(T *)(uintptr_t)a` is `devHandle` (a non-device address is stuck) |
| | `sizeof` | cells: `RecLay.size`, `CTy.size` |
| other | **`volatile`** | trace: `vLoad`/`vStore` |
| | **`_Atomic`** | cells + trace: atomic blocks, `aLoad`/`aStore`/`aCas` |
| | **`memory_order_*`** | trace: `COrd`, with `OrdUB` |
| | `asm` operands, `asm` | trace for port I/O (`portIn`/`portOut`); **NOT** for `mfence`/`sfence`/`invlpg`/`syscall` (opaque) |
| | `register` (syscall register variables) | **NOT** (part of the opaque syscall stub) |
| | `restrict`, `__builtin_unreachable` | — (proof exports, not semantics) |
| | `const`, `inline`, `__attribute__`, `_Noreturn`, `_Static_assert`, `__typeof__` | — (`const` objects are read-only blocks) |

**The hard forms the plan names are pointer arithmetic, dereference, address-of,
`volatile`, `_Atomic`, ordering and `goto`.** The model expresses all of them except
`goto`, which is a control form: its semantics needs continuations and no memory.

**What the core does not express** is seven forms: `union` definitions and `union` types
(tagged unions, 29 definitions), `float`/`double`, `void*` (foreign), the opaque `asm`
bodies, and `register` (syscall). Each needs a small extension (§7), or it stays an
assumption. Aggregate *values* (by-value struct locals, compound literals, struct returns)
are not a form but a gap in `CEnv`; step 2 closes it.

## 6. Findings

1. **A null pointer is dereferenced in the emitted C.** `beispiele/38-unveraenderlicher-zeiger.gab`
   declares `static tz : ptr<normal, rw> Platz = 0;` and writes `tz.slots[i].a = 5`. It
   emits `static Platz * const tz = (Platz *)(uintptr_t)0;` and then `tz->slots[i].a = 5;`,
   which is C UB (6.5.3.2p4) on every call of `setz`. The checker admits it, and Gabbro's
   model cannot see it, because a `ptr` value is `Unit` there, a capability without an
   address. In this model the access is stuck: `0` is no object's address. This is reported
   here, not fixed; `crates/` was not touched.
   **Status 2026-09-13 (lane 145): fixed at the checker, `crates/` touched.**
   `(T *)(uintptr_t)0` is still a null pointer constant (C11 6.3.2.3p3), so no
   emitter spelling can cure it -- UBSan fires on the unrepaired emission
   (`member access within null pointer`). `N260` refuses an immutable pointer
   starting at `0`; `beispiele/38` binds its pointer to declared storage
   instead, and the corpus sweep (239 emitting units) holds zero
   `(uintptr_t)0`. Remainder: a `static mut` pointer starting at `0` still
   lowers to a null spelling (the kernel NULL-init idiom; flow, not a
   declaration).
2. **`BEWEIS.md` §2 row 5 is false as written.** It says no cast between pointer types is
   ever emitted. The emitter writes 153 casts from `volatile uint8_t *` to
   `volatile uintN_t *`. They are harmless for strict aliasing, because they target MMIO
   and not memory, but the sentence has to say that.
3. **The census over-counts two forms.** `dereferenz *` counts function-pointer declarators
   `(*const name)` as dereferences (42 of 227). `zeigerarithmetik` counts integer
   arithmetic on names declared as pointers elsewhere in the unit (2 of 598). Both are
   lexer approximations of the kind the tool's own `UNGEMESSEN` section names. The class is
   right; the counts are high.
4. **All 598 pointer-arithmetic sites compute inside one object.** Every site is
   `base + constant` or `base + i·stride + constant`, on a byte view, a device window or a
   byte helper. None leaves its block by construction of the layouts. The model states this
   as `ptrAdd` progress under the layout bound; per-site discharge is step 2.

## 7. The extensions the CUTS name, sized

| extension | why | size (Lean lines, estimate) |
|---|---|---:|
| union cells: admissible types per offset, effective type recorded at the store | tagged unions (29 definitions) | 300–400 |
| aggregate values in the environment (struct locals, compound literals, returns) | 109 struct locals | 600–900 |
| `CTy.fl` floating cells | `f32`/`f64` fields | 150 |
| fresh frame numbers threaded by the call semantics | frames revive after re-entry | 200 |
| foreign calls as observations with a frame assumption (A_n) | `extern`, `void*`, callbacks | 300–500 |
| the observation trace ↔ machine G (A10, interleavings) | concurrency | 2,000+ (outside T4) |

## 8. The estimate for plan step 2 (T4 passes i–iii) on this model

**What this lane measured.** Opus, one session: 1,966 lines, 69 theorems, green.
- The memory core (§1–§10) is about 870 lines.
- The refinement is about 480 lines.
- The correspondence is about 365 lines.
- The witnesses are about 180 lines.

The expensive parts turned out to be the position arithmetic (`pos_inj`, `cell_pos`) and
the dependent `storeSlot` cases. Both are now done once, as lemmas, for every layout.

| pass | plan (mid) | on this model | why |
|---|---:|---:|---|
| (i) 15 near-neighbour forms | 1,500 | 1,200–1,800 | They barely touch memory. The five base forms already run on the new memory, so there is no rebasing. |
| (ii) 20 medium forms | 5,000 | 3,000–4,000 | Struct layout with padding is done (`natLay`, `RecLay.wf`), and `sizeof` is `RecLay.size`. What remains is conditional evaluation (`?:`, `&&`/`||`), conversions and the declaration forms. |
| (iii) 24 hard forms | 10,000 | 6,000–8,000 | Load, store, pointer arithmetic, address-of, frames, volatile, atomics and the UB inventory exist. Per form there remains statement-level wiring plus a correspondence lemma (200–300 lines), plus the extensions of §7 without the machine-G row (about 1,500–2,000), plus `goto` continuations (about 800). |
| **Σ** | **16,500** | **≈ 10,000–14,000** | |

**The risk that stays** is on the Gabbro side of each correspondence lemma, not the C
side. Every Gabbro statement form brings its dependent-typed `execStmt` case, and lane 128
measured that tax. The rates above are an Opus agent's; for Muse lanes, apply the plan's
§4 rework factor.
