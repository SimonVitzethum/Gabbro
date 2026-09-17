# Storage census: emitted layouts vs Rust (lane 238)

Method: exact emission spellings read off `crates/gabbro-check/src/emit.rs`
(read-only for this lane), compiled with gcc 13 `-std=c11 -O0` on x86_64
Linux, against handwritten `#[repr(C)]` Rust equivalents compiled with
rustc 1.97.1 `-O`. Every pair below was built and run; sizes, alignments
and field offsets are measured, not derived. The scratch probes lived in
`.tmp/census_size.{c,rs}` and were removed after the run so the tree stays
clean; the Rust reference source is reproduced verbatim in §5 so lanes 239
and 244 can re-run it.

Reference inputs: `beispiele/140-atomic-array-counter.gab` (S4),
`beispiele/124-two-threads-private.gab` (S1 shape: one-`u32` slot,
`count 2`), `beispiele/120-tagged-construction.gab` (S8:
`Nachricht = { Leer, Kurz(u32), Lang(u64) }`), `laufzeit/start.c`
(fixed runtime cost).

## 1. Per-shape table (bytes on x86_64)

| # | Shape (Gabbro → emitted C) | Emitted | Rust `repr(C)` equiv | Delta | Cause of delta |
|---|---|---|---|---|---|
| S1 | `table T count 2 { stand: u32 }` → `T_slot{uint32_t}; T{slots[2]}; static T T_speicher;` | 8, al 4 | `struct Konto{slots:[KontoSlot;2]}` 8, al 4 | 0 | — |
| S2a | record slot `{ art: u8, stand: u32 }`, count 4 | slot 8 (art@0, stand@4), table 32, al 4 | identical, incl. offsets | 0 | 3 B mid-padding inherent to both layouts |
| S2b | record slot `{ stand: u32, art: u8 }`, count 4 | slot 8 (stand@0, art@4), table 32, al 4 | identical, incl. offsets | 0 | 3 B tail-padding inherent to both layouts |
| S3 | `atomic G : u32` → `static _Atomic uint32_t G;` | 4, al 4 | `AtomicU32` 4, al 4 | 0 | — |
| S4 | `atomic REGEL : [u32; 256]` → `static _Atomic uint32_t REGEL[256];` | 1024, al 4 | `[AtomicU32; 256]` 1024, al 4 | 0 | — |
| S5a | `arena A … of u32`, hi 16 → `{ uint32_t buf[16]; uint32_t used; }` | 68, al 4 | identical | 0 | `used` counter = 4 B payload, 0 pad here |
| S5b | arena of `u8`, hi 10 → `{ uint8_t buf[10]; uint32_t used; }` | 16, al 4 (buf@0, used@12) | identical, incl. offsets | 0 | `used` forces 2 B mid-padding after `buf` in both |
| S6 | `linear type T;` (token) → `{ uint8_t nichts; }` | 1, al 1 | `struct Token(u8)` 1 / `()` 0 | +1 vs `()` | C has no addressable zero-sized type; the byte exists so the value can be passed and addressed, nothing ever reads it (emit.rs:1979) |
| S7 | `linear ghost type T;` → erased, nothing emitted | 0 | `()` 0 | 0 | erasure is total: no type, no value, no zeroing |
| S8 | `tagged type Nachricht` → `{ Nachricht_marke marke; union { uint32_t Kurz; uint64_t Lang; } last; }` | 16, al 8 (marke@0, last@8) | `struct{marke:u32,last:union{kurz:u32,lang:u64}}` 16, al 8 | 0 | 4 B marke→last padding inherent to both; payload-free variants add no union (no empty union in C) |
| S9 | `const K : [u32; 4]` → `static const uint32_t K[4]` | 16, al 4 | `[u32; 4]` 16 | 0 | lives in rodata, same bytes |
| S10a | mmio/dma device handle → `{ volatile uint8_t *basis; }` | 8, al 8 | `struct{basis:*mut u8}` 8 | 0 | qualifier is access form, not storage |
| S10b | port device handle → `{ uint16_t basis; }` | 2, al 2 | `struct{basis:u16}` 2 | 0 | — |
| S11 | `accumulates m … per cpu 4` → `static _Atomic uint32_t m_zellen[4];` | 16, al 4 | `[AtomicU32; 4]` 16 | 0 | one cell per core, no fold state |
| S12a | slot with nested field `bytes : [u8; 6]` → `{ uint8_t bytes[6]; uint32_t len; }`, count 3 | slot 12, table 36, al 4 | identical | 0 | 2 B mid-padding inherent to both |
| S12b | format handle → `{ uint8_t *bytes; uint32_t len; }` | 16, al 8 | identical | 0 | 4 B tail-padding inherent to both |
| S13 | `option index into T` → `uint32_t` | 4, al 4 | `u32` 4 | 0 | sentinel is `count N` itself: `None` costs 0 bytes |

Per-table runtime overhead in the emitted unit: **0 bytes**. A used table
emits exactly its storage struct plus the `T_NONE` define (0 bytes); there
is no `used` counter, no lock word, no vtable in the unit. (Arenas are the
only carrier with a counter: S5.)

## 2. Fixed runtime cost (`laufzeit/start.c`, hosted POSIX, x86_64 glibc)

| Object | Bytes | Scales with |
|---|---|---|
| `pthread_mutex_t sperre_L` (+ `L_nimm`/`L_gib` code) | 40 data | per declared lock |
| `pthread_t faden[N_WURZELN]` (main stack) | 8 | per declared root |
| thread stack (default `ulimit -s` 8192 KiB virtual; resident only touched pages) | 8 MiB virtual | per declared root |
| idle root `ruhe()` | 0 data (code only, never spawned on hosted) | — |
| emitted `__attribute__((unused))` decls (unused prototypes, `T_NONE`) | 0 (no object code, no storage) | — |

Fixed-cost total for a unit with L locks and R roots:
**40·L + 8·R bytes data** (plus R thread stacks at 8 MiB virtual each).
Example `beispiele/124` (L=1, R=2): 40 + 16 = **56 B data** + 2 stacks.

## 3. Top-3 overhead causes, ranked by bytes

1. **Lock object, 40 B per lock** — the `pthread_mutex_t` in `start.c`.
   Not in the emitted unit at all (the unit only declares `void L_nimm(void);`);
   orientation only: Rust `Mutex<()>` measures 8 B / al 4 (futex-based std,
   different implementation, not an equivalent).
2. **Arena `used` counter, 4 B per arena + up to 3 B alignment padding**
   (measured: S5a +4/+0, S5b +4/+2) — the only per-carrier counter the
   emitter writes; tables have none.
3. **Linear token, 1 B per live token value vs a Rust ZST (`()`, 0 B)** —
   deliberate: C needs one addressable byte; a `linear ghost type` is
   instead fully erased (S7, 0 B).

Everything else in §1 deltas at exactly 0: padding in records, tagged
unions, nested array fields and format handles is layout-inherent and
byte-identical between the emitted C and `repr(C)` Rust.

## 4. Budget statement for lanes 244 and 239

- Enforceable per-shape byte budgets are the "Emitted" column of §1;
  any layout change that moves one of those numbers breaks this census.
- Fixed-cost budget: 40 B data per lock, 8 B data per root, no per-table
  overhead in the emitted unit.
- Non-budgets (identical on both sides, listed for completeness): C enum
  marke = `u32` 4 B; `const` tables = plain arrays in rodata; `volatile`
  on mmio/dma handles costs nothing.

## 5. Rust reference source (scratch, re-runnable)

```rust
use std::mem::{align_of, size_of};
use std::sync::atomic::AtomicU32;
#[repr(C)] struct KontoSlot { stand: u32 }
#[repr(C)] struct Konto { slots: [KontoSlot; 2] }
#[repr(C)] struct RecSlot { art: u8, stand: u32 }
#[repr(C)] struct Rec { slots: [RecSlot; 4] }
#[repr(C)] struct Rec2Slot { stand: u32, art: u8 }
#[repr(C)] struct Rec2 { slots: [Rec2Slot; 4] }
#[repr(C)] struct ArenaA { buf: [u32; 16], used: u32 }
#[repr(C)] struct ArenaB { buf: [u8; 10], used: u32 }
#[repr(C)] struct Token(u8);
#[repr(C)] struct Nachricht { marke: u32, last: NachrichtLast }
#[repr(C)] union NachrichtLast { kurz: u32, lang: u64 }
#[repr(C)] struct Com1 { basis: *mut u8 }
#[repr(C)] struct Port1 { basis: u16 }
#[repr(C)] struct PktSlot { bytes: [u8; 6], len: u32 }
#[repr(C)] struct Pkt { slots: [PktSlot; 3] }
#[repr(C)] struct DtbKopf { bytes: *mut u8, len: u32 }
// + size_of/align_of/offset_of! prints per shape; ghost () = 0 B;
// orientation only: size_of::<std::sync::Mutex<()>>() = 8, al 4.
```

Cuts: no `gabbro emit` run was used (shapes read off emit.rs spellings,
which is what the budget enforces); measurements are x86_64 Linux only
(arm/aarch64 alignment of `_Atomic u64`/`double` may differ — S8's al-8
row is the one to re-measure there); thread-stack figure is the process
`ulimit -s` default (8192 KiB), not a per-unit constant.
