# Language audit: what is RAM-heavy, CPU-heavy, ugly, laborious or unwritable

Date: 2026-10-07. Author: Sonnet agent E. Branch: `worktree-agent-a09e960b6d6567175`.
Builds on the two earlier reports (`SPRACHLUECKEN-REPORT.md`, `SPRACHLUECKEN-LEAN-REPORT.md`, whose
Part B rows R1-R4 said "bytes not measured"); this file MEASURES them.

**Scope note (coordinator, 2026-10-07).** The emitted C backend is DEPRECATED; the planned path is
the AArch64 native compiler with translation validation. The "C bytes" column below is therefore
*evidence of what the language semantics implies* (the sizes come from `gabbro emit` + `sizeof`
with gcc on x86-64, probes in `.claude/muse-arbeit/kratz/sonnetE/p1..p7.gab`, not committed). The
"native AArch64" column is an EXPECTATION for a direct compiler, NOT a measurement; no AArch64
compiler exists yet. Everything under "C" fixes is marked LEGACY.

Method: each row names the source, the number measured on emitted C, and what a direct compiler
would need. `u8 in 0 .. 3` etc. are checker-proved ranges (M1), so the representation only has to
hold the range, not the declared word.

## Findings (measured)

| # | Construct (source) | C bytes measured | Native AArch64 expectation (not measured) | Why | Proposed fix | Guarantee touched | Effort |
|---|---|---|---|---|---|---|---|
| 1 | `static mut A : [u32 in 0 .. 3; 1000]` | 4000 (`[u8 in 0..3;1000]` = 1000; `[u2;1000]` = 1000) | 1000 B byte cells (`ldrb`/`strb`, 1 instr); 250 B packed 2-bit (`ldrb`+`ubfx`, 2-3 instr) | the cell is the DECLARED word (`ctyp` of the carrier); the range is a checker-only fact (`emit.rs` "W6") | native layout = `Darstellung.bits`/`schmalBytes` of the range, offset-encoded; **Lean theorem done** (`Speichermodell/Darstellung.lean`) | none (M1 already proves the range; `dec_enc`) | Lean done; native lowering = compiler work |
| 2 | table slot field `f : u32 in 0 .. 3` | slot of `{bool, u32, u8, u8, u16, bool, tagged}` = 24 B x 1000 = 24 000 | slot sorted + ranges narrowed: 1+1+1+1+2+1+tag(1)+4 payload = 12 B, 12 000 per 1000 | same as 1, plus no field reordering | same; reorder is free for a record that crosses no FFI | none | as 1 |
| 3 | `[[u32 in 0 .. 1; 64]; 64]` | 16 384 | 4096 (byte) / 512 (1 bit/cell, `packBytes 4096 1`) | declared word again | as 1, packed: `packBytes_le_zellen` | none | as 1 |
| 4 | `[bool; 4096]` | 4096 (1 byte per bit) | 512 B packed (`ldrb`+`ubfx`/`tbz`, 2 instr per test; `strb` read-modify-write per set) | `bool` = `bool` byte; no bit-vector type | packed layout of `bool` arrays is `bits 0 1 = 1`; set/get proved by `feld_setze`/`setze_niedrig`/`setze_hoch` | none (the write only touches its bit: `setze_niedrig/hoch`) | Lean done |
| 5 | `index into Q` / `option index into Q` cell, count 256 | 4 B each; `Q_slot` = 16 B (naechster, vorher, phase tag, grund) | count 256: `vorher` 1 B, `option` needs the sentinel 256 -> 2 B; slot 5 B (6 aligned) | the index lowers to `uint32_t` (`ctyp` `Index`) | `bits 0 (N-1)` for the index, `bits 0 N` for the option (sentinel `N`); tyFits generic already in `CSpeicher.lean` | none | native lowering |
| 6 | `tagged type Kl = { K0..K3 }` | 4 B (C `enum`) | 1 B (2 bits) | C enum tag | `bits 0 (cases-1)` | none | native lowering |
| 7 | `tagged type Gem = { Leer, Klein(u8), Gross(u64) }` | 16 B (4 tag + 4 pad + 8) | 16 B naturally aligned, 9 B only unaligned/packed | union alignment | native: tag byte + payload sized by the largest case, aligned only when the payload needs it | none | native lowering |
| 8 | `type Mix = { a : u8, b : u64, c : u8 }` vs same fields sorted | 24 B vs 16 B (`Sortiert`) | 16 B if the compiler orders by alignment | fields keep source order | reorder by decreasing alignment unless the record crosses an FFI/`format`/`device` boundary (needs an explicit layout marker) | none for pure records; ABI for FFI records | small, but needs the marker |
| 9 | `type Paar = { x : u32 in 0..3, y : u32 in 0..3, z : bool }` | 12 B | 1 B packed (5 bits) or 3 B bytes | declared words | as 1-2 | none | as 1 |
| 10 | `string max 5` value | 12 B (`uint32_t len` + 5 + pad) **LEGACY FIX done: 6 B** | 1 B len + 5 = 6 B (`max <= 255`); 2 B len above | length word was always 32 bit | length word = `zellBytes (bits 0 max)`; Lean `CString` carries `len : Nat`, no width | none | C part trivial (done); native = layout |
| 11 | `string max 100` | 104 B | 101 B (-3) | same | same | none | same |
| 12 | `static KOPF : u32 in 0 ..< 256` | 4 B | 1 B | declared word | as 1 (scalar: negligible) | none | none worth doing |
| 13 | `string` in a table slot, array, record, static | refused `N465` | cannot be written | "length flow facts cannot reach aggregates" | a length-carrying string cell with the length in the same word; checker rule needs the same flow facts per cell | would need the N454/N455 rules extended per cell, no weakening | large (checker + Lean) |
| 14 | `static mut X : bool = false;` | `C001 "non-constant initialiser"` for a literal: UNWRITABLE (workaround `u32` flag, 4 B) | n/a | emitter had no `true`/`false` arm | **LEGACY C fix done** (`static bool X = false;`); native compiler: trivial constant | none | done in C |
| 15 | `static mut TAB : [u32; 4] = [1,2,3,4];` | `P011` (only `= 0`); const tables only | unwritable | grammar has no mutable-static initialiser list | allow an initialiser list for `static mut` arrays (data section); exporter has no array `Glob` (LG002) so no Lean statement moves, but the program stays UNCERTIFIED | none | medium (parser + checker + native data section) |
| 16 | `B = A;` whole-array copy | `N287` refusal; element loop, N iterations | one `ldp/stp` sequence or memcpy call | C has no array assign | add a checked `copy A to B` primitive with equal static lengths (no failure case) | none (extents equal by type) | medium (checker + Lean store model) |
| 17 | `RING pop: let b = RING[e]; ENDE = ...; return b;` | `M147 "b may be stale here"` although only `ENDE` is written (reproduced twice, `p7.gab`) | n/a (checker) | M147 invalidates a value read through `RING[e]` when any carrier it indexed through is written | workaround: `return RING[e]` after the write; refine M147 to name the carrier it actually staled (RING) | none (the rule is sound, too coarse) | small-medium (checker) |
| 18 | `u32 + u32` | `M104` / `M101` (range `0 .. 8 589 934 590`) | n/a | no overflow semantics by design | ergonomic: a sugar `a + b` widening to `u64` in a `let` is already possible; a hint could name the widest type | none | doc only |
| 19 | traverse find-first | S001: no exit (`leave i`) | whole walk per query | known, SPRACHLUECKEN row 3 | labelled traverse | none | medium |
| 20 | runtime bound check on `u8` array reads | `((uint64_t)(i) < N ? A[i] : trap)` emitted although the checker proved `i < N` (byte-carrier "second opinion", `lese_bytes`) | none (checked statically) | the emitter discharges only when `ausdruck_obergrenze` reads the C type, not the range | none for native; in C a `u32 in 0..<N` index is not recognised | none | not a cost: `cc -O2` removes it. Measured 300 000 x 4096 reads: 6.06 s checked vs 6.26 s unchecked, 4.79 s vs 4.46 s on the second run = noise |

Not measured (the model/no program exists): AArch64 instruction counts above are expectations from the
layout alone (`ldrb`+`ubfx` for a packed bit field, one `ldrb` for a byte cell). They should be
re-measured when the native backend exists.

Items already known and out of scope: unbounded dynamic structures; generics (SPRACHLUECKEN row 1);
records as values in the Lean model (row 2).

## What was fixed

1. **Lean (the representation semantics, the important part):**
   `grammatik/Grammatik/Speichermodell/Darstellung.lean`, imported by `Grammatik.lean`. Over every
   `Int` range, nothing program-specific: `bits lo hi` (bits of the offset encoding), `enc`/`dec`
   with `dec_enc`/`enc_dec`/`enc_lt_two_pow` (every value fits), `bits_minimal` (nothing narrower
   holds the range), `zellBytes`/`schmalBytes`/`schmal_le_wort` (the narrow cell never costs more
   than the declared word), packed fields `feld`/`setze` with `feld_pack`, `feld_setze` (a write is
   read back exactly), `setze_niedrig`/`setze_hoch` (neighbouring bits untouched), `packBytes` with
   `packBytes_le_zellen`, and `decide` examples with the numbers of this audit (`[u2;1000]` = 250 B,
   `[bool;4096]` = 512 B, `[[u32 in 0..1;64];64]` = 512 B). Checked: file compiles with
   `lean` 4.33.1 standalone; `#print axioms` of five key theorems: `propext`, `Quot.sound` only; no
   `sorry`/`axiom`/`native_decide` (`pruefe-kein-sorry.py`: 0 violations). `lean-layout.py --check`
   passes. **NOT run:** the full `lake build` (no warm cache in this worktree, memory), so
   `gabbro_ziel` was not re-printed; the file imports nothing and nothing imports it, so the goal
   theorem cannot move.
2. **LEGACY C, two trivial emitter fixes** (`crates/gabbro-check/src/emit.rs`, marked legacy, no Lean
   correspondence required by the new rule):
   * `static mut X : bool = false|true;` now emits `static bool X = false;` (before: `C001`).
   * the string length word is the narrowest unsigned type for `max`: `gabbro_string_5` 12 -> 6 B
     (`uint8_t len`); `lenof` reads `((uint32_t)s.len)` so surrounding arithmetic is unchanged.
   Verified: emitted `beispiele/161-zeichenkette.gab` and the bool probe compile with
   `cc -std=c11 -O2 -Wall -Wextra -Werror`. **NOT run:** `pruefe-emission.sh` (the background run
   produced no output), `cargo test`; the `saetze.rs` sentence text was updated to the new layout.

## What remains (proposals, ordered by value/risk)

* Native layout lowering using `Darstellung` (rows 1-9, 12): compiler work; the theorem side exists.
* Checker: a column-aware `M147` (row 17); a `static mut` initialiser list (row 15); a `copy` primitive
  (row 16); strings inside aggregates (row 13) - these need checker rules and Lean store models.
* Do NOT change the C widths of table slots/arrays (rows 1-9): the two chain instances `kette_104`
  and `kette_108` pin `uint32_t` cells in Lean text (`Korrespondenz104`), and the C backend is legacy.
