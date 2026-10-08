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

---

# Round 2 (checker and Lean follow-up, ordered by Simon 2026-10-07)

Per item: what was done, the probes, and the measured result. Tests: `cargo test -p gabbro-check
--no-fail-fast` (all collections), `REGISTER.txt` regenerated by the `zertifikate` test. The full
`cargo test` of the workspace (prover / `gabbro prove`), `pruefe-emission.sh`, the full `lake build`
and the guardians `pruefe-zahlen.py` / `pruefe-saetze.py` were NOT run (Sail generation held the
build slots; no warm Lean cache in this worktree). Counters that the guardians track (corpus size,
README figures, `MARKE_EMIT*`) are therefore not updated and must be re-measured by the merger.

## #17 M147: a selector does not taint the value (DONE, checker)

`let b = RING[e]; ENDE = ..; return b;` was refused as stale. Cause: `traeger_im_ausdruck` added
the carriers of the INDEX expression to the sources of the bound value, so a write to the
selector (`ENDE`) expired `b`, a snapshot of the cell that was selected. Now only the content
carrier taints; if the selector mentions an expired local the old behaviour stands. Example
`185-ringpuffer` (clean), gift `1404` (a write to `RING` itself still falls, once). Sentence
`m1.frische` extended. No Lean model exists for M147 (checker lint), so no Lean change.

## #15 / #14 static initialiser lists and bool literals (DONE, checker + parser; legacy C)

`static [mut] A : [T; N] = [e0, ...]` (nested rows too) parses (`parse.rs`) and is held by the
`konstanten.rs` pass exactly like a const table (`K191` length, `K194` element range, `N285/N286`
shape, every element a translation-time value). The emitter writes one initialised C array
(`.data`, no init code). Example `186-statische-tabelle`; gifts `1405` (`K194`), `1406` (`K191`).
`static mut X : bool = false;` emits (example `187-bool-statisch`; LEGACY C, 5 lines). Guarantee:
unchanged -- the initial values are range-checked like const elements, so M1's element range is
still true of the initial state. Lean: arrays have no `Glob` form in the exporter (`LG002`), so
no statement moves; example 186 stays UNCERTIFIED exactly like 122. Example 187 IS certified
(`G187_bool_statisch.lean`, generated; it uses the existing `bool` `Glob`) -- that generated
module was NOT built here, a `lake build` must confirm it.

## #16 whole-array copy (DONE, checker; legacy C)

`B = A;` and `M[i] = M[j];` are admitted when both sides are array places of the same length at
every depth with the same machine word (or `bool`) at the leaf and the source element range
inside the target's. Wider source range: new `N579` (sentence `m1.feldkopie_bereich`, gift `1407`).
Different length, compound operator or non-place source: `N287` unchanged (gifts `1408`, `951`,
tests in `nested_arrays.rs` updated to the different-length forms). Example `188-feld-kopie`.
LEGACY C: one `__builtin_memmove(target, source, sizeof(target))` (verified under
`cc -std=c11 -O2 -Wall -Wextra -Werror`). No new Lean form: arrays are outside the exporter.

## #13 strings in aggregates, #18 u32+u32, #19 find-first exit: NOT done, with the reason

* **Strings in tables/arrays/records (`N465`).** Soundness needs the per-cell length discipline:
  `N454` (index < len) and `N455` (copy fits) are decided from FLOW facts about a local; a cell
  in memory can be rewritten by another thread or call between the check and the use, so the
  facts die at every call/write (the M147 machinery). A sound design: a string cell is a
  `(len, bytes)` pair that is only ever read by first copying it into a local (`let s = T.slots[i].name`)
  and only written whole; then the checks apply to the local. That needs (a) a Lean `Val` form
  for a bounded string in `Ty` and the store model (today `Ty` has none, `LG002`), (b) the
  checker rule that a string place may appear only as the whole right side of a `let` or the
  whole left side of an assignment, (c) an exporter form. Not started: no Lean `Ty.str`.
* **`u32 + u32` without a wider type (`M104`).** The Lean model (`Zahl lo hi`) is exact
  arithmetic, so a sum assigned to a `u64` IS sound there; `M104` exists because the C backend
  computes in the operands' width. For the native path the rule can be relaxed: the sum's range
  `0 .. 2^33-2` is held against the CONTEXT type (return / `let` / assignment target) and the
  compiler widens the operands before adding. In C it needs an operand cast to the context width
  at every context. Not implemented: the context type is not threaded into `rechnung` (it is
  synthesised bottom-up), and with the C backend deprecated the change belongs with the native
  lowering. Sound, small, pending that threading.
* **Find-first exit from `traverse`.** `leave i` over the traverse binder is a parser/emitter
  change of ten lines, but it is NOT sound as a pure addition: the exporter's `traverse` form
  (`lean_g.rs`, `by unvisited`) and the `touches` / completeness reasoning assume the walk visits
  every element; after an early exit "all slots were processed" is false. The G model needs a
  `Block.traverseExit` former whose invariant is "visited prefix", and every pass that concludes
  completeness after a traverse must be made to ask whether the body can leave. Not started.

## How `Darstellung` enters the native layout lowering

`Speichermodell/Darstellung.lean` is range-generic. The lowering of a declared `Ty` to storage is
then three lookups, none program-specific:
1. cell width of `Ty.int lo hi`  = `schmalBytes lo hi` (bits `bits lo hi`); `Ty.bool` = `bits 0 1`;
   `Ty.opt n` = `bits 0 n` (the sentinel is `n`); `Ty.grund n` = `bits 0 (n-1)`;
2. store: encode with `enc lo v`, load with `dec lo n`; the correctness obligation of every load
   and store is `dec_enc` / `enc_lt_two_pow` (the checker's M1 range IS the premise);
3. packed arrays/fields: `packBytes` for the size and `feld`/`setze` for access, with
   `feld_setze` (read what you wrote) and `setze_niedrig`/`setze_hoch` (neighbours intact) as the
   per-access lemmas the AArch64 `ubfx`/`bfi` sequences are validated against.
The existing `tyFits` (`CSpeicher.lean`) is the same statement for the C cell; the native
`tyFits'` is `bits lo hi <= 8 * cellbytes`, proved from `zellBytes_fits`. A bridging file
`DarstellungTy.lean` over `Ty`/`encW` is the next step; it was not written because it imports
`CSpeicher` and no Lean build was possible in this round.

---

# Tracking (dated; status per finding)

## 2026-10-08 -- #19 find-first exit from `traverse`: DONE

`leave i;` / `next i;` over a `traverse` binder (`by unvisited`): `schleifen.rs` pushes the binder
as a label; `by consuming` falls as `N580` (gift `1413`, sentence `schleifen.traverse_ausgang`).
The Lean model already had `Stmt.leave`/`Stmt.next` and `traverseLauf` (invariant checked at the
exit); the exporter (`lean_g.rs`) now writes them for the INNERMOST binder at the end of a block
(`LG004` otherwise). Example `190-erster-treffer` is CERTIFIED: `./lean-bau` 734 jobs, 0 errors,
module `G190_erster_treffer` built. `cargo test -p gabbro-syntax -p gabbro-check`: 67 collections,
0 failures (three tests that pinned `S001` for the binder were rewritten). The C emitter registers
no label for a `traverse` and refuses the exit by name (`C001`); nothing new there.

## Status of every finding (rows 1-20 of this report)

| # | Finding | Status |
|---|---|---|
| 1-9, 12 | minimal-width / packed layout of ranged ints, bools, index cells, tags, records | Lean model DONE (`Speichermodell/Darstellung.lean`, merged); `DarstellungTy.lean` over `Ty`/`encW` DONE (agent 03, reviewed and built here: `tyBits`, `encN_lt`, `decN_encN`, `narrow_fits`, `narrow_le_wide`, packed `getCell_setCell`/`getCell_setCell_ne`, `packBytes_cells`; standard axioms); record field ordering DONE (`RecordLage.lean`, agent 03, reviewed and built: `lage_ge_summe`, `absteigend_ohne_luecke`, `absteigend_minimal` over permutations, `offset_ausgerichtet`, the 24/16/10 witnesses of finding 8; standard axioms); native lowering OPEN (compiler work) |
| 10, 11 | string length word | C change not taken (C deprecated); native size theorem is part of the string design |
| 13 | strings in tables / arrays / records | **DONE for table slot fields (2026-10-08)**: Lean `ZeichenfolgeZelle.lean` (copy-out/copy-in round trip, other cells untouched, loaded string fits, native cell never above the C layout; standard axioms), checker rule `N581` (a slot field `string max N` is read whole into a local and written whole; any other mention falls), example 191 (UNCERTIFIED `LG002`, no exporter string form), gifts 1414-1416, gift 1163 re-aimed at a record field (still `N465`). Static one-dimensional string arrays `[string max N; K]` are cells too (agent 05, example 192, gifts 1418-1421; `= 0` is the only initialiser). Record fields, nested arrays, consts, pointer targets stay `N465`: OPEN |
| 14 | `static mut X : bool = false` | DONE (legacy C emit, example 187) |
| 15 | static array initialiser list | DONE (parser + `konstanten.rs`, example 186, gifts 1405/1406) |
| 16 | whole-array copy | DONE (`N579`, example 188, gifts 1407/1408) |
| 17 | M147 selector taint | DONE (example 185, gift 1404) |
| 18 | `u32 + u32` in the context width | DONE (2026-10-08, agent 05, reviewed and integrated): `+ - *` as the whole value of a `let x : T`, `return`, plain `=` or direct call argument computes in `T`'s width when `T` is non-wrapping, no operand is wider than `T` or of another signedness class (literals fit any width); `u32 + u32` into `u32` stays `M104` (gift 1409), no context stays `M104` (1410), a range that does not fit `T` is `M101` (1411), mixed signedness unchanged (1412); example 189 (UNCERTIFIED `LG003`: the assignment target has no G form), gift 583 flipped to silent like the lane-191 flips, sentence `m1.breiter_kontext`, nine `rechenwerk` tests, legacy C emitter mirrors it. Lean: the model's `Zahl lo hi` arithmetic is exact, so no model change |
| 19 | find-first exit | DONE (above) |
| 20 | runtime bound check on `u8` reads | NOT A COST (cc removes it; measured noise) |

## The two earlier gap reports and `gabbro zeremonie` (rows, 2026-10-08)

| Row | Finding | Status |
|---|---|---|
| G1 | no type parameters / generics | BLOCKED: language decision (`Ty` is deliberately non-recursive, OFFEN O15); needs Simon |
| G2 | record as a value has no `Ty` (`LG002`) | BLOCKED: priced and refused 2026-09-15 (0 of 113 corpus programs gain); needs a `Ty.prod` decision |
| G3 | `traverse` early exit | DONE (#19) |
| G4 | windowed `traverse from s count n` | OPEN: `P001`; parser, bounds, effects and Lean window arms |
| G5 | `option` over ordinary types | OPEN: language design (index-only today) |
| G6 | `count` as a predicate | OPEN: invariant language (`D021`) |
| G7 | strings in aggregates | BLOCKED, awaiting Simon (#13) |
| G8 | byte pointers have no G form (O37) | OPEN |
| G9 | `Endblock` binders (`let x = f()`, return under `locks`) | OPEN: named model decisions (O14/O15/O27) |
| G10 | `bool` static | DONE (#14) |
| G11 | payload hand-off after `awaits` (O25c) | OPEN: proof work, no weakening |
| G12 | dense 256-way dispatch | Lean soundness of the jump table (`Sprungtafel.lean`) IN PROGRESS (agent 03); the lowering itself belongs to the native compiler |
| R/C/P/U rows | RAM / compute / proof-time / ugly rows of the Lean report | covered above where they overlap (strings, bool static, traverse exit); rest OPEN |
| E1, E2 | ceremony | `gabbro zeremonie --table`: A1-A4 (annotation equal to what the signature or declaration says; an effect entry a callee already declares) and R1-R4 (duplicates) MAY FALL; T1-T10 (effects, costs, requires/ensures, maintains, invariants, loop bounds, touches, reserved, register class) MAY NOT. Making derivable clauses optional is a language decision (PLAN-EINFACHHEIT); no clause was made optional this round. OPEN, needs Simon |
| U1 | `type Q(T) = ...` parses and means a ghost parameter | DONE (2026-10-08): `N582` (gift 1417, sentence `namen.typ_parameterliste`); `linear` witnesses keep their list |

Decisions needed from Simon: strings in aggregates; generics; records as values; making derivable
ceremony optional; `option` over ordinary types.
