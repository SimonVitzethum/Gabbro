# Open language decisions: one brief per item (2026-10-08, Sonnet U)

Each brief: what it is, a concrete before/after, the options with cost (Lean model, checker,
guarantee impact, effort) and a recommendation. Evidence: `messung/SPRACHE-EFFIZIENZ.md`.
"Lean groundwork" means a standalone, built file already exists; the language form is what needs
the decision. Effort is for one focused agent-week at most: S = days, M = 1-2 weeks, L = longer.

## 1. Generics (type parameters)
**What.** One ring buffer / queue / copy per element type is written by hand; `type Queue(T) = ...`
parses but means nothing (now `N582`).
**Before.** `type RingU32 = { kopf : u32, ende : u32, ... }` plus a copy of every function for
`RingU8`, `RingPkt`. **After.** `type Ring<T> = { ... }; fn push<T>(r : ptr<normal,rw> Ring<T>, x : T)`.
**Options.** (a) Do nothing; a generator that writes the monomorphised copies with a byte-identity
guard (S, no language change, no model change). (b) Generics by monomorphisation at check time:
the checker instantiates a generic item per use and checks each instance as ordinary code (Lean
model: none, the exporter sees only instances; checker M-L; guarantees unchanged because every
instance is checked in full). (c) True parametric types in `Ty` (recursive `Ty`; Lean change L,
touches every proof over `Ty`, OFFEN O15).
**Recommend (b)** if the stack's libraries (ring, queue, copy, sort) are wanted; otherwise (a).
Never (c) before the native compiler exists.

## 2. Records as values (`Ty.prod`)
**What.** A record cannot be a function result or a plain value in the Lean model (`LG002`); programs
use out-pointers and stay UNCERTIFIED when a record is returned.
**Before.** `fn lies(k : ptr<normal,r> Konto, i : index into Konto, out : ptr<normal,w> Eintrag)`.
**After.** `fn lies(k : ptr<normal,r> Konto, i : index into Konto) -> Eintrag`.
**Options.** (a) Keep out-pointers (no work; costs one indirection and certification). (b) Add
`Ty.prod (List Ty)` with `Val` = tuple, field read/write, `Block.bind` of a record, and the C
and native correspondence (Lean L: every `Ty` match in the model grows an arm; checker S; guarantees
unchanged, a record value is a copy). (c) Only records of scalars (flat product, no nesting): Lean M.
**Recommend (c)** first: it covers completion values (`Completion{id,len}`), the one shape the
reports measured, with a cheap `tyFits`/layout story (`RecordLage.lean` already orders fields).
Measured payoff of (b)/(c) on the 113-program corpus in 2026-09: 0 programs; the gain is for new code.

## 3. Optional derivable ceremony (A1-A4, R1-R4 of `gabbro zeremonie --table`)
**What.** The calibration says these MAY fall: A1-A3 a `let` annotation equal to what the callee,
place or name already declares; A4 an effect entry a callee already declares; R1-R4 duplicates
(effect twice, `requires`/`ensures` twice, a `requires` repeating a parameter range).
**Before.** `let n : u32 = lies(k, i);` and `effects { reads k.slots, reads k.slots, locks K }`.
**After.** `let n = lies(k, i);` and `effects { reads k.slots, locks K }`, or the effects list omitted.
**Options.** (a) Keep as is: unannotated `let` already works; the rest is style (0). (b) Make R1-R4
a hint, then a refusal "redundant" (checker S; no guarantee impact, it removes text only). (c) Derive
the whole `effects` clause (lane-191 derivations exist for settled-empty cases; `gabbro pruefe --fix`
writes it): checker M, Lean none, guarantee unchanged ONLY if the derived list is what the body does.
`ensures` is never derived (PLAN-EINFACHHEIT). **Recommend (b) now, (c) for `effects` of leaf
functions**; keep T1-T10 (costs, requires/ensures, maintains, loop bounds, touches) as written.

## 4. Grammar for `option <range type>`
**What.** `option index into T` exists; `option u32` does not parse. Lean groundwork:
`OptBereich.lean` (sentinel = one past the range; free when the range does not fill its power of two).
**Before.** `tagged type Bytes_Opt = { Nichts, Etwas(Bytes) }` + a match per use (10 lines each).
**After.** `static mut frei_min : option Bytes = none;` ... `match frei_min { some(b) => ..., none => ... }`.
**Options.** (a) Keep the hand-written tagged sum (0). (b) Sugar for the tagged sum: parser +
checker desugar, Lean none (S). (c) A first-class `Ty.opt` over ranges lowered with the sentinel:
Lean M (generalise `Ty.opt n`, reuse `OptBereich`), checker M, 1 extra bit at most (often 0).
**Recommend (b)** now; (c) when the native lowering needs the sentinel for density.

## 5. Windowed `traverse ... from s count n`
**What.** Walk a window of a table; needed for hold chunking (never hold a lock for a whole table)
and windowed scans. Today `P001`. Lean groundwork: `Fenster.lean` (chunking lemma, early exit).
**Before.** `retry` with a hand-threaded index and a `narrow` per access.
**After.** `traverse i over slots of t from s count 8 by unvisited { ... }` with `requires s + 8 <= count`.
**Options.** (a) Keep `retry` (0). (b) Parser + a checker bound rule (`s + n <= count`, `N`-code) +
exporter/G window arm + cost per window (Lean M: a `Stmt.traverseFenster` former whose semantics is
`lauf` over `indizes s n`; guarantees unchanged, bounds are checked once at entry instead of per access).
**Recommend (b)**; it is the one change that makes lock-hold chunking expressible, and the Lean
part is mostly the existing `traverseLauf` with a different index list.

## 6. `count` inside invariants
**What.** `count k in slots of T : p` is a value in code but not in `invariant`/`spec fn` (`D021`), so
"refcount equals the number of slots pointing at it" is a comment next to a hand counter.
Lean groundwork: `Zaehlen.lean` (`zaehle_schreibe`, `refcount_erhalten`: the update law).
**Before.** `-- refcount == number of slots with ziel == t` and a manual loop variable.
**After.** `invariant refcount_ok : forall t in slots of Obj : Obj.slots[t].rc == count k in slots of Tab : Tab.slots[k].ziel == t;`
**Options.** (a) Keep comments (0). (b) Allow `count` in predicates, same-table only (cross-table is a
`group` invariant, SYNTAX:554): checker M (domain binder resolution), Lean M (a counting `Pred` form
over a finite domain, with `zaehle_schreibe` as the maintenance lemma). **Recommend (b)** in that
restricted form; the maintenance proof obligation then becomes mechanical for one-slot writers.

## 7. Strings in record fields, nested arrays, consts, pointer targets
**What.** Slot fields and static 1-D arrays are string cells (`N581`, done). The rest is `N465`.
**Before.** `type Eintrag = { name : string max 8 }` refused. **After.** accepted, read/written whole.
**Options.** (a) Stop here (0): slots and static arrays cover tables and name registries. (b) Record
fields: a record VALUE copy is whole-in/whole-out already, but a record reached through a pointer is a
cell too: needs the cell rule on `p->name` (checker M; Lean: the `Zellen` model per record field is
the same lemma). (c) Nested arrays `[[string max N; K]; J]`: same as one cell per element, checker S.
(d) `const` strings: a literal table of text is safe (immutable); needs a constant-fold of lengths (S).
(e) Pointer targets (`ptr<..> string max N`): a pointer to a cell, aliasing again (M, riskiest).
**Recommend (c) and (d)** (cheap, safe); (b) with records-as-values (item 2); not (e).

## 8. `~` elements in static initialiser lists
**What.** `static mut A : [u32 in 0 .. 255; 4] = [~1, 1, 2, 3];` passes the checker (the folder cannot
fold `~` without a width) and only the legacy C emitter refuses it.
**Before/After.** Today accepted by the checker, later `C001`. After: either `K190` or folded per width.
**Options.** (a) Refuse `~` in a list element (`K190`, S, one line, no guarantee impact: the element
range cannot be verified, so refusing is the sound choice). (b) Teach the folder the width of the
element type (`~x = 2^w - 1 - x`): checker S, Lean none. **Recommend (b)** with (a) as the fallback;
it is the same `~` the user already writes elsewhere (`u32::max` is the all-ones spelling today).

## 9. Endblock binders (`let x = f();` / `return` under `locks` at the top level)
**What.** `Endblock` has no binder for a call result, so the tail-let of a call and a return under
`locks` at a body's top level stay UNCERTIFIED (`beispiele/21`, `98`, `99`, `110`, `125`).
**Before.** Restructure so the `let` sits inside a nested block. **After.** `let x = f(); return x + 1;`
certified.
**Options.** (a) Restructure by hand (small cost per site). (b) Add `Endblock.bindCall` and a locks-return
form to G: Lean L (a new former, machine rules, `RestHalt` arms in `Spec.lean`, a reviewed Spec diff,
SATZKARTE section), exporter M, no checker change; guarantees unchanged but the goal theorem's proof
moves (`gabbro_ziel` must be re-closed). It is the highest-leverage single certification change
(O15 measured 21/98/99 plus every top-level tail-let). **Recommend (b)** as an Opus-level task, after the
GabbroV bridge, because it touches the goal statement's proof.

## 10. Byte pointers (O37)
**What.** `ptr<normal, r> u8` has no G form, so byte-level programs (region answers, packet parsing)
run but cannot be certified (`LG003`/`LG002`, example 183).
**Before.** Parsing code is UNCERTIFIED. **After.** `buf[i]` through a `ptr<..> u8` with the extent clause
certified.
**Options.** (a) Leave it uncertified (the guarantees still hold by the checker; only the Lean chain is
missing). (b) Model a byte region as `Tab` with `count = extent` and a `u8` field, bridging pointer
indexing (`N571`) to slot access: Lean M-L (a region form: fresh, disjoint, extent from the gate's
`ensures`), exporter M. The pointer-index hole (O36, `N571`) is already closed at the checker.
**Recommend (b)**, after item 9; it unlocks the network stack's certification.

## 11. Payload hand-off after `awaits` (O25c)
**What.** Publish a flag, `awaits` it, then read a PLAIN payload: refused today (`N485` reserved, no
rule), so lock-free message passing takes a lock instead.
**Before.** `lock K; write payload; unlock` on both sides. **After.** producer writes the payload then
`flag = 1 publishes payload`; consumer `awaits flag` then reads the payload without a lock.
**Options.** (a) Keep the lock (a performance cost on a path designed lock-free; guarantees kept).
(b) Implement the happens-before race-freedom rule: the producer writes the payload only before
`publishes`, the consumer reads it only after `awaits` (flow facts over two threads): checker L, Lean L
(DRF-SC extension of `RennfreiBis`/GX; the goal theorem's atomic rely gains a payload clause, a
Spec diff). No guarantee is weakened if done; it is the heaviest item here.
**Recommend (a) until the native backend measures the lock cost**; then (b) as an Opus task. It is the
only item whose payoff is a measured performance number rather than ergonomics.

## Suggested order
1) item 8(b), 3(b), 7(c)(d): small, no model risk. 2) items 5, 6, 4(b), 2(c): language forms over the
Lean groundwork that already exists. 3) items 9, 10: certification reach, Opus-level, after GabbroV.
4) items 1(b), 11: only on measured need.
