# A1 — `own` and separation at call boundaries

*Design record of the aliasing rule `R014` and its model. Decided 2026-10-17 on a paper gate:
both fragments of the target kernel stay writable, the loan carries the loop, and no construct
beyond what exists was needed. **Status: slices 1-4 are built.** The decision "a re-view borrows,
it does not consume" is recorded here; reverse it here, not in code.*

**Summary.** Two pointer arguments of one call must not point at one object when one of the two
callee parameters is writable or `own`. The checker decides it from provenance roots (`R014`,
`m3.rs`); the Lean model proves what separation buys (`Logik/Vertraege/Getrennt*.lean`,
`Objekt*.lean`, SATZKARTE §74-§76); the LLVM backend uses it for `noalias` where the checker holds
the whole call. What is not proved is listed in §7.

## 1. Measurement (`gabbro alias`, source text only, release binary of 2026-09-30)

| tree | functions | S1 (>= 2 ptr params) | S2 (call sites) | S3 (same root) | S4 (re-views) | S5 (write/read split) |
|---|---|---|---|---|---|---|
| `beispiele/` (169 units) | 540 | 9 | 1 | 0 | 0 | 3 |
| `messung/` (265 units) | 774 | 26 | 6 | 1 | 8 | 14 |
| `bibliothek/` (3 units) | 46 | 0 | 0 | 0 | 0 | 0 |

The surface is small, so a rule at call boundaries touches few sites. **Blind spots stand:**
aliases through a table index, an address, or a call two frames up leave no trace; sums over
units do not see calls between units. *These counts are a dated measurement of the corpus of that
day, not re-run for this revision; `gabbro alias <file.gab>` re-measures.*

## 2. What already existed

- `SYNTAX.md` §3 row `own`: `ptr<…, own> T` is sugar for *"`T` is `owner m` and the callee
  `consumes m … allocs m`"* — **the mark is borrowed for the call and comes back.** An `own`
  parameter is already a loan.
- `m3.rs`: `R004` (one place at two `own` parameters of one call) and `R007` (one place at two
  writable parameters) — the syntactic half; `eigner_nie_erzeugt` (nobody mints a mark).
- Missing was the other half: **two DIFFERENT names for one object.**

## 3. The gate, fragment by fragment

1. **F1 `delete_leaf(c, o, a, rf, s)`** — `a`, `rf` are `own`, `c`, `o` plain `rw`. Writable and
   distinct by declared type and by table. Stays writable. **Green.**
2. **F1 `revoke`** — calls `delete_leaf(c, o, a, rf, victim)` inside `traverse … by consuming`.
   The question was whether a linear value in a loop is consumed after the first pass. **Not with
   this reading:** `own` is a loan, it comes back after each call, and the loop re-lends it. No
   `requires`-for-`consumes` rewrite is needed. **Green, no new construct.**
3. **F3 `call` (IPC fastpath)** — `f : ptr<…, rw+own> Frame` is returned as `ptr<…, rw+own> Frame`:
   the SAME owner handed back, not a new one. The "comes back" half of the loan. **Green.**
4. **Counter-probe `udp-echo::echo_beantworten(e, k, w, …)`** — `k : rw IpKopf` and
   `w : r Kopfworte` are two views of ONE header (`kopfworte_von` is an S4 alias factory); the body
   reads the checksum through `w` and writes `k`. The known stale-checksum defect. **The rule below
   refuses the call that passes both.**

## 4. The decision: a re-view BORROWS, it does not consume

A function `fn(ptr A) -> ptr B` (S4) answers a pointer with **the same root** as its argument. It
does not consume the source (that would make every header read a hand-over) and it does not mint a
new owner. While both are live, they are one root.

## 5. The rule set (generic, no per-program cases)

- **Root of a pointer expression:** a parameter name; a static; a fresh allocation or minted mark;
  the root of its source through a re-view. Anything else — a field, an index, an indirect call,
  an unresolved callee, an argument that is no bare name, a re-view of an untraced pointer — is
  **`unknown`, and `unknown` equals every root.**
- **S-1 (separation at a call, `R014`):** for every pair of pointer arguments of one call where at
  least one of the two parameters is writable or `own`, the two arguments have **different roots**.
  Pairs of two read-only parameters are free. (`R007` is the case "same place"; `R004` the `own`
  case; they remain separate rules.)
- **S-2 (inherited precondition, no annotation):** a function with >= 2 pointer parameters of which
  one is writable assumes its parameter roots pairwise distinct; its callers prove it by S-1. The
  obligation travels up to entries, where roots are statics or allocations, distinct by
  construction.
- **S-3 (the boundary, `R015`):** a function callable from outside the checked unit (`pub`, or
  called by no body of its unit) cannot be proved by S-1. Its assumption of distinct parameters is
  a **named assumption**, reported as a **hint** (`R015`), not a refusal: refusing would tighten
  every export with a pointer pair. Whether it should grow into an explicit `own` at the boundary
  is open and recorded, not decided.
- **Not built, on purpose:** lifetimes, regions of validity, a general borrow checker. A fragment
  that needs one is booked as the fifth-mechanism finding, not smuggled in.

## 6. Slices — what was built, in order

**Slice 1 — root provenance in the checker (`R014`), refuse-only. Built.** `m3.rs::getrennte_wurzeln`,
sentence `m3.zeiger_wurzel`, rows in `crates/gabbro-check/tests/wurzeln.rs` (refusing rows each with a
silent twin that differs in one place). Poison probes: `beispiele/gift/257` and `1444`
(`alias-sicht-und-quelle`); positive probes: `delete_leaf`/`revoke` shape, two read-only views,
example `1163` (`sicht-neben-eigener-quelle`). Acceptance was 0 new diagnostics outside the probes.

**Slice 2 — Lean, at carrier granularity (§74). Built.** `grammatik/Grammatik/Logik/Vertraege/Getrennt.lean`
and `GetrenntZeuge.lean`.
- *What the model is.* `Ty.ptr n rw` names its carrier (table `tabNr n`) in the TYPE, and a pointer
  value is `Unit`; `own` is exported as read-write. The argument-to-carrier map of a call is
  fixed by the callee's signature, so `ParamGetrennt` is a property of the callee: the map is
  injective on pairs with a writable side (`ParamGetrennt`, decided by `paramGetrenntB`,
  `paramGetrennt_iff`).
- *Proved (generic).* `getrennt_paarweise`, `getrennt_schreiben_trennt` (disjoint carriers; a store
  through one leaves the other), `getrennt_lesesicht_bleibt` / `getrennt_ruf_rahmen` (with the
  frame declared over the parameters, every run of the call — `rufAt`, every depth and world,
  through `rufAt_treu` — leaves a read-only parameter's carrier unchanged), `leihe_wurzel`,
  `leihe_nicht_getrennt` (the borrow rule at one pointer type).
- *Converse (witness).* `ohne_getrennt_nur_versprechen`: `aendern(k : ptr rw T, w : ptr r T)`, frame
  over the parameters, one real `rufAt` run moves the object behind `w` from 0 to 5. Positive
  witness `getrennt_ruf_rahmen_zeuge`.
- *Obstructions it named* (not gaps to close by a premise): roots are finer than carriers (two
  parameters of one table type are one carrier whatever their roots), so slice 2b followed;
  re-views across types do not reach the model (record pointers and foreign re-views are refused
  by the exporter, `LG005`/`LG001`; `beispiele/1163` is `UNCERTIFIED LG001`); a frame naming a
  table directly is outside `RahmenUeberParams`.

**Slice 2b — objects below a table (Simon's decision, §75). Built, for objects that are one slot.**
`Objekte.lean`, `ObjektRahmen.lean`, `ObjektWurzel.lean`, `ObjektZeuge.lean`. Machine G and
`Zielsatz/Kern/Spec.lean` are unchanged; `gabbro_ziel` stays on `propext`, `Classical.choice`,
`Quot.sound`.
- *The choice.* An object is a SLOT: `Obj` = (carrier, identity), every field of slot `nr` of table
  `tab`. G's world is already indexed this way and a record pointer into a table names one record;
  a field would be finer than a pointer names, a table is slice 2. A pointer to one object is the
  PAIR of parameters G already has — the capability `ptr n rw` and an index into its table
  (`ObjPar`) — so the identity is a value the caller chooses.
- *Proved (generic).* `ObjGetrennt` (injective on every pair with a writable or `own` side);
  `objGetrennt_schreiben_trennt`; **`objGetrennt_ein_obj_iff`** (with one object per carrier,
  `ObjGetrennt` IS `ParamGetrennt`) and `getrennt_objGetrennt`. The object discipline of a body
  (`oS`/`oB`/`oE`, over the whole grammar; indirect calls and `schreibBytes` refused) gives
  **`rufAt_obj`** and **`obj_ruf_rahmen`**: under `ObjGetrennt` every run leaves every field of
  every read-only parameter's object, also when it lies in the table the call writes. Borrow rule:
  **`umsicht_behaelt`** (a body `return k;` answers the object it was handed).
- *The bridge to `R014`.* `Herkunft` (parameter / fresh / re-view / union / unknown) with the roots
  of §5 (unknown = every root); **`r014_objGetrennt`**: disjoint roots at a call give
  `ObjGetrennt` under four NAMED hypotheses — `ParamVerschieden` (S-2; at an entry the `R015`
  assumption, never discharged), `FrischNeu` (fresh answers are new objects; a theorem for the
  model's allocator, `frischNeu_aus_arena` over `ArenaDyn.freiAlloc`), `RechteOk` (a writable
  parameter gets a writable root, `R002`/`R003`), `HerkunftTreu` (every argument names what its
  provenance denotes; for a re-view in the model `umsicht_behaelt`, for a foreign re-view or a
  fresh answer the binding's contract). `r014_ruf_rahmen` composes it with `obj_ruf_rahmen`.
- *Witnesses.* `aendern(kp : ptr rw T, k, wp : ptr r T, w)` over ONE table: at `k = w = 0` not
  `ObjGetrennt` and one real run moves `w`'s object 0 -> 5; at `k = 0, w = 1` `ObjGetrennt`, every
  run leaves `T.slots[1]`, and `ParamGetrennt` fails (`zeuge_obj_feiner`: strictly finer than
  slice 2). `aendern(k, sicht(k))` is never separated and `R014Rein` refuses its provenance;
  `aendern(k, f)` with `f` the allocator's first fresh slot is `R014`-clean and the frame follows
  (`zeuge_r014_ruf_rahmen`).
- *Finding (checker) — CLOSED.* The first `getrennte_wurzeln` gave an untraced name NO root and
  skipped every pair with it, and a re-view whose argument had no root got a FRESH root, against
  §5 ("unknown counts as every root"). A re-view through a function pointer,
  `let w = v.s(k); aendern(k, w);`, passed with 0 errors, and `rust_lesart_luecke` proved the Rust
  reading unsound in the model. **Repaired in commit `a6a2e2d6`:** `UNBEKANNT` is a root equal to
  every root (an unresolved or indirect callee, a field read, an argument that is no bare name, a
  re-view of an untraced pointer); a fresh root is only for an answer that comes from no pointer
  argument. Measured: 0 new `R014` over every tracked `.gab` except the probe `gift/1444`;
  `wurzeln.rs` has 10 rows (function-pointer re-view, field pointer and the read-only twin are new);
  the sentence `m3.zeiger_wurzel` was rewritten.

**Slice 3 — the boundary hint `R015`, rows in `saetze.rs`. Built.** `m3.rs`, sentence
`m3.zeiger_wurzel_grenze`, a hint at an exported or uncalled function that assumes two pointer
parameters distinct; both directions in `wurzeln.rs`. `SYNTAX.md` §3 carries the pointer rule.
**Not done from the original plan:** rewriting `R004`/`R007` as the "same place" special cases of
`R014` — they remain two rules beside it.

**Slice 4 — compiler, `noalias` only where the checker holds the whole call. Built.**
`crates/gabbro-check/src/llvm.rs`; `noalias` was emitted only at `own` parameters, and now also on
a WRITABLE pointer parameter of a function that is not `pub`, has a body, is called from a body of
its unit, has its address nowhere taken, is named by no entry/boot/concurrent item, and whose
declared `effects` name nothing but its own pointer parameters (`E008` keeps that list a superset
of its callees', so the function cannot reach the pointee through a global). Calls into it are held
by `R014`; it rests on the named `R015` assumption of exported callers. A unit with a function
value outside a function body gets no extension. Measured: 10 `noalias` over `beispiele/` +
`messung/*/` (was 2), the IR verifies with `opt`; `tests/noalias.rs` has one positive row and four
refusing twins (exported, uncalled, address taken, table named in the effects). The rule is a Rust
checker rule, **not a Lean judgment**; the model side is `Logik/Vertraege/Objekt*.lean`
(`dokumente/LLVM-BACKEND.md`).

## 7. What is open

1. **Records over byte buffers.** Objects are single slots: a record laid over a byte buffer (a
   `format`, n slots) is not one object, so the cross-type re-view of `udp-echo`
   (`kopfworte_von : ptr IpKopf -> ptr Kopfworte`) has no model statement. It needs range objects
   over a byte table and `schreibBytes` in the discipline. `LG005` (record pointers) and `LG001`
   (foreign re-views) stay: lifting them needs the exporter to lower each record-pointer
   parameter to the pair (`ptr n rw`, `index (count t)`) and every `p.f` to `durch p t f (var k)`,
   a decided discipline check per exported body, and a contract form for a foreign re-view's
   `HerkunftTreu`.
2. **The four bridge hypotheses** of `r014_objGetrennt` are named, not proved for the checker:
   `ParamVerschieden`, `FrischNeu` (proved only for the model's allocator), `RechteOk`,
   `HerkunftTreu`.
3. **The checker's walk over `let`s** (flat, no scoping; a name bound twice carries the union of its
   roots) is not formalised over G syntax; its correctness is the premise `HerkunftTreu`. The
   discipline is a `Prop`, no Bool the exporter could compute.
4. **`R004`/`R007` are not yet special cases of `R014`.**
5. **No mutation run** has been done over the new rule (`mutiere-pruefer.py`): none of
   `getrennte_wurzeln` or the `noalias` conditions has been mutated and measured.
6. **The S-3 decision** (named assumption vs. explicit `own` at the boundary) is recorded, not
   taken.

## 8. Risks, said now

- S-1 over-refuses wherever a root is `unknown` (a plain parameter reaching a callee together with
  another pointer). Measured after the repair: 0 new `R014` over every tracked `.gab` except the
  probe; the corpus count in §1 says few sites.
- Aliasing through table indexes (`slots[a]`, `slots[b]`, `a == b`) is NOT covered by roots; it
  stays the separate index-distinctness question (`M1`), not hidden here. At the model's object
  granularity the two indices are the identity `ObjGetrennt` compares, which is why slice 2b helps
  there only where the discipline of §75 applies.
- This is a design decision about the language. A red corpus measurement reopens it.

## 9. Where it lives

| What | Where |
|---|---|
| the rule, in the language | `SPRACHE.md` §5 (aliasing is decided at calls), `SYNTAX.md` §3 (pointer rows) |
| the checker | `crates/gabbro-check/src/m3.rs` (`R004`, `R007`, `R014`, `R015`), sentences `m3.zeiger_wurzel`, `m3.zeiger_wurzel_grenze`, rows `tests/wurzeln.rs` |
| the model | `grammatik/Grammatik/Logik/Vertraege/{Getrennt,GetrenntZeuge,Objekte,ObjektRahmen,ObjektWurzel,ObjektZeuge}.lean`, SATZKARTE §74-§76 |
| the backend | `crates/gabbro-check/src/llvm.rs`, `tests/noalias.rs`, `dokumente/LLVM-BACKEND.md` |
| probes | `beispiele/gift/257`, `beispiele/gift/1444-alias-sicht-und-quelle.gab`, `beispiele/1163-sicht-neben-eigener-quelle.gab` |
