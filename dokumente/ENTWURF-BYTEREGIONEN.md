# Byte regions in machine G -- the design for OFFEN O37

*C-free lane, 2026-10-05 (session 15). A design, not a result: nothing below is proved yet.
It exists because O37 moves the goal statement, and AGENTS.md §3 wants the `Spec.lean` diff
reviewed against a written reason before any code.*

## 1. What is open

OFFEN O37 names three gaps around a REGION -- the answer of a gate declared
`-> ptr<normal, …> u8 or R` with `ensures n <= lenof(result)` (`beispiele/183`):

| | |
|---|---|
| G has no byte pointers | `Ty.ptr t rw` is the capability to a DECLARED carrier `t`; a `ptr<…> u8` has no `Ty`, and `lean_g.rs` refuses it (`LG002`). Every program with one is `UNCERTIFIED`: 64, 168, 169, 180, 183 |
| nothing releases a region | no clause of a gate's contract ends a pointer's validity |
| a Gabbro body cannot pass the extent on | only a body-less callee's `ensures … <= lenof(result)` gives an answer an extent |

This document is about the first row. The other two build on it (§6).

## 2. What G has today

* `World.slots : ∀ t, Int → ∀ f, Wert (D.typ t f)` -- every declared table, indexed by ALL
  integers; `count` bounds the index TYPE (`Ty.index (D.count t)`), not the store.
* `Expr.durch (p : Expr (.ptr n rw)) t … (i : Expr (.index (D.count t)))` -- an access
  through a pointer is a slot access with the same guards (`darf D t Λ`).
* `leseBytes`/`schreibBytes` -- `n` bytes of a byte field, as one number.
* An axiom (`D.Ax`, every foreign body) answers through `Orakel.wirkt : World → Env → World × Int`;
  the raw word is fitted to the declared answer type by `einpassen`, and an answer outside the
  type is the hardware stop.
* `RennfreiBis` (Spec.lean): two unordered accesses by different threads to one carrier of
  `D.Tab ⊕ D.Glob`, one a write, are excluded.
* Twelve Lean files match on `Ty` constructors explicitly (37 `| fnptr` arms; measured
  `grep -rln "| fnptr\|| ptr " Grammatik` = 12). A new constructor is a bounded repair, not a
  rewrite of the model.

## 3. Measured facts the design stands on (2026-10-05)

Probes (scratch files of the C-free lane, `p1`-`p4.gab`; the one that became a rule is `beispiele/gift/1399`):

1. **A byte access needs an extent, and an extent has two sources only**: a gate answer bound
   once by `let … else` (the gate's `ensures n <= lenof(result)`), or the function's own
   `requires n <= lenof(p)` over a parameter it never assigns (`N571` at an index, `N463` at a
   call). A region stored in a `static` and read back has none: `q[0] = 1` falls with `N571`,
   `write(1, ABLAGE, 1)` with `N463` (`p2.gab`).
2. **An extent never crosses a thread** -- since `N578` of this session. Roots take no
   parameters; a `child` region reads only the value handed at the gate's `stack` parameter
   (`N451`/`N452`), and that parameter is now an integer (`N578`, gift 1399). Before `N578` a
   region handed as the stack was indexed by parent AND child with 0 errors (`p3.gab`) -- the
   one path by which region bytes reached two threads, found while writing this design.
3. Consequence: **every access to a region's bytes is made by the thread whose `let` bound
   the region, or by a callee on that thread.** Region bytes are thread-private memory. A
   race-freedom leg for them is a theorem about where region VALUES can live, not a new guard
   discipline.
4. The second source of byte pointers is an ARRAY passed where a `ptr<…> u8` is taken (decay,
   `beispiele/64`, `180`'s `PUFFER`): those bytes ARE a declared carrier, possibly shared and
   guarded, and every rule about that carrier applies to them.

## 4. The design

### 4.1 The type and the value

```lean
inductive Ty where
  …
  /-- `ptr<…, rw> u8` -- a byte place: where it points, never how far it reaches. -/
  | bytes (rw : Bool)

inductive BytePlatz (D : Deklaration) where
  /-- a byte field of a declared table, from slot `k` on (array decay) -/
  | traeger (t : D.Tab) (f : D.Feld t) (hf : D.typ t f = .int 0 255) (k : Int)
  /-- region number `r` of the store, from byte `k` on -/
  | region (r : Nat) (k : Nat)
```

`Val (.bytes rw) := BytePlatz D`. **The extent is not part of the value or the type.** The
checker keeps extents as FACTS over names (`n <= lenof(p)`), and G does the same (§4.3).

### 4.2 The store

`World` gains `regionen : Nat → Option (List Byte)` -- region `r`'s bytes, `none` before it is
handed over. Each region records the thread it was handed to (`RegionEigner : Nat → Option Faden`
in the thread machine's `Speicher`). A gate whose answer type is `.bytes true` creates the next
free number (fresh BY CONSTRUCTION in the model -- two answers never alias in G); its length is
the oracle's (the raw answer carries the base; the extent is the length the oracle hands, at
least what the gate's `ensures` names, which is the gate's contract and the template
`tor.region`'s `RegionVertrag`, user logic as before).

### 4.3 The access, and what stops it

```lean
| byteLies (p : Expr Γ Λ (.bytes rw)) (i : Expr Γ Λ (.int lo hi)) : Expr Γ Λ (.int 0 255)
-- Stmt
| byteSchreib (p : Expr Γ Λ (.bytes true)) (i : Expr Γ Λ (.int lo hi)) (v : Expr Γ Λ (.int 0 255))
```

* `.traeger t f _ k`: the access IS `slot t (k + i) f`, with `darf D t Λ` as a premise of the
  constructor exactly like `durch` -- so every guard and every race rule of `t` applies.
  Out of `0 ..< count t` is the new stop `Logik.ausdehnung`.
* `.region r k`: the byte `k + i` of region `r`. Outside the region's length, or a region not
  owned by the acting thread, is `Logik.ausdehnung`.

`Logik.ausdehnung` is a LOGIC stop, like `Logik.bereich` for floats: the program's own values
decide it, for every oracle. **Stage 1 (§5 S1) leaves it to `LogikPflicht`** -- the user's duty
already says no reachable machine stands at a logic stop, so `gabbro_ziel` stays true with no
new premise, and the duty is NAMED, not silent. **Stage 2 (S4) discharges it by a checker
component** (`ausdehnungB`, the Lean twin of `N571`/`N463`: linear facts over names bound once,
`passt`), and the duty then holds for every accepted unit.

### 4.4 Race freedom

Regions are not carriers of `D.Tab ⊕ D.Glob`, so `RennfreiBis` neither covers nor forbids them
as written. The statement gains ONE leg:

```lean
/-- Every region access is made by the region's owner. -/
def RegionPrivatBis … : Prop := ∀ … step i by thread f touching region r → RegionEigner r = some f
```

It holds because (i) the owner check is part of the access rule (anything else is
`Logik.ausdehnung`), and (ii) S4's component excludes that stop. A byte place of kind
`.traeger` is an ordinary carrier access and stays under `RennfreiBis` unchanged.

### 4.5 Where a byte place may live

`D.gtyp g ≠ .bytes _` and `D.typ t f ≠ .bytes _` -- a byte place is a value of `Env` only
(parameters, `let`s, answers). The exporter refuses a `static`/field of byte-pointer type by
name (`LG002`, the reason widened). That costs nothing the checker accepts today: a static
byte pointer has no extent (fact 1), so nothing can be indexed through it anyway.

### 4.6 Foreign bodies and the frame

A gate taking a byte place (`write(fd, buf, len)`) reads it through the oracle, which sees the
whole `World`. A gate that WRITES one (`read`) changes `World.regionen`/`slots`; its frame
becomes: only the places of parameters its `effects` name as written, within the `requires`
extent. That is a hardware assumption of (c) (`HardwareAnnahmen`), stated per axiom
(`aschreibtParam : Ax → Fin (aparams a).length → Bool`), the analogue of `aschreibt` for tables.

## 5. Slices

| | content | moves `Spec.lean`? |
|---|---|---|
| S1 | `Ty.bytes`, `BytePlatz`, `World.regionen`, `byteLies`/`byteSchreib` over `.traeger` only, `Logik.ausdehnung`; repair the twelve matching files; `gabbro_ziel` re-proved | yes: one `Logik` case (header: the reason) |
| S2 | regions: a gate answering `.bytes true` allocates; `RegionEigner`; `.region` accesses; `RegionPrivatBis` leg | yes: one leg, one hardware frame clause |
| S3 | exporter: `LG002` lifted for `ptr<…> u8` parameters, lets and region answers; the gate's `ensures n <= lenof(result)` as an extent fact (today `LG003`) | no |
| S4 | `Akzeptiert` component `ausdehnungB` (twin of `N571`/`N463`), the duty discharged | yes: (a) gains a component |
| S5 | GabbroV `Body` + bridge; C correspondence (the template `tor.region` exists) | no |

Then the other two rows of O37: a release clause (`own` on a gate parameter kills the bound
name -- regions get a `freigegeben` state and an access to it is `Logik.ausdehnung`), and a
Gabbro body passing an extent on (an `ensures n <= lenof(result)` at a Gabbro function
becomes provable once S4's facts exist in G).

## 6. What this design does NOT claim

* Nothing about the kernel: that a mapping is fresh, readable, writable and as long as the
  oracle says is the gate's contract (`linux_seiten_holen`), user logic, unchanged.
* No pointer arithmetic, no int->ptr: `BytePlatz` is built only by decay of a declared
  carrier and by a gate's answer (Simon's decision 1).
* No byte place in shared memory (§4.5): passing a region between threads stays
  inexpressible -- by design for now; lifting it needs a guard discipline for regions.

## 7. Why S1 is not started by the C-free lane alone

Measured 2026-10-05: a new `Expr` constructor reaches 19 Lean files (62 `leseBytes` sites as
the yardstick), a new `Stmt` constructor more (176 `assignDurch` sites), and **both inductives
are read by the direct x86-64 compiler's modules** (`Grammatik/X86/ExpressionLowering.lean`,
`X86/OptDceDead.lean` among the `leseBytes` sites) -- the area where the laptop's Muse lanes
integrate dozens of branches a day. A change of `Syntax.lean`'s core inductives breaks every
open branch that matches on them at its merge. S1 therefore needs a coordinated slot from the
orchestrating session (a short freeze of `Syntax.lean`/`Typen.lean` consumers, or a lane that
owns the repair across `X86/`), not a private fork of this lane. Until then this file is the
reviewed design target, and the gap stays named in OFFEN O37.
