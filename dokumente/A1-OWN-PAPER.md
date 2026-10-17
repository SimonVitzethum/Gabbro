# A1 — `own` and separation at call boundaries (paper gate, 2026-10-17)

*Status: PAPER. No checker line was written. This is the gate `PLAN.md` A1 demands before
any code: both fragments stay writable, the loan carries the loop, no construct beyond what
exists. Result below: **GREEN, with one design decision taken** (re-views borrow, they do
not consume). Decision recorded by Simon's go-ahead of 2026-10-17; reverse it here, not in
code.*

## 1. Measurement (`gabbro alias`, source text only, release binary of 2026-09-30)

| tree | functions | S1 (>= 2 ptr params) | S2 (call sites) | S3 (same root) | S4 (re-views) | S5 (write/read split) |
|---|---|---|---|---|---|---|
| `beispiele/` (169 units) | 540 | 9 | 1 | 0 | 0 | 3 |
| `messung/` (265 units) | 774 | 26 | 6 | 1 | 8 | 14 |
| `bibliothek/` (3 units) | 46 | 0 | 0 | 0 | 0 | 0 |

The surface is small, so a rule at call boundaries touches few sites. **Blind spots
stand:** aliases through a table index, an address, or a call two frames up leave no trace;
sums over units do not see calls between units.

## 2. What already exists (do not re-invent)

- `SYNTAX.md` §9 row `own`: `ptr<…, own> T` is sugar for *"`T` is `owner m` and the callee
  `consumes m … allocs m`"* — **the mark is borrowed for the call and comes back.** So an
  `own` parameter already IS a loan.
- `m3.rs`: `R004` (one place at two `own` parameters of one call) and `R007` (one place at
  two writable parameters) — the syntactic half. `eigner_nie_erzeugt` (nobody mints a mark).
- What is missing is the other half: **two DIFFERENT names for one object.**

## 3. The gate, fragment by fragment

1. **F1 `delete_leaf(c, o, a, rf, s)`** — `a`, `rf` are `own`, `c`, `o` plain `rw`.
   Writable and distinct by declared type and by table. Stays writable. **Green.**
2. **F1 `revoke`** — calls `delete_leaf(c, o, a, rf, victim)` inside
   `traverse … by consuming`. The question was whether a linear value in a loop is consumed
   after the first pass. **Not with the existing reading:** `own` is a loan (§2), it comes
   back after each call, and the loop re-lends it. No `requires`-for-`consumes` rewrite is
   needed. **Green, no new construct.**
3. **F3 `call` (IPC fastpath)** — `f : ptr<…, rw+own> Frame` is returned as
   `ptr<…, rw+own> Frame`: the result is the SAME owner handed back, not a new one. Under the
   loan reading this is the "comes back" half. **Green.**
4. **Counter-probe `udp-echo::echo_beantworten(e, k, w, …)`** — `k : rw IpKopf` and
   `w : r Kopfworte` are two views of ONE header (`kopfworte_von` is an S4 alias factory);
   the body reads the checksum through `w` and writes `k`. This is the known stale-checksum
   defect (`PLAN-SICHERHEIT.md`). **The rule below must refuse the call that passes both.**

## 4. The decision: a re-view BORROWS, it does not consume

A function `fn(ptr A) -> ptr B` (S4) returns a pointer with **the same root** as its
argument. It does not consume the source (consuming would make every header read a hand-over)
and it does not mint a new owner. While both are live, they are one root.

## 5. The rule set (all generic, no per-program cases)

- **Root of a pointer expression:** a parameter name; a static; a fresh allocation / minted
  mark; the root of its source through a re-view, field or index. Anything else is `unknown`.
- **S-1 (separation at a call):** for every pair of pointer arguments `(i, j)` of one call,
  where at least one of the two parameters is writable or `own`, the two arguments must have
  **different roots**; `unknown` counts as a root equal to every other root. Pairs of two
  read-only parameters are free. (`R007` is the case "same place"; `R004` the `own` case.)
- **S-2 (inherited precondition, no annotation):** a function with >= 2 pointer parameters of
  which one is writable assumes its parameter roots pairwise distinct; its callers prove it
  by S-1. The obligation therefore travels up to entries, where roots are statics or
  allocations — distinct by construction.
- **S-3 (the boundary):** a function callable from outside the checked unit (exported,
  `extern`-facing, entry) cannot be proved by S-1. There the distinctness is either a
  **named assumption** of the binding or the parameters carry `own` explicitly. Decision on
  which of the two is left to the Lean slice (see §6) — it must not be silently a third thing.
- **Not built, on purpose:** lifetimes, regions of validity, a general borrow checker. If a
  fragment needs one, it is booked as the fifth-mechanism finding (A1 red), not smuggled in.

## 6. Plan, vertical slices (Lean first within each slice, per `AGENTS.md`)

1. **Slice 1 — root provenance in the checker, refuse-only.** New code for S-1 over
   parameter roots and re-views (S4). Poison probes: `echo_beantworten` shape, a re-view
   passed with its source, a field of the same root. Positive probes: `delete_leaf`/`revoke`
   shape, two read-only views. Measure the corpus: **0 new diagnostics outside the probes**
   is the acceptance; any hit is read by hand.
2. **Slice 2 — Lean.** A `ParamGetrennt` predicate (roots pairwise distinct) on the call frame,
   the preservation theorem under `exec_rahmen`, and the witness (non-degenerate fixture).
   `gabbro_ziel` must stay on exactly `propext`, `Classical.choice`, `Quot.sound`.
   **Status 2026-10-17: done at the model's granularity, with two obstructions named.**
   `grammatik/Grammatik/Logik/Vertraege/Getrennt.lean` (+ `GetrenntZeuge.lean`, SATZKARTE §74).
   - *What the model is.* `Ty.ptr n rw` names its carrier (table `tabNr n`) in the TYPE, and a
     pointer value is `Unit`; `own` is exported as read-write. The argument-to-carrier map of a
     call is therefore fixed by the callee's signature, and `ParamGetrennt` is a property of the
     callee: the map is injective on pairs with a writable side (`ParamGetrennt`, decided by
     `paramGetrenntB`, `paramGetrennt_iff`).
   - *Proved (generic).* `getrennt_paarweise`, `getrennt_schreiben_trennt` (disjoint carriers;
     a store through one leaves the other), `getrennt_lesesicht_bleibt` / `getrennt_ruf_rahmen`
     (with the frame declared over the parameters, every run of the call -- `rufAt`, every depth
     and world, through `rufAt_treu` -- leaves a read-only parameter's carrier unchanged),
     `leihe_wurzel`, `leihe_nicht_getrennt` (the borrow rule at one pointer type).
   - *Converse (witness).* `ohne_getrennt_nur_versprechen`: `aendern(k : ptr rw T, w : ptr r T)`,
     frame over the parameters, one real `rufAt` run moves the object behind `w` from 0 to 5.
     Positive witness `getrennt_ruf_rahmen_zeuge` on `getrennt(k : ptr rw T, q : ptr r U)`,
     whose run really writes `T`. All on `propext`, `Classical.choice`, `Quot.sound` at most.
   - *OPEN / obstructed.* (1) **Roots are finer than carriers**: two parameters of one table
     type are one carrier in the model whatever their roots, so S-1/S-2 (distinct roots) has no
     model statement; `R014`-clean is not `ParamGetrennt` there (the counter-model's two parameters
     are two names). Expressing S-2 needs objects below a table that a pointer can name -- a
     model change, not a lemma. (2) **Re-views across types do not reach the model**: record
     pointers and foreign re-views are refused by the exporter (`LG005`, `LG001`;
     `beispiele/1163` is `UNCERTIFIED LG001`), so the borrow rule is the model's reading only at
     one pointer type; two tables are disjoint by construction, sound only because no
     cross-type view is exported. (3) A frame naming a table directly (a static root beside a
     parameter) is outside `RahmenUeberParams`. The S-3 boundary decision stays with slice 3.
3. **Slice 3 — S-3 boundary** and the rows in `saetze.rs` (`pruefe-saetze.py`), `SYNTAX.md`
   §9, and the rewrite of `R004`/`R007` as the "same place" special cases of S-1.
4. **Slice 4 — compiler:** `noalias` only where S-1 holds (`LLVM-MODELLSTAND.md`: `own` →
   `noalias`; never guessed).

## 7. Risks, said now

- S-1 over-refuses wherever a root is `unknown` (a plain parameter reaching a callee together
  with another pointer). The corpus count in §1 says few sites; **slice 1 measures it before
  any promise.**
- The aliasing through table indexes (`slots[a]`, `slots[b]`, `a == b`) is NOT covered by
  roots; it stays the separate index-distinctness question (`M1`), not hidden here.
- This is a design decision about the language. A red slice-1 corpus measurement reopens it.
