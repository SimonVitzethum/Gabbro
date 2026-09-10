# SYNTAX section draft: TOCTOU as a documented class (design only)

Status: DESIGN ONLY, no implementation. Worktree lane-90, base 536e118,
2026-09-10. Source of fact: `messung/TOCTOU-KATALOG.md` (measured against
`d162dfc`), which owns the five patterns, their windows, and for each what
the checker holds across the window today. This note owns the prose that
`dokumente/SYNTAX.md` will carry. Do NOT edit `SYNTAX.md` itself from this
lane; a later lane moves the text over.

## 1. Placement proposal

One primary landing spot, two cross-references, all already shaped for it:

- Primary: `dokumente/SYNTAX.md` section 16.2 gains a new item, numbered
  10, naming check-then-use as a class. The draft prose in section 2 below
  is the item text; the table in section 3 below is its carrier-or-gap
  register. Section 16.2 is the right home because every pattern below is
  already booked there in pieces (interleavings in item 1, the memory model
  in item 2, devices in item 3, cost and deadlines in item 7) without ever
  saying the pieces share one shape.
- Cross-reference one: the section 11 row for `let x = A awaits { p, q };`
  appends one sentence pointing at the new item, so the awaits-then-act gap
  (a load that rebinds clean and is never revalidated) is named where the
  spelling lives.
- Cross-reference two: the section 10 device table appends the H018 half of
  the mapping from section 4 below beside the `transition` row, so the
  driver-handoff window is named where the doorbell lives.

No grammar production moves with this draft: no spelling changes, no new
attribute, no new Lean shape. The draft documents the class; the rules it
names already exist.

## 2. Draft prose for the section 16.2 item

> 10. check-then-use. Every pattern in this item has the same three parts:
> a check that establishes a fact, a window during which the world can move,
> and a use that relies on the fact still holding. What differs between the
> patterns is what moves, and what the checker holds across the window. The
> discipline for all five is one rule, stated as validation-copy: a checked
> value may be used after the window only through a carrier the checker
> still holds, and where no carrier reaches across the window the use must
> revalidate or copy under the guard the use relies on. A use of the
> pre-window value with neither a held carrier nor a fresh validation is
> the shape this item refuses wherever a rule stands beside it, and names
> as a gap wherever none stands. The five instances are narrow-then-use
> (a narrowed carrier-derived value or a tainted local acted on later in
> the same body), syscall check-then-copy (a Gabbro-side validation of a
> length or pointer consumed by foreign copy code), awaits-then-act (a
> published snapshot acted on after the load), budget-check-then-run (a
> statically counted cost relied on across the call boundary), and
> deadline-check-then-run (a probed cycle count relied on at deployment).
> The table beside this item says for each instance what carries it and
> where the gap stands, with the reason beside each gap.

## 3. Per-pattern carrier-or-gap table

| pattern | window | carrier, or gap with reason |
|---|---|---|
| narrow-then-use | narrow point to use point, inside one body | carried per writer: own-body writes kill facts per write and expire taints at carrier granularity (M147); direct calls kill and expire per callee writes-hull, with coarse kill-all-nonlocal when the hull is unreadable; indirect calls expire every taint since this lane (M147, gift 715 through gift 717); loops expire all taints at the boundary and never carry facts inward (gift 703, gift 709). Open gap: concurrent siblings, where one body with one Lage never walks beside the other, so no expiry crosses the member boundary; W001 refuses same-place and same-table writes between declared-concurrent bodies, which narrows but does not close the read-and-use remainder. |
| syscall check-then-copy | Gabbro-side check to foreign copy | carried at the boundary and exported beyond it: both halves die at the extern call (V1 facts over non-locals, every V4 taint), so a checked value cannot be used afterwards without a re-read. By-construction gap: inside the foreign body a re-read is invisible and an ensures clause that narrows is trusted surface (see FREMDVERENGUNG). |
| awaits-then-act | load to act | carried for order, open for staleness: V006 and V007 hold the payload order, V001 and V002 refuse orphan halves, V004 and V005 hold the ordering strength on the publish side. No revalidation rule stands: the load rebinds clean because it is fresh at load time, and nothing later expires it on a concurrent publish. Staleness stays a logic question the pairing rules deliberately do not ask. |
| budget-check-then-run | count time to run time, across the call boundary | carried by counting and refusing: the K pass counts statically, K005 refuses a promise the pass cannot read, an indirect call costs what its fn type promises and falls without a constant bound, E008 reconciles declared effects against the computed hull. Fail-closed gap: a count over a domain with no length is refused outright by D025 (gift 693) instead of admitted as an unbounded budget; foreign costs are trusted certificate lines, same export as pattern 2. |
| deadline-check-then-run | probe run to deployment on the named machine | carried structurally only: K011 a readable number, K012 a declared machine, N056 a falsifier that resolves in-unit, booked as the named assumption hardware fortschritt with manifest entry frist fn eingehalten and sample probe sonde tick. By-construction gap: a sample is not a bound, an unresolved probe is a program next to the tree, and the Lean mapping fristAlsAnnahme proves nothing about time. |

## 4. Rule mapping: M147, H018, and the future rules

M147, built. The freshness refusal for V4 taints: decision-uses of expired
locals fall, while storing or moving an expired local stays allowed. It pins
the narrow-then-use row of the table above across own-body writes, direct
calls with readable and unreadable hulls, the loop boundary (gift 703), and
since this lane across indirect calls (gift 715 for a statement call, gift
716 for a call in a let right-hand side, gift 717 for the boundary where a
refresh and a store stay silent and only a narrow subject falls). Measured
beside gift 702, the stale decision that falls as M147 alone. The follow-up
the catalog books but does not build is precision, not coverage: refine the
indirect-call expiry with the fn type contract (reads, writes, pure) instead
of expiring everything. The coarse rule errs safe, and no corpus site shows
a hot tainted path through an indirect call yet.

H018, built. The driver-handoff rule: a function that writes a DMA-visible
buffer place and rings the MMIO doorbell holds one guard across both halves
of the window. It is the checker half of the GeraetWache premise from
Geraet.lean (handoff before the device write, take-back after, the CPU side
ordered against the endpoints), where every window of a chain runs under one
guard. Three limits stand beside it: direct writes only (a doorbell behind a
transition call or an extern fn is not a site), intraprocedural (both halves
in one body), strength unasked (shared-held orders as well as exclusive).
Measured at gift 724 through gift 726, each with a guarded twin that stays
silent. In the table above H018 belongs to the syscall check-then-copy row
as the driver-shaped instance: the check is the buffer fill, the use is the
doorbell, and the guard is what holds the window.

Future rules, not built. Three, one per open gap in the table: cross-body
expiry needs hull propagation through the nebeneinander machinery, not a
kill line, so it waits on that transport; awaited-value revalidation needs
a rule that expires a clean load on a concurrent publish, which the pairing
rules deliberately do not ask today; foreign-body visibility (re-reads after
the check, narrowing ensures clauses) is exported by construction and can
only be narrowed by contracting the foreign surface, never by checking it.
None of the three is a refusal this lane can add; the draft names them so
the later lane that adds one has the item text already standing.

## 5. Self-check (this lane) and what the next lane owns

No build was run in this lane; `SYNTAX.md` is untouched; the Lean index is
untouched. This file carries prose and references only, so no EBNF counter
reads it: it holds no fenced grammar blocks and no production-shaped lines.
The next lane moves the section 2 prose into section 16.2 as item 10,
places the section 3 table beside it, appends the two cross-reference
sentences from section 1, and proves nothing new: M147 and H018 arrive
already measured, and the future rules arrive already named.
