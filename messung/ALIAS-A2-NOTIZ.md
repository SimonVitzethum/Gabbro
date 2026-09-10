# A2 census and the cheapest exact rule

Lane: lane-14. Base: 291c27b. Date: 2026-09-10.

This note records the A2 census (two pointers to one object under
different names) and the cheapest rule that answers the event half
exactly, without building an alias analysis.

## 1. What A2 is

A2 is race form A2 of `messung/RACE.md`: two pointers to the same
object under different names. The canonical shape is
`w = kopfworte_von(k)` in `messung/netz/udp-echo.gab`: one memory
area, once as fields through `k` and once as words through `w`.
Nothing in the checker refuses it today.

## 2. Census case: the stale checksum at zero errors

`echo_beantworten` in `messung/netz/udp-echo.gab:231` takes `k` and
`w` side by side from the caller and declares
`effects { reads e, reads w, writes k }`. It reads the IPv4 header
checksum through `w` (`kopf_gueltig` at line 158, via `kopfsumme`
over `w`) and then writes `k.quelle`, `k.ziel`, and `k.ttl` through
`k` (lines 251-254). Both views cover the same twenty bytes, and
`kopfworte_von` at line 154 states what `w` is. RFC 791 section 3.1
requires the checksum to be recomputed after such writes. The
checker reports:

    messung/netz/udp-echo.gab: 25 items, 0 errors, 0 hints

The rights half is correct there (`w` carries read-only rights, `k`
carries read-write rights, each access is within its rights). What is
missing is the event half: a statement of the form "a write through
`k` expires what was read through `w`". That statement is not a
rights check and not an alias analysis; it is an ordering between
two named program points, of the same kind as `V006` at the pairing.

## 3. The five strata from `alias.rs`

Source: `crates/gabbro-check/src/alias.rs`. The counter is a census,
not a pass: it refuses nothing and decides nothing. Corpus figures
below are quoted from `messung/RACE.md` section 3, measured over
53 units (213 functions, 86 with at least one pointer parameter)
with `gabbro alias --summe`.

| stratum | what it counts | error direction | corpus count |
|---|---|---|---|
| S1 | signatures with 2 or more pointer parameters | over-counts: two pointers may point at disjoint objects | 10 (writable 9) |
| S2 | call sites passing 2 or more pointer arguments | over-counts, same reason | 3 (writable 2) |
| S3 | of those, two arguments sharing one syntactic root | under-counts | 0 (writable 0) |
| S4 | re-views of shape pointer-to-A to pointer-to-B, the alias factories | under-counts | 2 (taken at 0 sites) |
| S5 | S1 bodies whose effects write through one pointer and read through another | over-counts within S1 | 5 |

Notes on the rows:

- S1 and S2 are upper bounds; S3 and S4 are lower bounds. The true
  figure lies between them. Printing only one side would let the
  reader choose the flattering direction.
- S5 reads the declared `effects` clause, not the body, because the
  clause is already held against the body elsewhere. For a function
  with missing or incomplete effects, S5 counts what the clause
  states, not what the body does.
- The S4 sites are both in one unit: `netz::udp_echo::kopfworte_von`
  (IpKopf to Kopfworte) and `netz::udp_echo::udpkopf_von`
  (IpKopf to UdpKopf). Neither is called in the same file; the live
  alias enters through the signature of `echo_beantworten`, which
  receives `k` and `w` together from outside.
- The five S5 sites, spelled out: `beispiel::zeuge::aufloesen`,
  `beispiel::handschlag::uebertragen_lassen`,
  `netz::udp_echo::echo_beantworten`, `caprock::kapraum::blatt_loeschen`,
  and `caprock::kapraum::einsammeln`. Of these, one carries genuine
  protocol relevance: `echo_beantworten`.
- S3 is zero on the clean corpus. The syntactically definite alias
  (the same name twice at one call) does not occur there.

## 4. What none of the five sees

An alias through a table index, through an integer address, or in a
caller two frames up leaves no trace in any count. The udp-echo case
lands in S4 and S5 because `kopfworte_von` is written as a function;
had the same re-view been done by arithmetic on an address, every
figure here would be one smaller and nothing about the program would
have changed. All five strata count what the source states.

## 5. Cheapest exact A2: stale-use taint

Design source: `messung/FRISCHE-V4-ENTWURF.md`. The proposal makes
alias analysis unnecessary by never asking whether two names alias.
It tracks freshness from syntax alone: a taint map beside the M1
fact set records, per function body, which locals hold
carrier-derived data and from which carrier (carrier granularity,
table or static name only).

- The map grows at exactly one place: a binding whose right side
  reads a carrier, or calls a function whose effects read one.
- A write naming a carrier expires every local tainted by that
  carrier, whether the access paths match or not. Own writes expire
  too. Loop boundaries clear all taints; calls clear the taints of
  carriers in the callee writes-hull.
- An expired local may still be stored or moved (write right side,
  passing it on), but may not be acted on: branch or match
  condition, call argument, return value, narrow subject, index.
  Acting on it is refused as `logik (veraltet x)`, a named clause of
  the existing refusal, so no new error constructor and no change to
  the sentence induction.
- There is no may-alias lattice anywhere in this design.

Ceremony, measured in the draft over 131 files: 12 carrier-derived
bindings, 9 of them device-register reads (excluded by construction),
leaving 3 table-derived ones, of which one swap temporary stays
allowed as a move, one never meets a killing write, and one needs a
re-read (1 to 2 sites against the narrow yardstick of 24).

Loud statement, carried over from the draft: the literal
`udp-echo.gab` still passes under this rule, and must. Its defect is
an omission (the checksum is never recomputed after the `k` writes)
and no local holds the stale value, so no expiry can fire. The rule
catches the udp-echo shape (a named stale use: read a sum through
`w`, write through `k`, then decide on the stored sum) rather than
the missing recompute. A rule that flagged the literal file would be
flagging without a stale name.

Falsifier pair from the draft: a binding `let sum = kopfsumme(w)`
followed by `k.ttl = 64` and a branch on `sum` must fail; a fresh
read of `kopfsumme(w)` after the write, with no live taint between,
must pass.

## 6. Status

A2 itself stays open by design. The taint rule answers the event
half (A3) and leaves the alias question (A2) unasked. The figures in
section 3 are the basis on which a later decision about a full
analysis can rest; building one without that decision would add
trust surface.
