# The correspondence table — Lean fragment against Gabbro `pred`/`expr`

*Ordered by `AUFTRAG-GABBROV.md` §7. One row per construct of the Lean
fragment with its named counterpart in Gabbro's `pred`/`expr` — and a
guardian that holds both lists against each other:*

```
./instrumente/zaehle-pflichten.py --korrespondenz
```

*Two directions, two hardnesses (§7): Lean-can-Gabbro-cannot is **red** —
a failure, the fragment is taken back or the Gabbro side is built first.
Gabbro-can-Lean-cannot is **yellow** — the obligation ends undecided and
stands in `OFFEN.md` by name. Red must be empty and stay empty; what keeps
it empty is the order, not luck: demands get a table row only when the
Gabbro side lands first (§7.3).*

*Measured 2026-09-09 from tree `1af516a`. Every verdict below names the
command or the line it was read off.*

---

## The rows

*Each cell holds `/`-separated names, and every one of them resolves: a
`LEAN` name occurs in `V1.lean`, `V2.lean`, `lean.rs` or `Body.lean`; a
`GABBRO` name in `ast.rs`, `kw.rs`, `parse.rs` or `SYNTAX.md`. The guardian
checks exactly that — a row that names nothing is not a correspondence.*

| Lean construct | Gabbro counterpart | Verdict | Evidence |
|---|---|---|---|
| `LEAN ∧/∨/¬/→` | `GABBRO Und/Oder/Nicht/Folgt/Klammer` | `GREEN` | `lean.rs:1308` carries all three connectives; `.bin`/`.un` emitted over `messung/fragmente/F01.gab` |
| `LEAN =/≠` | `GABBRO Vergleich` | `GREEN` | `lean.rs:1305` (`in_expr`), `:1337` (`expr_term`); `duty_4`–`duty_6` carried over `beispiele/01-tabelle.gab` |
| `LEAN allD/forallSlots` | `GABBRO Quantor/SlotsVon/ElementeVon/Alle/Existiert` | `GREEN` | `lean.rs:1376` carries `Alle`/`Existiert`; `(.forallSlots …)` emitted; `F01.gab`: `total 17 goals 17 refused 0` |
| `LEAN World` | `GABBRO Vergleich` | `GREEN` | single-state predicates: the V1 rows over one `World` (`L18`–`L22`: `reg w "GSTS" …`); carried |
| `LEAN State` | `GABBRO ensures/requires/old` | `GREEN` | relations over pre/post pairs: 20 of the 66 V1 rows take `(s s')`; the `V` call-site duties of `F01.gab` are carried. §7's phrase *"predicates over values"* reads as one state and is corrected in `GABBROV.md` §7 (§7.1) |
| `LEAN wrapTo` | `GABBRO wrapping` | `GREEN` | integer arithmetic with overflow: `(.wrapTo 32 …)` emitted over `F01.gab`; an `opaque` type gives no bound by design |
| `LEAN .int` | `GABBRO bitpos` | `GREEN` | no divergence measured; caveat: no row of the 63 exercises dedicated bitvector operations (`V1.lean` and `lean.rs` carry no bit terms, all five F2 rows are integer comparisons) |
| `LEAN SpecShape` | `GABBRO spec fn` | `GREEN` | pure helpers: carried when the body is a plain expression; otherwise `LeanReason::SpecShape` refuses — a rejection, not a divergence |
| `LEAN reachesIn` | `GABBRO Erreicht` | `GREEN` | `lean.rs:1436` emits `(.reaches tab from to via count)`; `(.reaches "CapSpace" … "parent" 80256)` stands in the `F01.gab` export; `F01.gab`: `total 17 goals 17 refused 0`. §7.2's yellow premise (*"the Lean channel refuses it by name"*) no longer holds — another lane built the carrying path, and this row records the measurement instead of the premise |
| `LEAN Atom` | `GABBRO Vergleich` | `GREEN` | `V2.lean:54` (`Atom.eq`/`Atom.ne`) is the same atom the automatic channel carries; the checker decides conjunctions of it |

## Red — empty

*No row. A specification that says what no Gabbro program can state is a
failure (§7/E3): either the Gabbro side comes first, or the fragment is
taken back. The guardian fails on any `RED` row.*

## Yellow — empty, with the reason written down

*§7 ordered exactly one yellow row: `PredArt::Erreicht`. Measured
2026-09-09 it is carried for the whole population (row `reachesIn`
above), so no yellow row stands. The residual shape condition is not a
row: outside the fitting shape — ends that do not resolve to slots of
one counted table (`lean.rs:1108`, `slot_index`) — the channel still
refuses with `LeanReason::Quantified` (`lean.rs:339`). No population row
ends there; should one appear, it becomes yellow with an `OFFEN.md`
entry, and the guardian demands the entry.*

## Demands — not rows, and that is the mechanism

*`V1.lean`'s `bedarf` block names three means the fragment must still
adopt. None of them is a table row, because no specification can be
written in them through any tool — each stands in exactly one place, as
a labelled demand. They get rows when their Gabbro side lands, and the
Gabbro side lands first; that order is what keeps red empty:*

| Lean demand | Gabbro side | State |
|---|---|---|
| `LEAN countD` | `GABBRO count` | `DEMAND` — `count` is a reserved word (`kw.rs:265`) with no `pred`/`expr` production; §7.3 builds the Gabbro side first, no new source word |
| `LEAN firstD` | `GABBRO traverse` | `DEMAND` — «B10»: `traverse` yields no value and knows no `break`; a different loop form, booked not built |
| `LEAN reachesIn` | `GABBRO Erreicht` | `GREEN` — carried for the population (row above); the unrolling-vs-closure cost question stands in `OFFEN.md` (`O6`) |

*The guardian checks this section too: every `DEMAND` name on the
Lean side resolves in `V1.lean`, every one on the Gabbro side in the
Gabbro sources — a demand that names nothing is not a demand.*
