# V-clocks: what the pairing pass orders today, and what it does not

Lane 137 measurement note, 2026-09-11, base `6f26e76`. Read-only over
`paarung.rs`, `geteilt.rs` (H012/H005), `nebeneinander.rs`, `aufrufgraph.rs`,
`kosten.rs`, `namen.rs`: nothing outside the three gift probes below and this
note was touched. The checker owns no clock word; this note uses **clock** for
one thing only: *the happens-before edge a rule relies on when it stays
silent*. A V-clock is a release/acquire pairing edge, a W-clock the
interference edge the concurrency pass assumes (common lock, paired payload,
machine-ordered atomic). The remainder is the set of edges neither pass names.

## 1. V003-hint-only: the skip is wider than the doubt

`V003` fires when a function with an **incomplete** call hull publishes
something (`paarung.rs:249-264`): a hint, then `continue` -- `V008`,
`V004`/`V005` (relaxed payload), `V010` (foreign writer), `V001`/`V002`
(orphaned halves) never run for that function. Measured today:

- The trigger needs a non-empty publish set; an incomplete hull that only
  awaits gets no hint and its `V002` runs against a lower-bound global set.
- The skip is per-function but the sets are global: `alle_publiziert` /
  `alle_erwartet` (`paarung.rs:205-212`) still contain the undecidable
  function's halves, so an incomplete function silently redeems a complete
  function's orphan (and vice versa). The doubt does not propagate.
- A relaxed-only publish on an incomplete hull takes the other road:
  `relaxed_mit_last` never reaches `publiziert`, so no `V003` fires and
  `V004`/`V005` speak normally.
- `V006`/`V007` (order) and `V009` (missing pairing) run outside the skipped
  loop and are unaffected by it.

**Pin:** `beispiele/gift/758-v003-hint-skips-orphan-check.gab`
(`-- erwartet: Hinweis V003`). `kreis` recurses under `decreases`, publishes
an orphaned `{ m }` on `G`: exactly `Hinweis V003` plus the honest companion
`Hinweis E009`. The twin (`mw`/`mr` on `F`) is the same pairing with a
complete hull and must stay silent. `V003` has no probe until this one
(`saetze.rs`, `paarung.keine-waise`: "`V003` is a hint and has none").
Measured finding set: exactly those two hints, no errors.

## 2. H012-nesting: one position repaired, its neighbour not

`H012` (rank order through the callee's hull) and `H005` (exclusive `Held`
through calls) are checked in `geteilt.rs`: `block` (`:1425`) walks
statements, `rufprobe` (`:1592`) checks one call, `rufprobe_expr` (`:1693`)
walks expressions. Covered today: direct statement calls, `let`/`return`/
assignment sources, `wenn` conditions, index expressions (the `gift/179`
repair), `aligned`/index-only `sizeof`/`lenof`, and `let-else` -- whose source
is only ever a direct call or a place (`LetQuelle`, `ast.rs:1224-1229`), so
`als_ruf` misses nothing. Blind today, by reading:

- **Measured:** a call nested in the argument of a statement-level call.
  `StmtArt::Ruf(r) => rufprobe(r, …)` (`geteilt.rs:1508`) never descends into
  arguments, while the graph edge exists (`aufrufgraph.rs:789`, `nimm_ruf`
  recurses into direct call arguments) and the expression twin
  (`rufprobe_expr`) walks them. Same principle as `gift/179`, one position
  further out. `H005` rides along: an exclusive `Held` demand in the nested
  call is equally invisible.
- **Read, not run** (owner-lane pins): the `match` subject (`MatchStmt`,
  never passed to `rufprobe_expr`), the `traverse` object and `decreases`
  measure (`eigene_ausdruecke` names them, `block` has no arm), the
  `retry … until` and exchange-`when` predicates (calls in predicates exist --
  `PredArt::Vergleich`, the `tu() == 9` finding -- but `block` never reads
  `eigene_praedikate`), the `narrow` place (an `Ort`, so an index call fits,
  no arm), the `publish` value, an index call on an `await` source, and the
  `count … : pred` predicate (`ExprArt::Zaehle`, the `_` arm of
  `rufprobe_expr`; `Held` inside it is read by other passes, calls are not).

**Pin:** `beispiele/gift/759-h012-call-in-statement-argument-silent.gab`
(`-- erwartet: H012`). Verdict carrier `falsch` (the `gift/142` shape), pinned
hole `loch` (`senke(lies_l1())` under held `L2`, silent; `senke` re-takes `L2`
itself so the hole isolates the argument position and nothing else),
must-pass twin `aufsteigend` (the same nesting ascending, allowed). Measured
finding set: exactly one `H012` (the direct call); the nested inversion and
the twin stay silent. A first draft fired a companion `H007` (`senke` wrote
the protected `b` lock-free); the shipped shape takes `L2` around its own
write, rank-equal and silent by construction.

## 3. W-clocks: three edges modelled, the fourth assumed

`W001`/`W002`/`W003` (`nebeneinander.rs`, sentences `nebeneinander.*` in
`saetze.rs`) model exactly three happens-before edges: a lock standing in
BOTH hulls (pair-level, `:115-117`), a `publishes` payload pairing (`:121`),
a machine-ordered atomic carrier (`:127-133`). Closed world over
entry/boot roots (`W002`, `:337-383`), fail-closed on incomplete hulls and
unresolvable members (`W003`, `:211-227`, `:256-278`). Remainder:

- **Measured:** the pair-level lock exempts without a site. A common
  `locks L` returns *no overlap at all* before any place is compared
  (`ueberlappung`, `:115-117`) -- open question 1 (held-set analysis,
  `:30-32`). Two bodies sharing `L` around unrelated work race silently on
  every write outside it.
- **Read, not run:** `per cpu` cells fall unless lock-shared although
  disjoint by core (open question 3, `:33-35`, false-positive direction);
  `entrust` roots are skipped, not cleared (open question 2, `:36-37`);
  same-table different-place writes fall unless lock-shared (interim over
  open question 4, `:136-158`, conservative direction, pinned by `gift/704`).

**Pin:** `beispiele/gift/760-w001-pair-level-lock-exempts-uncovered-write.gab`
(`-- erwartet: W001`). Verdict pair `h`/`k` (shared write, no common lock),
pinned pair `f`/`g` (same overlap, `L` in both hulls around unrelated `Y`
writes, silent). Only `W001` may fall; no entry/boot roots, so `W002` stays
out by construction. Measured finding set: exactly one `W001` (the `h`/`k`
pair); the `f`/`g` pair stays silent.

## 4. V012: assigned free, NOT implemented

`V012` occurs nowhere in the tree (no `.rs`, `.py`, `.md`, `.gab`, `.lean`
hit on 2026-09-11) -- the identifier is free, and it stays free after this
lane. The minimal safe candidate is specified, not built:

- Candidate: the 759 hole lifted to a refusal -- either `H012` extended into
  statement-call arguments, or a `V012` narrow rule for exactly that
  position. The probe already carries its must-fall shape and its twin.
- Why not built here: the edit belongs to the `geteilt` owner lane; a new
  refusal needs its sentence in `saetze.rs`, its corpus lists (`korpus.rs`,
  `paesse.rs`) and its guardian bookings (`pruefe-vergabe.py`,
  `pruefe-zahlen.py`) -- a surface this lane may run exactly one suite of
  (`beispiele`). A refusal that fires nowhere today is dead code; one that
  fires somewhere unseen is churn. The pins make the future diff trivial and
  the re-measurement exact.

## 5. Re-measurement

Lane budget, the only command run:

```bash
CARGO_BUILD_JOBS=4 cargo test -p gabbro-check --test beispiele
```

At merge the owning lanes owe the full surface this lane could not run
(`korpus`, `paesse`, `rechenwerk`, `einheit`, `pruefe-emission.sh`,
guardians) plus two register lines the new files move by construction:
`DONE.md:1562` and `README.md:163` say `500 poison probes`; with
758/759/760 the tree holds 503. The number moves here, the register follows
at merge -- one writer per register, no lane edits it alone.
