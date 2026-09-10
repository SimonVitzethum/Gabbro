# S2 loop design — discharging SchleifenOK over RunsLoop and iterate

*Design draft for step S2 of dokumente/PLAN-SICHERHEIT.md, section 4. Status on
2026-09-10: drafted, not built. Base: commit 291c27b (S1 baseline, program
safety theorem over the sequential core).*

## 0. What this step has to show

After S1, `exec_sicher` carries two premises about the environment that are the
same theorem one level down:

| premise | definition | what it promises |
|---|---|---|
| U1 UmgebungOK | Anweisung.lean:520 | every declared callee keeps the world well-formed and answers per its signature |
| U2 SchleifenOK | Anweisung.lean:528 | every registered loop keeps the world and its scope |

S2 discharges both from the wiring `Body.lean` already provides — `Runs` (the
environment runs the body) and `RunsLoop` with `iterate` (the environment runs
the loop as a sequence of passes). This draft covers the loop half (U2); the
call half (U1) is sketched in section 5 because it fixes the induction
principle the loop half reuses. S2 counts when both premises disappear from
`exec_sicher` and return as theorems (`umgebung_ok_of_runs`,
`schleifen_ok_of_runsloop`), stated once over a program with a body table.

## 1. The pieces, with the lines they stand on

| piece | file and line | role in the induction |
|---|---|---|
| Outcome exited, left | Body.lean:1211, Body.lean:1213 | a pass ends by falling off, by next, or by leave |
| step loop arm | Body.lean:1329 | a loop entered with a true invariant answers with the environment state |
| exec | Body.lean:1357 | stuck is an outcome of its own, never a running state |
| iterate | Body.lean:1415 | one pass per index in ks, loop variable bound to it |
| RunsLoop | Body.lean:1429 | the environment state equals the end of some index sequence |
| Ergebnis exited, left rows | Anweisung.lean:661, Anweisung.lean:662 | both carry WFU of the entry scope |
| pruefe loop arm | Anweisung.lean:370 | registered scope must equal the current one, invariant must be bool, body must check |
| LogikS invariante | Anweisung.lean:473 | the only ground loop case today: invariant false on entry |
| logik_grundfaelle | Sicherheit.lean:132 | names every pass-through constructor, so a new one fails loudly |

## 2. Why the exited and left rows carry the entry scope

A block only ever adds names (U3 in PLAN-SICHERHEIT.md), so everything a loop
body binds is invisible past the loop — `namen.rs` refuses any later read.
`Ergebnis` books exactly that: `running` carries WFU of the scope after the
statement, while `returned`, `exited` and `left` carry WFU of the scope at
entry (`Δ0` in Anweisung.lean:657). The two loop rows were put there for this
step, and the induction below uses them at every pass boundary:

- a pass that ends `running` or `exited` continues with the tail of the index
  list; the state satisfies WFU of the entry scope by the `exited` row, so the
  induction hypothesis applies unchanged;
- a pass that ends `left` stops the loop (`iterate` discards the remaining
  indices at Body.lean:1422), and the final state already satisfies WFU of the
  entry scope by the `left` row — no weakening step needed.

Without those two rows the induction would have to weaken each pass result
back to the entry scope by hand; with them the pass boundary is free.

## 3. The induction over the index list

Claim (`schleifen_ok_of_runsloop`): for a loop `id` with
`P.schleife id = some Δ`, `schluss … inv = some .bool` and
`pruefeBlock P erg Δ body = some _`, if `RunsLoop ρ id body v` holds then
`ρ id` keeps `Welt` and `WFU Δ`.

Proof shape, by induction on the index list `ks` that `RunsLoop` provides:

- Base (`ks = []`): `iterate` returns the entry state unchanged
  (Body.lean:1416), which satisfies both by assumption.
- Pass (`k :: ks`): bind `v` to `k` and run the body. Apply
  `pruefeBlock_sicher` to the pass state. Its `Ergebnis` gives four cases:
  `running` and `exited` continue the induction over `ks` (section 2);
  `left` ends it; `stuck` yields `LogikB` in the body and is lifted to the
  loop by the new `rumpf` constructor of section 4.

The world half travels with `Welt_store`-style preservation at every store
inside the pass; the scope half travels with the `exited` and `left` rows.
Neither half needs a new invariant: the loop rule already says the invariant
is preserved, and entry is the caller side (the `step` loop arm gets stuck on
a false invariant, which is the `invariante` ground case).

## 4. The new LogikS constructor for a body that gets stuck

Today a loop contributes exactly one ground case to `LogikS`: `invariante`
(Anweisung.lean:473). A pass that gets stuck inside the body has nowhere to
go — the induction of section 3 needs a pass-through constructor so that
stuck-in-body stays inside the own-logic predicate instead of escaping the
theorem:

```
| rumpf {id inv body s v k} :
    eval s inv = some (.bool true) ->
    LogikB ρ body { s with local' := bindLocal s.local' v (.int k) } ->
    LogikS ρ (.loop id inv body) s
```

Consequences, both intended:

- `logik_grundfaelle` (Sicherheit.lean:132) must gain a seventh disjunct for
  the loop-with-stuck-body shape. Until it does, the theorem fails — loudly,
  not silently — which is the documented purpose of stating it as a theorem.
- `exec_sicher` keeps its shape (`stuck` implies own logic): a loop whose
  callers invariant holds and whose body gets stuck now reports the body site
  instead of falling outside `LogikB`.

## 5. The call half (U1), for the shared induction principle

Per routine `f` with `Runs ρ f body_f` and an accepted body,
`pruefeBlock_sicher` gives that `ρ f` keeps `Welt` and answers per signature —
provided every callee inside does (U1 for them). That is a fixpoint over the
call graph: induction over the topological order for an acyclic graph; for a
cycle, `K008` and `K009` supply `decreases`, which makes the induction
well-founded on the measure — the same shape `Coverage.lean` uses in
`recursion_cycle_carried`. Falsifier: a corpus unit with a call cycle and no
`decreases` must be refused by the theorem, not assumed away.

## 6. Open points this draft does not close

| point | status |
|---|---|
| pass-entry binding of the loop variable | the induction needs WFU of the entry scope extended with v bound to an integer; whether pruefe guarantees that binding is an open proof obligation (adapter A1 in the S4 notes) |
| which indices a domain yields | RunsLoop quantifies over every sequence; RunsLoopIn and RunsLoopN narrow it, and which indices a domain yields is the domain's business, not this file's |
| termination of the pass sequence | a loop is rho id and its passes are the environment's business; forever_laeuft_ewig stands |
| fault classes of Finding 1 | an out-of-range index reads in this model instead of failing; S3 moves that to a fault outcome independently of this step |

## 7. Acceptance

`UmgebungOK` and `SchleifenOK` no longer appear among the premises of
`exec_sicher`; `umgebung_ok_of_runs` and `schleifen_ok_of_runsloop` are proved
(0 sorry, only propext, Classical.choice, Quot.sound); the theorem is stated
once over a program with a body table; `logik_grundfaelle` names the new
constructor; the three one-line mutations of PLAN-SICHERHEIT.md section 2
still fail against the changed checker.
