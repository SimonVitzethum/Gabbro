# S2 environment design — discharging U1 and U2

*Design for step S2 of `dokumente/PLAN-SICHERHEIT.md` section 4. S1 is built;
this file builds nothing. It records the induction shape, the wiring through
`contract_of_duty`, and the falsifier that keeps the theorem honest.*

## 1. Goal and acceptance condition

Today the callee behavior is a premise: `UmgebungOK` says every declared
callee keeps the world well formed and answers per its signature, and
`SchleifenOK` says every registered loop keeps the world and its scope.
`exec_sicher` assumes both.

S2 counts when both premises are theorems instead of assumptions:

| premise today | theorem after S2 | source of the duty |
|---|---|---|
| `UmgebungOK P Gamma rho` | `umgebung_ok_of_runs` | `pruefeBlock_sicher` per body, lifted over the call graph |
| `SchleifenOK P Gamma rho` | `schleifen_ok_of_runs` (loop half of the same induction) | `pruefeBlock_sicher` exit rows over `iterate` |

The statement is given once over a `Programm` with a body table
(name maps to body, signature, measure), not once per routine. The
checker side (`pruefeBlock_sicher`) supplies the per-body duty; the
model side (`Body.lean` section on recursion) supplies the lifting.
No person writes an induction over the call graph.

## 2. Inputs S1 already provides

| item | location | role in S2 |
|---|---|---|
| `Runs rho f body` | `Body.lean`, environment answers with the final state and value wherever the body ends | connects a body run to the environment entry |
| `contract_of_duty` | `Body.lean`, a duty over the body is the contract under `Runs` | the wiring, see section 4 |
| `Below`, `ContractBelow`, `contract_of_duty_rec` | `Body.lean`, self recursion | one routine calling itself, induction over its own `decreases` |
| `BelowM`, `ContractBelowM`, `contracts_of_duties_rec` | `Body.lean`, mutual recursion over `Member` | a cycle of any size, one induction over the common bound |
| `RecursionCycleCarried`, `recursion_cycle_carried` | `Coverage.lean` | the same cycle shape as a carried property of the checker |
| `RunsLoop`, `iterate`, `looprule_of_body` | `Body.lean`, loop passes as index lists | the loop half, induction over the index list |
| `pruefeBlock_sicher`, exit rows | `Sicherheit/Anweisung.lean`, running, returned, exited, left | the duty for each body, including loop exit shapes |
| `K008` / `K009` | checker, recursion carries a `decreases` term | the evidence the induction needs at each cycle member |

## 3. The induction — `umgebung_ok_of_runs`

### 3.1 The program table

Fix a program `P` with, per routine name: a body, a signature, and an
optional measure expression. Fix an environment `rho` with `Runs rho f
body_f` for every member. The claim is `UmgebungOK P Gamma rho`:
for each declared callee, from a world in `Welt`, the answer keeps
`Welt` and matches the signature. The proof goes by case over the call
graph of the bodies.

### 3.2 Acyclic part — induction over the topological order

Where the call graph below a routine is acyclic, order the routines so
that every callee precedes its callers. Prove the contracts in that
order, innermost first:

1. A leaf (no callees) meets its duty directly: `pruefeBlock_sicher`
   on its body gives the post state and the shaped answer, and
   `contract_of_duty` turns that duty into `Contract rho f pre post`
   under `Runs`.
2. A caller whose callees already carry contracts meets its duty the
   same way, with each call site closed by the already proved callee
   contract (the U1 hypothesis at that site is now a theorem, not a
   premise).
3. The `Welt` half travels with the same steps: stores go through
   `Welt_store`, which needs only the checker side, so no extra
   induction is owed for it.

Nothing here needs a measure. The induction is over the graph order,
and it is well founded because the graph fragment is finite and acyclic.

### 3.3 Cycles — `Below` plus `decreases`

A cycle cannot use the order above: no member precedes the others.
Each cycle member must therefore carry a `decreases` expression, and
the induction is over the measure, not over the graph:

- Self recursion: the duty may assume `ContractBelow rho f e t pre
  post`, the contract on states strictly below the current one in
  `Below e`. `contract_of_duty_rec` lifts that bounded duty to the
  full contract by induction over the natural bound. The person
  proves the body duty; the induction lives in the model once.
- Mutual recursion: the duty of each member `r` may assume
  `ContractBelowM rho r_prime r.measure t` for every member
  `r_prime` of the cycle — the contract of each member bounded by
  the caller measure through `BelowM`. `contracts_of_duties_rec`
  lifts all bounded duties to all contracts of the cycle at once,
  which is exactly what `recursion_cycle_carried` states as a
  carried checker property in `Coverage.lean`.

The load bearing point is the comparison inside `BelowM`: the
callee measure at the callee state against the caller measure at
the caller state. Members of one cycle may name different
expressions, and the induction needs them on one common bound
(the `key n` generalization in `contracts_of_duties_rec`). A
cycle whose members cannot be placed on one bound is not carried
by this induction, and the theorem must say so rather than
assume it.

### 3.4 Loops — induction over the index list

Per loop: induction over the `iterate` index list, using the
`exited` and `left` rows of the statement safety theorem (those
rows exist for this purpose). Each pass preserves `Welt` and the
scope under the invariant; `leave` ends the visitation early and
`iterate` returns the state as is. Recursion through a loop body
uses `contract_of_duty_rec_loop_in`: the induction over
`decreases` runs outside the loop rule, so the pass may assume
the bounded self contract while the loop rule handles the passes.
A routine whose body mixes a loop with a recursive call owes both
inductions, nested in that order.

## 4. `contract_of_duty` wiring

One theorem per call shape, each turning a proved body duty into the
environment contract the call sites need:

| call shape | bounded duty the body owes | lifting theorem | assumed contract at call sites after S2 |
|---|---|---|---|
| plain call, acyclic callee | post state plus shaped answer from `pruefeBlock_sicher` | `contract_of_duty` under `Runs` | proved callee contract, by graph order |
| self recursive call | duty under `ContractBelow` | `contract_of_duty_rec` | bounded self contract, discharged by measure induction |
| call into a cycle | duty under all `ContractBelowM` of the cycle | `contracts_of_duties_rec` via `recursion_cycle_carried` | bounded member contracts, discharged together |
| call under a loop | duty with loop rule over `iterate` | `looprule_of_body` plus duty lifting | `SchleifenOK` half, by index induction |
| recursive call inside a loop body | duty under `ContractBelow` with loop rule inside | `contract_of_duty_rec_loop_in` | bounded contract outside, loop rule inside |

The emitter instantiates these per unit. The shape each site needs
is fixed; only the body duty is per program.

## 5. Falsifier shape — a call cycle without `decreases` must refuse

The theorem is allowed to conclude contracts only where the evidence
exists. The probe that keeps it honest is a corpus unit with a call
cycle and no `decreases` on at least one member edge:

- Checker side: `K008` / `K009` refuse the unit. That refusal is the
  existing behavior the theorem rests on.
- Model side: the bounded duty premise (`ContractBelow` /
  `ContractBelowM` for that edge) cannot be discharged, so the
  corresponding contract is not concluded. The statement must make
  the `decreases` evidence a premise of the cycle case, never a
  silently assumed hypothesis.
- Negative direction: drop the `decreases` premise from a scratch
  copy of the cycle case and the proof must fail (open goal, not an
  admitted one). A theorem file with no such probe is undamageable,
  not covered.

Two further probes belong to the same family and should travel with
the build: a self recursive routine whose measure does not fall on
the recursive call (the `Below` side condition stays open), and a
two member cycle whose measures share no common bound (the `BelowM`
comparison stays open). Each must refuse on both sides.

## 6. Work items and known risks

1. Common bound across a cycle. `BelowM` compares two different
   expressions at two different states. The induction generalizes
   over one natural bound; members with incomparable measures need
   either a lexicographic or product construction or an explicit
   refusal. This is the sharpest open point of the design.
2. Foreign bodies. `extern`, `asm`, and entrusted routines have no
   body and hence no duty; their contracts stay hypotheses on
   `rho`, exactly as `PLAN-VERIFIKATION` section 2.3 records. S2
   must thread those hypotheses through, not close them.
3. Loop plus recursion nesting. The order is fixed (measure
   induction outside, loop rule inside); the reverse nesting is
   not covered by `contract_of_duty_rec_loop_in` and must refuse.
4. `Welt` across environment answers. The world preservation half
   of `UmgebungOK` at a call site needs the callee contract to
   carry `Welt`, not only the answer shape. The per-body duty
   already yields both; dropping either half reopens the call.
5. Statement over a program table. `Runs`, `BelowM`, and the member
   list must be read off one table so that the cycle a proof
   closes is the cycle the checker refused or accepted. A second
   register over the same graph is the failure class this folder
   writes against.
