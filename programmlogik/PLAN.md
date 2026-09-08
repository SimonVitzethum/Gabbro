# The plan: a person proves only their own logic

**Status 2026-09-08.** This file holds the whole plan behind the Lean channel of Gabbro
(`programmlogik/`), from the question it answers to what is still open — so that the next
step can be taken from the file and not from memory. It is written as the plan is executed:
every claim below is a measurement over the corpus (`beispiele/` + `messung/`, 189 units),
and the number next to it says when it was measured.

The one sentence the plan serves: **a person who wants to verify a Gabbro program formally
proves their own logic, and nothing else.** Everything that is not their logic — how calls
compose, how a loop carries its invariant, that the world is well-typed, what shape an
answer has, that a number stays in its declared range, which branch an `if` takes, what a
`match` on a `tagged` value can see, that a chain does not notice a store beside it, the
arithmetic the checker already decided — is carried by the model, the emitter, or the
automation. Where it is not carried it is either **named as an assumption** (with a name a
proof can point at) or **refused** (with a tag that says why). It is never left in the
person's lap silently.

---

## 1. What "own logic" means, and what it does not

**Own logic** is what the person wrote and only they can know: an `ensures` that follows
from what the body does; an `invariant` that survives a pass because of what the pass
changes; a `requires` strong enough for the body; a `reaches`-chain that is still intact
after a relink because of which fields the relink touched. If a proof needs the person to
say *why* the program is right, it is their logic.

**Plumbing** (Klempnerei) is everything a person would write by hand in Lean *before* they
get to their argument, and which is the same for every program:

| plumbing | what a person had to do before | who carries it now |
|---|---|---|
| a call | open the callee's contract, prove its precondition, rewrite the answer | `Contract`, `Frame`, `gabbro_calls` |
| a call in an expression | reason about an evaluation with a side effect | the emitter hoists it (`hoisted_call`) |
| a call chain | repeat the above per link, innermost first, with the answer rewritten | `gabbro_calls` rounds + goal rewrite |
| a loop | build the loop rule from the pass | `looprule_of_body`, `looprule_of_body_in`, `RunsLoopIn` |
| recursion | induction over `decreases` | `contract_of_duty_rec`, `contracts_of_duties_rec` (cycles) |
| the well-typed world | prove every store keeps `WF` | `WF_store`, `gabbro_wf`, `Shape.intIn` |
| a read of the world | produce a witness `σ p = .int n` | `WF_int`/`WF_intIn`/`WF_bool`/`WF_sum`/`WF_opt`, `gabbro_shape` |
| a declared range | prove `0 ≤ n ≤ 255` from the type | `Shape.intIn` in `shapeOf`, ranges in `_pre`, `hasShape_intIn_true` |
| a `tagged` value | know the cases and their payload ranges | `Shape.sum cases`, `Shape.caseOk`, `Shape.payloadOk` |
| an answer | know it has the declared shape and range | `result_clause` in every `_post` |
| an answer without shape | know it exists at all | `∃ v, r = some v`; `gabbro_values` splits it |
| control flow | split on every `if`, `match`, comparison | `gabbro_cases` |
| a store beside a read | decide same place / other place | `gabbro_split`, `store_here/elsewhere`, `bindLocal_*` |
| a store beside a chain | prove `reaches` is unchanged | `chase_store_field/carrier/global/fieldPlace` |
| arithmetic the checker did | `x & 251 ≤ 255`, `a*b ≤ A*B`, `0 ≤ a/b ≤ a` | `gabbro_bits`, `gabbro_mul`, `gabbro_divmod`, `omega` |
| a quantified premise | instantiate `∀ k < N` at the index in play | `gabbro_instantiate`, `gabbro_forall` |
| hypotheses in shapes | open `∧`, `∃`, `∨`, `hasShape`, `caseOk` | `gabbro_open`, `gabbro_open_hyps` |
| budget | a step that runs away takes the theorem down | `gabbro_try` (real heartbeat budget, restored on failure) |

**Not own logic, but not plumbing either — the named assumptions** (§6): the contract of a
foreign body, a device's promise, a `walk` clause, the initial state, and the correctness of
the checker and the emitter. These are not proved and not hidden.

**Explicitly out of scope:** formal verification of Gabbro itself (the checker, the
emitter, the model against the C the emitter writes). The plan is about what a *user* of
Gabbro proves.

---

## 2. The architecture: four layers, one file per layer

```
unit.gab ──► gabbro pflichten --lean ──► Duty/<Unit>.lean ──► lean ──► GREEN / OWED / RED
                (crates/gabbro-check/src/lean.rs)      ▲                (gabbro prove)
                                                        │
                                       programmlogik/Gabbro/Body.lean (the model + tactics)
                                       programmlogik/Proofs/<Unit>.lean (the person's file)
```

**The model** (`programmlogik/Gabbro/Body.lean`, Lean 4.33, no Mathlib): `World`, `State`,
`Value`, `Shape`, `Expr`, `Stmt`, `exec`/`step`/`eval`, the contract algebra (`Contract`,
`Frame`, `LoopRule`, `Runs`, `RunsLoop`, `RunsLoopIn`, `Below`, `ContractBelow`, `Member`,
`ContractBelowM`), the typing (`Typing`, `WF`, the `WF_*` witnesses), the `chase` chain with
its frame lemmas, and §7: the tactics. It builds without `sorry` at every commit.

**The emitter** (`crates/gabbro-check/src/lean.rs`): reads the checked tree and writes one
Lean module per unit — the typing `shapeOf`, every routine's body as a `Stmt` list, its
`_pre`/`_post`/`_writes`/`_requires`, every loop's `_inv`/`_body`, every foreign contract as
an assumption, the invariants, and one theorem per duty (`_meets` for a routine, `_keeps` for
a loop pass), each with generated **openings** (witnesses for every parameter and every read
the body makes, the hypothesis itself as rewrites) and `gabbro_auto`. It also writes the
**wiring** (`unit_closed`): from `Program ρ` and the duty statements, every contract and loop
rule of the unit, including the recursive ones. What it cannot say it **refuses with a tag**
(`LeanReason`), and the register (`pflichten.rs`) prints the tag next to the duty.

**The checker and the CLI** (`crates/gabbro-check/src/beweis.rs`, `crates/gabbro-cli`):
`gabbro prove|beweise [--template|--vorlage] [--model|--modell <dir>] <unit.gab>…` writes
`Duty/<Unit>.lean`, builds the model with `lake`, compiles the duties, and holds
`Proofs/<Unit>.lean` against them: GREEN (every statement proved, no `sorry`), OWED (which
statements), RED (a Lean error), SETUP (no Lean, no model) — exit 0/1/3 (2 is the
unknown-command exit of the CLI). `--template` writes the file a person starts from.
`gabbro emit --proved|--mit-beweis` refuses C for a unit that still owes a proof.
`instrumente/pruefe-lean-pflichten.sh` runs it tree-wide.

**The measurement** (`programmlogik/_pruefung/`, scratch, not committed): `lauf.sh` runs every
module of the corpus through `lean` (P at a time) and writes one line per file — errors,
`sorry`s, seconds; `probe.sh <module> [theorem]` shows what `gabbro_auto?` leaves. The
numbers in this file come from there.

---

## 3. What was built, layer by layer

### 3.1 The model

- **Calls.** `Contract ρ f pre post` (`∀ t, pre t → post t (ρ f t).1 (ρ f t).2`), `Frame ρ f
  writes` (a place outside the frame is untouched, as a rewrite `Frame_read`). A call reads
  its answer through the projections `(ρ f t).1/.2`, never through a pair-`match`.
  `bindCallElse` on `none` binds `.absent` and continues.
- **Loops.** `RunsLoop` and `RunsLoopIn ρ id body v lo hi` (the environment runs the passes
  with the index in range); `looprule_of_body`/`looprule_of_body_in` build the `LoopRule`
  from one pass. A loop over `slots of T` gets `0 ≤ k < count`; over `elems of`/`queue` the
  range that covers both readings of the binder (index or element).
- **Recursion.** `Below e t' t` (the measure decreases), `ContractBelow` (the self-contract
  below the measure), `contract_of_duty_rec` — one induction in the model. **Mutual
  recursion:** `Member`, `BelowM`, `ContractBelowM`, `contracts_of_duties_rec` — a cycle of any
  length, one induction over the shared measure; the emitter finds cycles (SCC) and wires
  them.
- **Shapes.** `Shape.int | bool | opt | intIn lo hi | sum cases`. `intIn` is the declared
  range of a place (a field `u8 in 0 .. 15`, a global, a payload, a local, an answer):
  `WF_intIn` gives a read its bounds; a store into such a place owes them (`gabbro_wf`
  with `omega`). `Shape.sum` carries its cases with their payloads: `none` (no payload),
  `some none` (a number), `some (some (lo, hi))` (a number in range) — `Shape.caseOk` and
  `Shape.payloadOk` compute on a literal case list, and a `match` over a `tagged` value never
  gets stuck on a case the type excludes.
- **`andBool`/`orBool`** for `&&`/`||`: a true conjunction splits into two halves
  (`andBool_true_iff`) even when one half stays symbolic.
- **`hasShape` computes on a constructor and stays folded on a variable** (the
  `Value.hasShape_*_*` simp equations); `Value.hasShape_*_true` turn a shape fact into a
  witness (with bounds for `intIn`, with case and payload for `sum`).
- **`chase`** (the `reaches` chain with exact fuel), `chase_refl` (a chain reaches where it
  starts), and the **frame lemmas** `chase_store_ne`, `chase_store_field`,
  `chase_store_carrier`, `chase_store_global`, `chase_store_fieldPlace`: a store into another
  field, carrier, global or record field leaves every chain as it was.
- **`store_here/store_elsewhere`, `bindLocal_here/bindLocal_elsewhere`** as simp lemmas;
  `shape_int`, `shape_intIn`, `shape_bool`, `shape_opt`, `shape_sum` (a local's witness from
  the precondition).

### 3.2 The tactics (`Body.lean` §7)

`gabbro_auto [lemmas] using Γ` = `gabbro_pipeline [lemmas] using Γ; all_goals sorry`;
`gabbro_auto?` prints what is left. The pipeline, every step under its own budget:

1. `gabbro_simp` — the model's simp set (`exec`, `step`, `eval`, `binop`, the shape
   equations, the store lemmas) with the caller's list.
2. `gabbro_cases 4` — the program's control flow: `by_cases` on every closed `decide p`, `if`
   condition, boolean read and boolean variable, at most 4 deep; the decision written as
   `decide p = true/false` *explicitly* (a `simp` that has to see through the `Decidable`
   instance was measured to miss it); a condition already decided — also in its normalised
   form (`¬ a < b` as `b ≤ a`) — is not split again.
3. `gabbro_calls Γ` — every `ρ f t` the goal mentions against every `Contract`/`LoopRule`/
   `ContractBelow`/`ContractBelowM` hypothesis, **innermost first**, 12 rounds, per instance
   guarded; the precondition closed by `gabbro_wf` and the simp set (`Below` by `omega`);
   the instance simplified into rewrites and opened; a mark `gabbro_seen : c = c` per goal
   so a second pass does not repeat it; **and the goal rewritten with the answer at once**
   (with the binding and store lemmas), because the next call outward sits under a `match`
   on this one's answer and is not collected until that `match` is gone.
4. `gabbro_values` — an answer without a shape (`∃ v, r = some v`), split by its
   constructors; then `gabbro_simp_hyps`, `gabbro_calls`, `gabbro_values`, `gabbro_calls`
   again (a chain of shapeless answers).
5. `gabbro_open_hyps`, `gabbro_simp_hyps`, `gabbro_forall` (a `allBelow f n = some true`
   premise proved from the context), `gabbro_cases 3`, `gabbro_simp_hyps`.
6. `repeat' apply And.intro`, `intros`, `gabbro_wf Γ`, `gabbro_shape Γ` (a witness for every
   read `σ p` in goal and hypotheses, skipping the witnessed), `gabbro_simp_hyps`,
   `gabbro_cases 3`, `gabbro_calls`, `gabbro_forall`, `gabbro_simp_hyps`, the conjunction
   split, `intros`, `gabbro_wf`, `gabbro_shape` — twice, because each round opens the next.
7. `simp [lemmas, *]; done`, `gabbro_split` (a read against a store: statically different
   places without a split, else `by_cases` on the place with the hypothesis read as an index
   equation), `gabbro_instantiate` (an invariant at the index in play), `subst_vars`.
8. From here **without the caller's list** (`simp_all` clears a hypothesis it used up, and a
   vanished name in the list fails the step): `simp_all`, `gabbro_shape`, `gabbro_wf`,
   `gabbro_cases 3 []`, `simp_all`, `gabbro_split`, `gabbro_instantiate`, `simp_all` — twice;
   `gabbro_wf`, `gabbro_divmod`, `gabbro_mul`, `gabbro_bits`, `omega`.

Total budget of the pipeline ≈ 11.3 M heartbeats; the emitter's header carries
`set_option maxHeartbeats` at that sum.

### 3.3 The emitter

- Contracts before duties (mutual recursion references forward); `_decreases` definitions;
  `ContractBelow` for self-recursion, `ContractBelowM ρ ⟨name, body, requires, post,
  decreases⟩ f_decreases s` for cycle members; `wiring_order` with SCC detection;
  `unit_closed` wires `cyc_i := contracts_of_duties_rec ρ [...]`.
- Parameter ranges in `_pre` (`.hasShape "n" (.intIn lo hi)`); a loop variable shadows the
  range of its name; a `let` of a ranged type carries its range in every invariant in scope
  (`shape_conjunct`), so the answer computed in a loop can meet its own range.
- `shapeOf` with `.intIn` for ranged fields, globals, record fields; `Shape.sum` interned
  per case list with payload ranges.
- Arrays as pseudo-tables (`Rec.field`, static arrays): places, assignments, `elems of`,
  `queue` (also `queue T.slots[i].f` through `field_records`), `lenof`.
- `aligned(e, n)` = `e % n == 0`; device carriers → `LeanReason::DevicePromise`
  (assumption); opaque newtypes carry the shape of their underlying type; statics, `atomic`,
  `accumulates`, unvalued constants in `shapeOf`; record fields by type name
  (`.field "Text" "len"`).
- Calls hoisted out of expressions (`match f(a)`, `if f(a)`, `let x = f(a)+1`, `g(f(a))`,
  `return f(a)+1`, assignment) — not under `&&`/`||`.
- Result clause in every `_post`: `∃ x, r = some (.int x) ∧ lo ≤ x ∧ x ≤ hi`, the bool, sum
  (with `caseOk`), option forms, `∃ v, r = some v` for an answer without a shape (a token, a
  record), `none ∨ reason` for an error channel without a value, `False` for `-> never`;
  `#ret` carries its shape (with range) through a loop.
- Openings: `hall` (a copy of the hypothesis simplified into rewrites), witnesses for every
  read (`WF_int`/`WF_intIn`/…), `int_lit` for negative literals, `_pre`/`_inv` in the simp
  set.

### 3.4 The checker and the CLI

`beweis.rs`: `Stand {Gruen, Geschuldet, Rot, Aufbau}`, `Befund`, `modell_finden`,
`lean_binaer`/`lake_binaer` (`$LEANBIN`/`$LAKE` or `~/.elan/bin`), `pruefe(baum, datei,
modell)`, `vorlage` (the template). CLI: `prove|beweise`, `--template|--vorlage`,
`--model|--modell`, `emit --proved|--mit-beweis`; the flag and subcommand registers
(`fahnen.rs`, `erstnamen.rs`) know the names, English first. `cargo test --no-fail-fast`
green (the field-shape test knows `.intIn`).

---

## 4. The measurement

Corpus: 189 units, 502 theorems (264 `_meets`, 49 `_keeps`, 189 `unit_closed`). Register:
175 duties — 90 carried as Lean goals, 72 assumed by name (40 device promises, 20 walk
clauses, 12 foreign bodies), 13 refused forms (9 quantifiers over `fields of` / `threads` /
`mappings of` / a membership, 2 carriers that are not tables, 2 layout built-ins).

*After run 24 the corpus is 190 units and the register 177 duties — 93 carried, 72 assumed,
**12** refused under six tags instead of one (§9.1).*

**Runs 24 and 25 were worked in two trees and each measured against run 23.** The merged
tree is measured in §11, and its number is neither of theirs.

`sorry` left to the person, per run (0 Lean errors in every run since the model was
sealed):

| run | sorry | what changed |
|---|---|---|
| first | 195 | the channel as of 2026-09-06 |
| — | 169, 111, 97, 65, 56, 52, 51 | recursion, shapes, cases, calls, splits, ranges of parameters |
| 16 | 91 | **stricter obligations**: ranged answers from field reads — the model had no ranges yet |
| 17 | 53 | `Shape.intIn` in the world, `∃ v` for shapeless answers, `chase_refl`, `gabbro_divmod`, `gabbro_wf` after late witnesses |
| 18 | 38 | payload ranges in `Shape.sum`, `subst_vars`, call chains rewritten in `gabbro_calls` |
| 19 | 35 | ranged locals, `gabbro_mul`, `queue T.slots[i].f` |
| 20 | 33 | late `gabbro_cases` round, explicit `decide` equations, flipped inequalities |
| 21 | 32 | `gabbro_values`, `chase` frame lemmas |
| 22 | 29 | `gabbro_bits` (`&&&`), arithmetic facts also from hypotheses (`planer` closes) |
| 23 | 28 | `^^^`/`\|\|\|` bounds in `gabbro_bits` (`udp-echo/falte` closes) |
| 24 | 29 | the refused forms split into six tags, one of them CARRIED, and recursion inside a loop wired (§9) — the one more `sorry` is a duty that was refused before |
| 25 | 23 | `passes`, the pass counter (§10) — five counter units close |
| **merged** | **24** | runs 24 and 25 in ONE tree (§11) — 190 modules, 0 errors, 343 s |

The count went *up* once (16) on purpose: every obligation the model did not carry before
(a declared range) was added to the statements first, and then carried.

---

## 5. What is left, and whose it is

Measured with `probe.sh` (`gabbro_auto?`) on run 21. Each entry: the unit, the theorem, the
goal that stands, and the verdict — **own logic** (the person's argument, or their
specification), or **gap** (plumbing this plan still owes, with the step that closes it).

### 5.1 Own logic — the person's argument

- **`beispiele/01-tabelle`** (4), **`messung/fragmente/F01`** (4), **`messung/caprock/kapraum`**
  (3), **`beispiele/55-kindkette`** (1): a `reaches`-invariant preserved across a relink.
  The frame lemmas peel every store *beside* the chain; what stands is the store *into* the
  chain field (`naechstes_geschwister = None`, `elter = Some p`) and the person's argument
  that the chain from the root still reaches every node — the invariant of a linked
  structure. In `55` the fourteen goals that stand all read
  `chase (store σ (slot "Kappraum" k "naechstes_geschwister") absent) …`.
- **`beispiele/56-auftragsring`** (1): distinctness over ring slots; the precondition does
  not say the new element `i` is fresh, and the statement is not provable as written — a
  **specification** to sharpen (`requires` that `i` is not in the ring).
- **`beispiele/19-traversierung`** (1), **`beispiele/46-verneinung`** (1),
  **`messung/proben/probe-suchschleife-passfach`** (1), **`messung/proben/probe-elems`** (1),
  **`messung/fragmente/F06`** (2), **`messung/netz/udp-echo`** (1): a counter or a sum
  in a loop whose invariant does not bound the next step — `n ≤ 16` does not give
  `n + 1 ≤ 16`, `summe ≤ 65535` does not give `summe + 1 ≤ 65535`, `s + w ≤ 2^32−1` from
  `s ≤ 2^32−1`. The invariant the person needs is `n ≤ k` (the index), or the sum bounded by
  the passes so far. *The checker accepts these bodies; how it decides the range of a counter
  incremented in a loop is the checker's business, not this plan's (see §1: no verification
  of Gabbro itself).*
- **`beispiele/09-ohne-zeiger`** (3): the invariant `∀ s, Kappenraum.slots[s].benutzt` is
  broken by `benutzt = false` in the body — the goals are `False`; a **specification**
  problem of the example (an invariant that cannot survive its own routine).
- **`messung/proben/probe-neun-domaenen`** (4): empty bodies with an `ensures`
  (`forall s : k.slots[s].marke == 0`, `forall x in chain(…) : elter == Some(p)` after doing
  nothing) — the syntax probe's, not the model's; the chain goals read `chase s.world …`
  over an untouched world, and nothing in the body makes them true.
- **`beispiele/gift/642`** (1): a forever loop in a function that answers — a poison example
  the checker refuses; its duty is `False` by construction.

### 5.2 Gaps — plumbing still owed (in order)

**After run 23 every `sorry` in the corpus is in §5.1.** What follows is not measured as a
`sorry` but is known to be missing:

1. **Counters in loops** (§5.1, six units): not a gap of the model but a candidate for a
   *convenience*: bind the pass index as a ghost local (`#pass`) in every `traverse`, so a
   person can write `n <= #pass` — the model would then carry `#pass < count` from
   `RunsLoopIn`. **BUILT 2026-09-08 as `passes`, not `#pass` — §10**; five of the six units
   closed, and the surface is a plain identifier, not a token.
2. **Refused forms** (13 → **12**, and one tag became six — §9.1): quantifiers over
   `fields of`, `threads`, `mappings of`, a membership (`x in …`); a carrier that is not a
   table; the layout built-ins (`sizeof`,
   `lenof` over a buffer). Each needs a model domain it does not have. They stay refused
   with their tag; a refusal is not a `sorry`.
3. **Recursion inside a loop** (~~not wired~~ **WIRED 2026-09-08 — §9.3**): the loop's
   contract and the routine's self-contract in one induction. No corpus unit had the shape,
   so it is measured on a probe (`messung/proben/probe-rekursion-in-schleife.gab`); three
   other shapes keep their refusal and now name which.
4. **`gabbro_calls` and hole goals** (measured, not fixed — the change is written and NOT
   built, §10.5): a precondition hole opened for an inner call does not see a hypothesis
   added by a later instance; the innermost-first order
   and the per-goal marks make it rare, not impossible.

### 5.3 What a person does

```
gabbro prove --template unit.gab > programmlogik/Proofs/Unit.lean   # the file to start from
# … replace `all_goals sorry` behind `gabbro_pipeline […] using shapeOf` by the argument …
gabbro prove unit.gab                                                # GREEN / OWED / RED
gabbro emit --proved unit.gab                                        # C only when green
```

The template holds the generated openings and the pipeline; what is left when the person
opens the file is what §5.1 describes for their unit, and nothing from §1's table.

---

## 6. The assumptions, by name

- `Assumed ρ` per unit: every **foreign contract** (`extern fn … ensures`), every **device
  promise** (a register read or write behind `transition`), every **walk clause**.
- `Initially s0`: the initial state — a well-typed world in which every invariant holds.
- Two carrier names are two places (no aliasing between declared carriers); a record type
  is one object of the model.
- The checker's decisions the model repeats only where it must (ranges, shapes); the checker
  and the emitter are trusted, not verified (§1).

---

## 7. Measured on the way — what bit, and where it is written down

- `set_option maxHeartbeats … in` inside a tactic block does **not** change the limit the
  check reads → `gabbro_try` sets `Core.Context.maxHeartbeats` and `withCurrHeartbeats`;
  a plain `try` does not catch a heartbeat exception → `tryCatchRuntimeEx`.
- A nested `by` in a `have` **logs** its failure as an error of the theorem instead of
  throwing → `GabbroMeta.haveClosed` with `?_` holes closed by the tactic.
- `isDefEq` outside the goal's context → "unknown free variable" → `withContext`.
- A hole goal opened early does not see hypotheses added later → innermost-first call order,
  per-goal marks.
- `simp_all` clears a hypothesis it used up (`hall`) → the late rounds run without the
  caller's list; user-named hypotheses are opened on copies.
- A call under a `match` arm has a loose bound variable and is not collected → the answer is
  rewritten into the goal in the same round (`gabbro_calls`), with the binding lemmas.
- A `¬ a < b` becomes `b ≤ a` under `simp_all`, and the same `decide (a < b)` is then split
  again → the flipped form counts as decided; the decision is written as an equation.
- `Shape.sum` without cases: a `match` on a payload-less case stayed stuck → the shape carries
  its cases (a soundness point of the obligation, not only convenience).
- `rsync -a` vs `cargo`, `pgrep -f` finding itself, a measurement that stops at the first hit
  — see `CLAUDE.md`; they apply to this channel's measurement scripts as well
  (`lauf.sh` never stops at an error, it counts).

---

## 8. The next steps, in order

1. Decide on `#pass` (§5.2 item 1) with the owner — it is a language question.
2. A second corpus (Caprock's units beyond `planer`/`kapraum`) to find the next plumbing
   class; every class so far surfaced from a `sorry` a person could not have been asked for.
3. Keep `Body.lean` without `sorry` and `cargo test --no-fail-fast` green at every commit;
   commit through `arbeitsprotokoll/.commitmsg` + `./commit.sh`; the measurement scratch
   (`programmlogik/_pruefung/`, `Duty/`, `Proofs/` from test runs) stays out of the tree.

---

## 9. Run 24 — the refused forms, and recursion inside a loop (2026-09-08)

`PLAN.md` §5.2 items 2 and 3, from the emitter's side. Every number below is
`_pruefung/lauf.sh` over the corpus regenerated from the emitter of this change, and
`cargo test --no-fail-fast` in the container.

| | before | after |
|---|---|---|
| modules | 189 | **190** (one new probe) |
| Lean errors | 0 | **0** |
| `sorry` | 28 | **29** |
| register: duties | 175 | 177 |
| carried as goals | 90 | **93** |
| assumed by name | 72 | 72 |
| **refused forms** | 13 | **12** |

### 9.1 The refused forms (item 2), measured one by one

The thirteen were `quantified` (9), `carrier-not-a-table` (2), `builtin` (2). **One tag
stood over forms whose grounds and whose ways out differ**, so the register told a reader
neither. They are now six tags, and one of the thirteen is carried:

- **`fields of <format|record>` — CARRIED.** The field list is declared and finite, so the
  quantifier is a finite conjunction; where the body does not read the binder — every use
  in the corpus — it collapses to the body (`true`/`false` for an empty list). A body that
  DOES read the binder stays refused (`quantified`): a field NAME is not a value of this
  model. Effect: `probe-neun-domaenen`'s `d6_fields` moved from *refused* to a goal.
- **`threads` → `quantified-threads`.** Every other domain hangs on a declaration
  (`count N`, `tree { … }`, `walk … levels`, the one field array of a record); `threads`
  hangs on nothing, so there is no index domain to cut. `beispiele/57-faedenhalt` says the
  same thing in its own header. **A language change, not a model change.**
- **`mappings of <walk>` → `quantified-mappings`.** Hardware — the same object a `walk`
  invariant speaks about, and those are ASSUMED by name.
- **`carrier-not-a-table` split in two.** `beispiele/21-verbundwert` is a field of a record
  VALUE (`let c = fertig(k, 7); c.len`) → `record-value`; the model's places are named by a
  record TYPE, and a binding has none. `messung/proben/probe-ipc-fastpath-durchgestochen` is
  `e.slots[core].receivers.buf[i]`, an array inside a record held in a SLOT →
  `slot-record-array`. **The second is refused for soundness, not for effort:** a record
  type is one object of this model, so every slot's copy would be the same place, and a body
  writing two slots' queues would be modelled as writing one.
- **The layout built-ins stay refused, and the ground is measured, not assumed.**
  `lenof(puffer) >= sizeof(Elf64Kopf)` (`beispiele/03-format`, `messung/grammatik/messreihe`)
  fails at `lenof` first → its own tag `layout-buffer-length`: nothing declares that buffer's
  length. `lenof` over a fixed-length array **was already carried** (the length stands in the
  declaration). And `sizeof(T)` has no number to give: **the C emitter refuses it by name for
  exactly this reason** (`emit.rs`, *"`sizeof(T)` would have to agree with the layout the
  checker computed, and that agreement is not established anywhere"*). A number here would be
  a layout claim Gabbro itself declines to make.

### 9.2 A refusal that is INHERITED now says so

`duty_1 N kopf_lesen :: ensures #1 — refused (builtin)` sent a reader looking for a built-in
in an `ensures` that has none: the clause is fine, the routine's `requires` is not. Two
chains were found by measuring, and both are printed now:

- a clause refused because the ROUTINE's body or `requires` has no term;
- a `table` invariant refused because one routine that WRITES its carrier has none — and in
  `probe-stellungen` the writer's own text does not mention the culprit either: the routine
  inherits `s8_threads` because it writes `Knoten`, and one untranslatable invariant on a
  table refuses **every** routine that writes it (there: five duties, from one `threads`).

### 9.3 Recursion inside a loop (item 3) — wired, and measured

**No corpus unit had the shape.** Both `NOT WIRED` notes in the corpus
(`beispiele/41-handschlag`, `probe-transport-warteschlange-aufsetzen`) read *callee refused*.
A wiring nobody measures is a wiring nobody has, so the shape is now a probe:
`messung/proben/probe-rekursion-in-schleife.gab` (checker: 0 errors).

The step is `Gabbro/Body.lean` §8, `contract_of_duty_rec_loop_in`: the induction over
`decreases` runs OUTSIDE the loop rule, so the pass may assume `ContractBelow ρ f e s0 …`
at the ROUTINE's entry state `s0` — and **owes in return that the measure has not moved**
(`eval t' e = eval s0 e`, carried across the passes in the loop's state predicate beside the
well-typed world). Without that second half the bound would be about a state the loop has
already left, and the assumption would be vacuous. Afterwards the loop's own rule follows
from the finished contract (`contractBelow_of_contract`).

Measured on the probe: **0 errors, 0 `sorry`** — `f_loop_1_keeps`, `f_meets` and
`unit_closed` all close, and `unit_closed` yields both the loop rule and the contract.
One emitter line was needed for it and it is written down: the measure equation has to be
opened with `.symm` (`have hmeas' := hmeas.symm`); the other direction rewrites the
parameter's witness into `s0.local' "n"` everywhere and the pass stops computing.

The step is written for **one ranged loop with nothing nested in it**. Three other shapes
keep their refusal and now name which: several loops, a `retry`/`forever` pass (no index
range to induct over), a nested loop.

### 9.4 The one `sorry` that came back, and why it is not plumbing

28 → 29, and the difference is `probe-neun-domaenen`'s `d6_fields`: a duty that was
**refused** is now a **goal**, and what stands is `x = 0` for `Knoten.slots[0].marke` after
an empty body — the same class as the four `sorry`s that file already had (§5.1: *empty
bodies with an `ensures`, the syntax probe's, not the model's*). It cannot be carried
because it is not true of the program. The same shape as run 16: an obligation the channel
did not state before is stated first, and the count says so.

---

## 10. The pass counter — `passes` (agent b, 2026-09-08)

**§5.2 item 1 is built and measured.** A person may write `n <= passes` over a `traverse`,
and `passes` is the number of passes already done.

### 10.1 Why it needed the model and not only a word

`n <= NSLOTS` is true of every run of `19-traversierung` and **unprovable as a loop
invariant**, and no tactic could ever close it: `LoopRule` quantifies over EVERY state the
invariant admits, so a pass that starts at `n = NSLOTS` has to be handled, and `n + 1 <=
NSLOTS` is false there. The sentence that survives a pass is `n <= <passes so far>`, and for
it to be sayable two things had to be added:

- **`#pass`, a ghost local.** The emitter binds it to `0` one `bindName` before the loop and
  makes the increment the pass's own first statement (so a `next` or a `leave` in the middle
  cannot skip it). Nothing of it reaches the generated C.
- **A bound on the NUMBER of passes.** `RunsLoopIn` says every index is in the domain's
  range and says nothing about how often the body runs — and without that no invariant can
  bound a counter. `RunsLoopN ρ id body v lo hi np` adds `ks.length ≤ np`, with `np` the
  domain's `count`. **This is a stronger assumption about the environment than `RunsLoopIn`,
  and it is the sentence `by unvisited` makes**: each slot is visited at most once, so a
  traversal of a table of `count N` runs at most `N` passes. It is assumed, as `Runs`,
  `RunsLoop` and `RunsLoopIn` are assumed (§6), and named here.

Model: `RunsLoopN`, `LoopRuleP ρ id wf inv pv` (the same conclusion as `LoopRule`, from a
state whose counter stands at zero — where the emitter puts the loop), `looprule_passes_aux`
and `looprule_of_body_p`. `gabbro_calls` knows `LoopRuleP`'s third premise. No existing
definition or theorem of `Body.lean` changed.

### 10.2 The language surface

`passes` — a plain identifier, **no keyword, no grammar-table entry** (`pruefe-grammatiktafel.py`
green, 0 of 218 terminals uncovered; `pruefe-syntax.sh`, `-todo.py`, `-englisch.py`,
`-kennungen.py` unchanged). It is declared by a `traverse` for its `invariant` and by nothing
else, exactly as the traversal variable is (`domaene.rs::aus_block`, `D021`/`D017`), and a
**declared name of that spelling wins** — local, parameter, constant, global, type, table,
`walk` or head; the emitter asks the same seven questions (`lean.rs::passes_is_free`). Where
the loop cannot count (no `count` behind the domain) the emitter **refuses with the tag
`pass-counter`** instead of writing `passes` out as `.global "passes"` — the wrong proof
object `D021` exists against.

Alternatives considered: `#pass` (unlexable today — a new token, a grammar-table row and a
guardian update); a keyword `passes` (a reserved word costs every program that already uses
it). The chosen surface costs nothing to a program that does not write it.

### 10.3 Measured

Corpus of 189 modules, `_pruefung/lauf.sh` with `P=6`, Lean 4.33 on tux:

| run | errors | sorry | secs |
|---|---|---|---|
| before (run 23) | 0 | **28** | 493 |
| after | 0 | **23** | 509 |

Closed: `beispiele/19-traversierung`, `beispiele/46-verneinung`,
`messung/proben/probe-elems`, `messung/proben/probe-suchschleife-passfach`,
`messung/netz/udp-echo` — five of the six units of §5.1's counter paragraph. Their `.gab`
invariants now read `n <= passes` (`summe <= passes`, `s <= 65535 * passes`); the arithmetic
is `omega`'s once `0 ≤ #pass < count` is in the pass.

`messung/fragmente/F06` keeps its **2** — and they are **not** the counter: with
`invariant i <= passes` the range obligation of `i += 1` closes, and what stands is
`w_i * 8 ≤ s.len`, the file's own `ensures result <= s.len`. That is **own logic** (§5.1),
and §5.1's entry for F06 was half right: one half was plumbing, the other is the person's.

`cargo test --no-fail-fast`: 31 collections, 0 failed (4 new probes in
`crates/gabbro-check/tests/rechenwerk.rs`). `lake build Gabbro.Body`: green, no `sorry`.

### 10.4 A second finding, kept small on purpose

A loop that may `return` carries the invariant as `(#returned ∧ post) ∨ (¬#returned ∧ inv)`,
so in the flagged branch **the person's own conjunct is gone** and a store in the body cannot
meet its range — even though no pass follows a `return` (it desugars to `… ; leave`). The
emitter now guards such a body with `if #returned { leave }`, which makes the pass do what the
run does. **Measured over the whole corpus it is one more `ite` for `gabbro_cases` to split**:
applied to every `may_return` loop it closed `probe-elems` and opened
`beispiele/39-auftragsdienst` (net zero). It is therefore written **only where the loop counts
its passes** — where the conjunct that the branch drops is the one just introduced.
*The general case is open, and its cost is measured, not guessed.*

### 10.5 What this run did NOT measure

Two items of §5.2 were worked and are **not** reported as done, because the Lean machine
became unreachable in the middle of the run (`device_bash`: *"Workspace unavailable"*, from
10:00 on; the file system stayed readable, the shell did not come back).

- **Pipeline speed.** `gabbro_pipeline_b` (§7 of `Body.lean`) is `gabbro_pipeline` with every
  one of its fifty steps wrapped in `gabbro_timed`, which logs the step's wall time;
  `_pruefung/zeit.sh <module>` sums those per step over a file. It is in the tree and it
  built, and the numbers it exists to produce were not taken. What IS measured: on
  `messung/fragmente/F01` (64 s) `set_option profiler true` attributes **56.3 s to `simp`
  across 48 calls above the 500 ms threshold** — the single largest of them 9.35 s; and the
  floor is **0.88 s per module** for `import Gabbro.Body` alone (5 runs of an empty importing
  file, 4.4 s), i.e. ~166 s of the corpus's 509 s is startup and not proof.
- **`gabbro_calls` and hole goals.** The change is written and is NOT in the model: it stands
  as a patch beside it, unbuilt. Its shape: the holes a round leaves are collected, and when
  every instance of the round is in, the round's calls are instantiated a second time INSIDE
  each hole — a hole's context never receives the main goal's later `have`s, but it does hold
  the theorem's own contract binders, so the fact is derivable there. An instance whose own
  premises do not all close at once is rolled back, so a hole never spawns a hole. The
  minimal example that exhibits the order (two calls at the SAME state, the second's
  precondition being what the first's contract says about it) is written too, and unrun.

---

## 11. The merged tree, measured (2026-09-08)

Runs 24 (§9) and 25 (§10) were worked in two trees, each on top of run 23. **Neither of
their numbers is the number of the tree that carries both**, so it was taken, and not
inferred:

| | run 23 | run 24 alone | run 25 alone | **merged** |
|---|---|---|---|---|
| modules | 189 | 190 | 189 | **190** |
| Lean errors | 0 | 0 | 0 | **0** |
| `sorry` | 28 | 29 | 23 | **24** |
| seconds (P=6) | 493 | — | 509 | **343** |

`_pruefung/erzeuge-all.sh` regenerated all 190 modules from the merged emitter (0 refused
by the checker), `_pruefung/lauf.sh` ran them with `P=6` on `ki-pc-fisch-101`. **24 = 23 +
the one duty run 24 turned from a refusal into a goal** (`probe-neun-domaenen`'s
`d6_fields`, §9.4) — the arithmetic of the two runs holds across the merge, which is the
only thing a merged measurement can confirm and the reason it was taken.

Where they stand, all nine files, and every one is §5.1:

```
beispiele/01-tabelle             4     a reaches-invariant across a relink
messung/fragmente/F01            4     the same
messung/caprock/kapraum          3     the same
beispiele/55-kindkette           1     the same
beispiele/09-ohne-zeiger         3     an invariant its own routine breaks -- a specification
messung/proben/probe-neun-domaenen  5  empty bodies with an `ensures` -- the syntax probe's
beispiele/56-auftragsring        1     distinctness the `requires` does not give -- a specification
messung/fragmente/F06            2     `w_i * 8 <= s.len` -- the person's (§10.3)
beispiele/gift/642               1     a poison example; its duty is `False` by construction
```

**Not one `sorry` in the corpus is plumbing.** §5.2's list is what is missing, and nothing
on it is a `sorry`.

Beside the corpus, on the same tree: `cargo test --no-fail-fast` 31 collections, 422 tests,
0 failed; `lake build Gabbro.Body` green, no `sorry`.

### 11.1 A register that was one step behind, found in the merge

`LeanReason::PassCounter` (§10.2) was declared, tagged and returned by the emitter, and
stood in **neither** `LeanReason::ALL` nor `zaehle-lean.py`'s `GRUENDE`. A refusal under it
would have been counted in a module's balance line and named in no reason line — *smaller,
which is the direction that flatters.* `zaehle-lean.py`'s own comment describes the same
incident from 2026-09-01, one register over: **"the second register, one step behind the
first."**

The test that was supposed to hold `ALL` against the enum walked `ALL` and checked that
what stands there is not mute — true of a list that is missing a variant. *A test over a
register cannot take that register as its population.* It reads the enum out of `lean.rs`
now and holds every variant against the array; with `PassCounter` cut back out, it fails
and names it.

**Five tags, five sentences, one guard** — and the five other tags of §9.1 were missing
from `GRUENDE` too, where the tool would at least have said `UNKNOWN refusal reason` out
loud.

---

## 12. Hole goals, pipeline speed, and two more loop shapes (agent b, 2026-09-08)

`PLAN.md` §5.2 item 4, §9.5 and the rest of §9.3 — the three things run 25 worked and could
not measure, because the Lean machine went away in the middle of it. **Every number below is
`_pruefung/lauf.sh` over the corpus regenerated from the emitter of this change**, run
locally with `P=4`.

*Where it was run, and why:* `ki-pc-fisch-101` is unreachable (`ssh -o BatchMode=yes -o
ConnectTimeout=8 ki-pc-fisch-101 hostname` → *"Connection timed out during banner exchange"*
— the jump host, not the target). `free -g` beside every run: **31 GB total, 15–17 GB
available, 20 cores.** `CLAUDE.md` asks for that measurement next to a local run, and this is
it.

| | baseline (`ec71432`) | + hole phase | + two loop shapes | + `simp_all` memo | **+ the fourth `simp_all` dropped** |
|---|---|---|---|---|---|
| modules | 190 | 190 | 192 | 192 | **192** |
| Lean errors | 0 | 0 | 0 | 0 | **0** |
| `sorry` | 24 | 24 | 24 | 24 | **24** |
| seconds (Σ per module) | 455 | 459 | 422 | 417 | **396** |

*The last column was run twice on the same tree — **402** and **396** — and the pair is the
error bar: single-second differences between neighbouring columns are noise, and only the
190→192 column and the last one are outside it.*

The baseline is §11's merged tree measured again in a fresh worktree: **190 / 0 / 24**, the
same three numbers, at 455 s where `ki-pc-fisch-101` needed 343 s at `P=6`. The two new
modules are the two new probes; **the `sorry` count does not move anywhere in the table**,
and neither does the set of files it sits on — the same nine of §11, with the same counts.

### 12.1 `gabbro_calls` and hole goals (§5.2 item 4) — the order, and a closer that dropped its own success

The patch §9.5 says stands beside the model was not in the tree; it was written again from
the shape §9.5 gives, and the minimal example with it (`_pruefung/Thole.lean` — scratch, as
the rest of `_pruefung/` is).

**The shape.** A hole a round opens is a metavariable whose context is fixed at that moment;
the `have`s the round's LATER instances add go to the main goal and never reach it. Two calls
at the *same* state have the same `approxDepth`, so innermost-first does not order them —
and the second's precondition can be exactly what the first's contract says about that state.
The hole then stands for no reason but the order. So: **once every instance of the round is
in, the round's calls are instantiated a second time inside each hole** — the round's calls,
not the hole's own, because the precondition names the state and not the call that decides
it, and `collectCalls` over the hole finds nothing. An instance whose premises do not *all*
close at once is rolled back, so a hole never spawns a hole.

**Measured.** `Thole.lean` holds the same two contracts twice, once with the calls in each
order in the goal. With the hole phase disabled, one of the two leaves
`t.local' "n" = Value.int 1` — the fact the other call's contract states — and the other
closes; with the phase in, both close. *Which of the two orders is the bad one is decided by
`qsort` on equal depths, and that is the point: at the same state there is no order to be
right about.*

**And the hole closer was dropping its own successes.** Its first alternative reads
`simp only [...]; (try apply And.intro) <;> …`, and **where `simp only` closes the
precondition whole, `<;>` runs on no goals and errors** — so the alternative that had just
succeeded failed, and a precondition the model decides by itself fell through to the person.
`(fun _ => True) t` is the smallest instance, and it stood open in the minimal example
before anything else was changed. `(simp only [...]; done)` now stands first in both closers.

**Over the corpus: nothing.** 190 / 0 / 24 before and after. §5.2 called this shape *"rare,
not impossible"*, and the corpus is where it is rare — **the minimal example is the evidence
that it is possible**, and it is now green.

### 12.2 Pipeline speed (§9.5) — the numbers that were never taken

`_pruefung/zeit.sh` (and `zeitmulti.sh`, which does several modules and never stops at the
first) over a spread. Milliseconds, summed over a module's theorems:

| step | | `01-tabelle` | `F01` | `09-ohne-zeiger` | `kapraum` | `08-bereiche` | `33-rekursion` |
|---|---|---|---|---|---|---|---|
| s33 | `simp_all` | 7 054 | **43 805** | 9 100 | **13 107** | 25 | 6 |
| s37 | `simp_all` | **24 427** | 9 196 | **10 279** | 2 594 | 0 | 0 |
| s40 | `simp_all` | 6 528 | 9 003 | 3 526 | 1 884 | 0 | 0 |
| s45 | `simp_all` | **22 590** | 9 400 | 3 083 | 1 779 | 0 | 0 |
| | **the four together** | **60 599** | **71 404** | **25 988** | **19 364** | 25 | 6 |
| | whole pipeline | 86 060 | 122 208 | 37 810 | 58 370 | 11 198 | 2 288 |
| | **share** | **70 %** | **58 %** | **69 %** | **33 %** | 0 % | 0 % |

**The four `simp_all` steps are the pipeline**, on every module that costs anything; the next
largest step anywhere is `gabbro_calls` at 6.6 s (`kapraum`, s02), and on the cheap modules
(`08-bereiche`, `33-rekursion`) the four cost nothing at all because the pipeline closes long
before them. *No other step was cut, because no other step had a number.*

**Cut 1 — `simp_all` runs at most once per goal** (`gabbro_simp_all_once`). A tactic that
changes a goal makes a NEW metavariable; one that fails under `try` leaves the old one. So
"this goal has not moved" is exact, and it is the memo's key. A step the heartbeat budget cut
off records nothing — `gabbro_try` shares one budget over `all_goals`, so a goal left
untouched for want of budget must be reached again by the next step.

| step | `01-tabelle` | `F01` | `09-ohne-zeiger` | `kapraum` |
|---|---|---|---|---|
| s37 | 24 427 → 23 099 | 9 196 → **2 337** | 10 279 → 10 114 | 2 594 → **614** |
| s40 | 6 528 → **431** | 9 003 → **1 391** | 3 526 → **82** | 1 884 → **0** |
| s45 | 22 590 → 22 770 | 9 400 → **1 428** | 3 083 → **82** | 1 779 → **2** |
| whole pipeline | 86 060 → 76 850 | 122 208 → 113 112 | 37 810 → 32 646 | 58 370 → 55 827 |

**Cut 2 — the fourth `simp_all` is gone.** On `01-tabelle` the memo did NOT make it free:
its goals really had moved under steps 41-44, and it still cost 22.8 s. So whether it closes
anything was measured, not argued — the corpus was run without it: **192 / 0 / 24, and the
`sorry`s on the same nine files with the same counts**, 417 s → 402 s (396 s on the repeat),
`01-tabelle` 39 s → 27 s. *That is a statement about this corpus.* A step that closes nothing over 192 units is
not thereby a step that closes nothing; putting it back is one line, and a unit that needs it
says so with a `sorry` and not silently. `gabbro_pipeline_b` keeps the gap in its step names
rather than renumbering — **a measuring copy that renumbers measures a different pipeline
than the one it is a copy of.**

**What did not move: the floor.** §9.5's 0.88 s per module for `import Gabbro.Body` alone is
untouched, and at 192 modules it is ~169 s of the 396 — **43 % of the corpus is now startup**,
and the next speed step is that, not the pipeline.

### 12.3 Recursion inside a loop — two more shapes wired, one still refused (§9.3)

§9.3 named three refused shapes. **Two of the three were refused on grounds that do not
hold**, and the third holds:

* **Several loops, the call in one of them — WIRED.** *"the induction is written for a
  routine with exactly one"* was an over-refusal: a loop that does not hold the call needs
  nothing the induction has. **But refusing it hid a real obligation**, and the probe
  `messung/proben/probe-rekursion-zwei-schleifen.gab` found it on the first run: one goal
  stood in the routine's duty, `x = w_n` — the value of `n` after the FIRST loop against its
  value at the routine's entry. *A `LoopRule` says nothing about the locals*, so as far as
  the model knew, a loop in front of the recursive one could have moved the measure. It
  cannot, and each loop proves that of its own body: **every loop of the routine carries the
  measure now**, the innocent ones as `lp_<loop> : ∀ s0, LoopRule ρ id (fun u => wellFormed u
  ∧ eval u e = eval s0 e) inv`, built beside the contract and instantiated at the routine's
  entry state inside the induction. Probe: **0 errors, 0 `sorry`.**
* **A `retry`/`forever` pass — WIRED.** *"no index range to induct over"* — and **the
  induction is over the `decreases`, never over the index.** What a range buys is
  `lo ≤ k < hi` inside the pass, an assumption the pass RECEIVES; `looprule_of_body` builds
  the rule of a rangeless loop without one. The model needed one theorem,
  `contract_of_duty_rec_loop`, which differs from `contract_of_duty_rec_loop_in` in exactly
  which builder stands inside the induction. Probe:
  `messung/proben/probe-rekursion-in-retry.gab`, **0 errors, 0 `sorry`.**
* **A stack of loops — still REFUSED, and the ground is the real one.** Every loop on the way
  from the routine's body to the call would have to carry the measure, and their rules would
  have to be composed inside one another: the inner loop's rule is a hypothesis of the outer
  loop's pass, and the outer pass would have to hand the inner one a rule stated against the
  ROUTINE's entry state. **What the model would need:** a `contract_of_duty_rec_loop_in₂`
  that takes both passes and threads `s0` through both loop-rule builders — or, better, one
  theorem over a LIST of nested passes, which is the shape `contracts_of_duties_rec` already
  has for a cycle. The tag now says *"a loop of the routine holds another loop … the
  composition is written for a flat routine, not for a stack of rules"*, and a loop that
  counts its passes has its own tag beside it (its rule is a `LoopRuleP`, and the composition
  takes a `LoopRule`).

Both probes are in `korpus.txt`; the corpus is **192** modules. `cargo test --no-fail-fast`
carries all three shapes: the two wired ones assert the composition and — for the
several-loops one — that **every** loop of the routine owes the measure equation, and the
stack asserts the refusal by name.

### 12.4 Two measurement collisions, and both were the apparatus

* **`cargo test` and `lauf.sh` in one tree.** A corpus run reported **52 Lean errors**, all of
  them `object file '.lake/build/lib/lean/Gabbro/Body.olean' … does not exist`. `cargo test`
  runs `gabbro prove`, which builds the model with `lake` — and `lake` replaces the very
  `.olean` the running `lean` processes read. *Not a finding, a collision*, and the same class
  as `CLAUDE.md`'s `rsync` into a directory a mutation run is working in. The rule that
  follows: **`cargo test` and `_pruefung/lauf.sh` do not run in one tree at one time.**
* **A guardian run beside a corpus run.** `pruefe-zahlen.py` reported six findings of the form
  *"`H` steht als 1, der Lauf sagt 10"*; run again on the quiet machine, none of them is
  there. A guardian that shells out to a tool measures the machine as well as the tree.
### 12.5 The `retry` probe carried an unfalsifiable assumption, and an instrument said so

*Found in the merge, 2026-09-08.* The first version of
`messung/proben/probe-rekursion-in-retry.gab` gave its `retry` a `progress
jemand_zaehlt_hoch`, declared the assumption behind it, and wrote `falsifier
sonde_jemand_zaehlt_hoch` behind that. **There is no program of that name in the tree.** A
`falsifier` naming a probe that does not exist is an unfalsifiable assumption wearing a
falsifiable one's clothes — the class `dokumente/UNFALSIFIZIERBAR.md` is written for, and the
shape `messung/OFFEN-PRUEFER-UND-GRAMMATIK-2026-09-07.md` §1.5 states: *an unfalsifiable
assumption covers exactly as much as one carrying a probe.*

**`instrumente/pruefe-sondendeckung.py` caught it, and the way it failed is worth reading.**
The name pushed its count of probe names outside the register from 13 to `MARK_AUSSEN + 1`;
its own speech test then expected one finding and got two, said NO, and the run **aborted
before printing the six numbers `pruefe-zahlen.py` reads**. So the visible symptom was five
findings one register over, all of the form *"der Befehl druckt die Zahl nicht mehr … der
Suchweg ist ab"* — `pruefe-zahlen.py` went from **5 findings to 11**, and the six new ones
were all of that shape. *(The `6` some counts report is `grep -c BEFUND`, which also matches
the filename `messung/ORDNUNGSSTICHPROBE-BEFUND.md`; the delta of six is the same either
way, and it is the delta that is the finding.)* *The instrument's own header
describes the same accident from an earlier day, one word of a comment wide.* **A guardian
that aborts is a guardian whose silence reads like consent** — `CLAUDE.md`'s rule about a
measurement that stops at the first hit, in its third instance this week.

**The way out was neither a probe program nor a raised mark.** `MARK_AUSSEN` is the ratchet;
raising it to quiet the guard is the one move that destroys what the instrument is for. And
writing `sonde_jemand_zaehlt_hoch` would have been inventing a falsifier for a promise
**nothing in the file needs**: the `progress` clause is optional, and what ends this loop is
its own body — `stand = 1` is the first statement of the pass, so `until stand >= 1` holds
after one pass and nobody outside the program promises anything. *An assumption a file does
not need is an assumption a file does not state.* The clause and the `assume` are gone; the
loop's SHAPE, which is the whole point of the probe, is untouched, and the module is still
0 errors / 0 `sorry` under `contract_of_duty_rec_loop`.

Measured after the fix: `aussen` back to **13** against a `MARK_AUSSEN` of 13 (no instrument
file touched), `pruefe-sondendeckung.py` exit **0** with its numbers printed (`A_p = 0.1316`,
booked 5/38, floor 1/8), and `pruefe-zahlen.py` back to its **five** standing findings — and that
those five are the merge's and not this channel's was measured, not argued: this commit's
diff was stashed and the guard run on the pure merge state, where the same five stand beside
the six-strong cascade. *`probe-rekursion-zwei-schleifen.gab` was checked and not assumed: it
states no `assume`, no `falsifier` and no `progress`, and neither does
`probe-rekursion-in-schleife.gab`.*

## 13. Run 26 — the coverage theorem: "everything except own logic" as a proposition (2026-09-08)

*Numbered 13 and not 12 on purpose: §12 is held for the run worked beside this one, and a
number that two trees claim is a merge conflict in a document that is supposed to be a
record.*

The sentence at the head of this file was, until today, a **slogan**: a claim about the
channel that nothing in the tree could contradict. It is now a theorem in
`programmlogik/Gabbro/Coverage.lean`, imported by `Gabbro.lean` beside `Body.lean`,
**built with no `sorry` and no axiom beyond `propext`/`Classical.choice`/`Quot.sound`**.

### 13.1 What is a theorem here, and what could never be

**"The tactic closes it" is not a theorem.** Tactic success is a property of a RUN, and a
file that stated otherwise would be the worst thing this tree can produce. So the verdict
type carries `carriedByTactic` for exactly the forms whose only evidence is the corpus, and
`Discharges` is `False` for them — *the classification tells the truth about what was
proved, or the top theorem breaks.*

What IS a theorem: **§1's plumbing table, turned into general lemmas.** Every proposition of
`Coverage.lean` §5 quantifies over an arbitrary `Env`, an arbitrary `Typing` and an
arbitrary program of the shape in question. None of them is about a unit of the corpus.

### 13.2 The enumeration and the verdicts

`Form` has **45 constructors**, one of which carries the 42 variants of `LeanReason` —
**86 forms expanded**. `classify : Form → Verdict` is total by construction, and the count
is: **32 carried** (a general lemma), **2 carried by the automation**
(`arithmeticBounds`, `budget`), **6 assumed by name**, **4 own logic**, and the 42 refusal
reasons under their own tags (39 refused, 3 assumed — `foreign-body`, `device-promise`,
`walk-invariant`, the three `LeanReason::kind` calls `Assumption`).

### 13.3 The top theorems, and why the last one is not a tautology

```
carried_discharges  : ∀ f : Form, classify f = .carried → Discharges f
classify_total      : ∀ f : Form, classify f ≠ .unhandled
ownLogic_is_the_persons : ∀ f : Form, classify f = .ownLogic → IsOwnLogic f
nothing_of_the_language_is_left_to_the_person :
                      ∀ f : Form, origin f = .language → classify f ≠ .ownLogic
the_sentence        : ∀ f : Form, ¬ IsOwnLogic f →
                        classify f = .carried ∨ classify f = .carriedByTactic ∨
                        (∃ n, classify f = .assumed n) ∨ (∃ t, classify f = .refused t)
```

`IsOwnLogic` is a **definition written without mentioning `classify`**: the obligation's
text comes from a clause the person wrote (`origin f = .person`) and that clause is one of
`ensures`, `invariant`, `requires`, `reaches`. So `ownLogic_is_the_persons` is two
independent case analyses agreeing, and `nothing_of_the_language_is_left_to_the_person` is
the half a coverage claim usually skips: *no form whose statement the grammar fixes is
handed over.* Beside them: `every_refusal_has_an_emitter_tag` (a refusal names a tag
`LeanReason::tag` actually prints, and no tag is empty) and `every_assumption_has_a_name`.

### 13.4 What had to become a PREMISE, and the two theorems that say why

Two of the general lemmas are **false without a side condition**, and the side condition is
therefore a premise — which is a statement about the emitter and not a convenience of the
proof. Both negations are proved:

* `store_without_the_shape_can_break_WF` — `∀ Γ σ p v, WF Γ σ → WF Γ (store σ p v)` is
  FALSE. So `StoreCarried`'s premise (the stored value has the declared shape) is exactly
  the goal `gabbro_wf` is pointed at, and the emitter's side condition does real work.
* `a_contract_says_nothing_where_its_precondition_fails` — a `Contract` gives nothing at a
  state where its `pre` fails. So the `V` duty at a call site cannot be dropped, and the
  model is right to get STUCK at a call whose precondition does not hold.

**Three further premises were needed and are named where they stand:**

| lemma | premise | what it says about the emitter |
|---|---|---|
| `CallCarried`, `CallResultCarried` | `WF Γ s.world` at the call site | the caller carries the well-typed world; the callee's *precondition* is NOT a premise — `step` is stuck without it, so getting past the call establishes it |
| `CallChainCarried` | the inner callee's post carries `WF` back | every `_post` the emitter writes has that conjunct; without it the outer contract has nothing to stand on |
| `StoreBesideChainCarried` | the place written is not a link of this chain | a syntactic side condition the emitter decides — and a store INTO the chain is a relink, which is the person's own logic (§5.1) |

### 13.5 The two demotions, with their ground

* **`arithmeticBounds`** — `x & 251 ≤ 255`, `a*b ≤ A*B`, `0 ≤ a/b ≤ a`. What the model
  carries is the arithmetic's MEANING (`arithmeticSemantics`: C's truncation, the sign of
  `%`, a zero denominator, a negative operand, a mask, a shift — six theorems of
  `Body.lean` §3.2, re-exported). The BOUNDS depend on the person's declared ranges, and
  there is no theorem "every bound the checker decided follows"; `gabbro_bits`/`gabbro_mul`/
  `gabbro_divmod`/`omega` close them on the corpus and that is all the evidence there is.
* **`budget`** — the heartbeat budget (`gabbro_try`). A step that runs away takes the
  theorem down; that is an operational property of a run.

### 13.6 The guard, and what it does NOT cover

`Form` and `Reason` are hand-written mirrors of `lean.rs`. A mirror that drifts still
typechecks, and the theorem is then green and about a language that is not Gabbro — the
`W7`/`W16` class, and §11.1 is its most recent instance. `instrumente/pruefe-deckung.py`
holds them together: the **population** both ways, the **order** of `Reason` against
`LeanReason::ALL`, every **tag**, every **kind**, that every `Form` has an arm in `classify`
and `classify` no catch-all, and that every carried form has an explicit arm in
`Discharges`. Ten speech tests, both directions; an unreadable subject is an ABORT (`2`),
a divergence a finding (`1`).

**What it does not cover, and this half is the honest one:** *that `Form` is the whole
grammar.* The refusal half is mechanical because `lean.rs` names its refusals in one enum.
**The CARRIED half has no such enum** — the emitter decides to carry a form by writing a
term, at some fifty places, and there is no list to compare against. A form the grammar
admits, the emitter carries, and `Form` never names would pass every check. *Closing that
is a change to `lean.rs`, not to the guard.*

### 13.7 Measured

Local, `free -g` beside it (31 GB total, 15–17 GB available, 20 cores; `ki-pc-fisch-101`
unreachable at the session's start — the jump host).

| | before | after |
|---|---|---|
| modules | 190 | **190** |
| Lean errors | 0 | **0** |
| `sorry` | 24 | **24** |
| seconds (P=4, sum over files) | 424 | **427** (118 s wall, warm cache) |
| `cargo test --no-fail-fast` | 31 collections, 422 tests, 0 failed | **unchanged** |
| `lake build` | green | **green, `Coverage.lean` with no `sorry`** |

**The corpus does not move, and that is the point**: `Coverage.lean` adds a module beside
`Body.lean` and changes nothing the emitter writes. The generated modules import
`Gabbro.Body`, not `Gabbro`.

Guardians before/after: `pruefe-kennungen.py`, `-syntax.sh`, `-grammatiktafel.py` green
before and after; `pruefe-englisch.py` red before and after with the same finding count
(its instrument word total moved by the new file, which is a total and not a finding);
**`pruefe-todo.py` went from red to GREEN and `pruefe-zahlen.py` lost one finding** — both
because `README.md`'s guardian and instrument counters were **already one step behind**
(33 booked against 34 measured, `61 of 61` against `61 of 62`) and booking the new
instrument corrected them to 35 and `62 of 63`. Two of `pruefe-zahlen.py`'s remaining
findings moved their measured value (`messung/RUECKLAUFWERTE.md`, 57 → 58 and 349 → 352):
those are counts over `instrumente/` that any new instrument shifts, they were red before,
and re-dating that file's measurement is not this run's.

### 13.8 What this run did NOT measure

* **That the emitter writes the statements these lemmas assume.** Every proposition of
  `Coverage.lean` is about the MODEL. That an `_pre`/`_post`/`_inv` says what the `.gab`
  file says is the emitter's correctness, and §1 puts it out of scope by name
  (`Form.checkerAndEmitterTrusted`).
* **Points 1 and 3 of `messung/GRAMMATIK-VOLLSTAENDIG-2026-09-08.md` §0.** This file
  answers point 2 — the proof channel answers for every form — and says nothing about a
  form that MEANS NOTHING, nor about an obligation that vanishes on a rename.

---

## 14. The tree that carries runs 26–28, measured (agent b, 2026-09-08)

§11's rule again: **neither of the numbers of runs 26, 27 and 28 is the number of the tree
that carries all of them**, so it was taken. `_pruefung/erzeuge-all.sh` regenerated all 192
modules from the merged emitter (0 refused by the checker), `_pruefung/lauf.sh` ran them at
`P=4` locally — `ki-pc-fisch-101` still unreachable, `free -g`: 31 GB total, 18 GB available,
20 cores.

| | §12 alone | **merged** |
|---|---|---|
| modules | 192 | **192** |
| Lean errors | 0 | **0** |
| `sorry` | 24 | **25** |
| seconds (Σ per module) | 396 | **399** |

**25 = 24 + `beispiele/57-faedenhalt`**, and it is the one difference in the whole per-module
table — every other module's count is identical. It is the quantifier-domain run's, booked in
its own words: *"the quantifier domain meant nothing in all nine, and one corpus program was
leaning on it."* **The same shape as run 16 and as §9.4**: an obligation the channel did not
state before is stated first, and the count says so. *A `sorry` that appears because a
statement got stronger is not a regression, and the only way to tell the two apart is to name
the file.*

The three recursion probes of §12.3 are **0 errors, 0 `sorry`** in the merged tree, so the
composition survives the merge with the emitter changes of runs 26–28 in it.

---

## 15. Run 29 — `threads`: the surface was designed, measured, and NOT built (agent f, 2026-09-08)

`messung/GRAMMATIK-VOLLSTAENDIG-2026-09-08.md` §2.3 books `threads` as a missing grammar
line, and §9.1 above states the ground: *"every other domain hangs on a declaration; `threads`
hangs on nothing, so there is no index domain to cut. **A language change, not a model
change.**"* It is the largest single class in the register. This run designed the language
change, measured what it would buy, and **found that the obvious surface is a synonym** — so
it was not built. What was built instead is the objection that closes the last form of
`threads` which stated nothing.

*Local runs; `ki-pc-fisch-101` unreachable through the jump host all day, and `free -g`
stands beside every number: 31 GB total, 13–17 GB available, 20 cores.*

### 15.1 What `kontexte.rs` actually knows — measured first, because the design hangs on it

The 2026-09-07 census §8.1 found a premise claiming Gabbro *"does not say who runs
concurrently"* refuted by `kontexte.rs`, which has printed a context count since 2026-08-19.
**If the execution contexts already fixed the thread set, the language change would be far
smaller than §9.1 assumed.** So it was measured before anything was designed:

```bash
for f in $(git ls-files 'beispiele/*.gab' 'messung/proben/*.gab' | grep -v gift); do
  ./target/debug/gabbro kontexte "$f"; done | grep -oE 'contexts: [0-9]+' | sort | uniq -c
#   112  contexts: 0
#     3  contexts: 1
#     2  contexts: 2      -- SEVEN contexts in the whole corpus, in FIVE files
```

The five are `07-eintritt-und-boot`, `11-grammatikbefunde`, `57-faedenhalt`,
`59-eintritt-nimmt-maskierte-sperre`, `60-annahme-mit-maschine`. And `Kontext`
(`crates/gabbro-check/src/kontexte.rs`) carries exactly six fields: `name`, `wurzel` (the
`dispatch` root), `modul`, `nie_verschachtelt`, `maskiert_verschachtelt` and `unterbricht`
(`via idt`).

> **A context is an `entry` — a static entry point — and a thread is a runtime object.**
> `erhebe` walks the items and pushes one `Kontext` per `ItemArt::Entry`; there is no other
> source. So the census's refutation stands and is *narrower than it reads*: Gabbro says which
> **entry contexts** exist, and says nothing about how many threads run. **§9.1's ground
> survives the measurement it was most likely to fail.**

The nearest thing to a declared concurrency cardinality is `accumulates … per cpu N` (one cell
per core, `ast.rs::AccDecl::pro_kern`, five sites in `05-nebenlaeufigkeit` and
`23-akkumulatoren`). **A core is not a thread** — `57-faedenhalt` declares 128 threads *and*
per-cpu stacks in one file — and no `accumulates` in the corpus stands beside a thread table.

### 15.2 The class is six duties and two clauses — the register counted the wrong noun

```bash
for f in $(git ls-files 'beispiele/*.gab' 'messung/proben/*.gab' | grep -v gift); do
  ./target/debug/gabbro pflichten --lean "$f"; done | grep -cE 'refused \(quantified-threads\)'
#   6
```

Six duties, and **four of them are the inherited refusals of §9.2**: `probe-stellungen`'s
`Knoten` carries one untranslatable invariant (`s8_threads`), and that refuses `s1_slots`,
`s2_chain`, `s3_descendants` and `s4_ancestors` along with it — each prints its own
`(inherited: this invariant HAS a term; …)` line. **The class is two clauses**:
`probe-stellungen::s8_threads` and `probe-neun-domaenen::d8_threads`. *A refusal class counted
in duties is four fifths one clause, and the largest class in the register was the smallest
change hiding behind an inheritance rule.*

### 15.3 The design, and why the obvious surface is a decoration

Every other domain hands the model a **number**. That is visible in the emitted term, not
inferred:

```bash
./target/debug/gabbro pflichten --lean beispiele/57-faedenhalt.gab | grep forallSlots
#   … (.forallSlots "t" 128 (.bin .ne (.place "Faden" (.name "t") "zustand") …))
```

`slots of Faden` becomes `.forallSlots "t" 128 …`, and `128` is the table's `count NFAEDEN`.
`Body.lean` declares the constructor as `forallSlots (v : String) (count : Int) (body : Expr)`
— **the domain of a quantifier in this model IS an integer.**

| | surface | what it emits | cost to a program that does not write it | verdict |
|---|---|---|---|---|
| **A** | `forall t in threads over Faden : …` | `.forallSlots "t" 128 …` | nothing (`over` exists) | **synonym** |
| **B** | a mark at the table (`table Faden … is threads`), bare `threads` resolves to it | `.forallSlots "t" 128 …` | nothing (`threads` is already a contextual keyword, `kw.rs`) | **synonym** |
| **C** | delete `threads` from the grammar | — | breaks four probe files | a terminal fewer, no meaning gained |
| **D** | `threads` = the LIVE slots: a liveness predicate at the declaration | a **second** constructor beside `forallSlots`, carrying `live` | nothing | **means something — and Gabbro has no liveness** |

**A and B pass the `passes` test of §10.2 and fail the completeness predicate.** They cost a
program nothing, they need no new terminal and no grammar-table row — and they make
`forall t in threads : P` the same index set, the same proposition and byte-identical C as
`forall t in slots of Faden : P`. That is a **synonym**, and a synonym is exactly the *"form
that means nothing"* of `GRAMMATIK-VOLLSTAENDIG` §1. *Buying six duties with a word that
changes no term is buying them with the same silence the domain already had.*

**D is the surface that would mean something**, and it is the one this run declines to invent.
`forall t in threads : Faden.slots[t].zustand != LAEUFT` should quantify over the threads that
EXIST, not over 128 slots most of which are free — that is what the sentence in
`57-faedenhalt` is trying to say, and it is a strictly different proposition. It needs a
declaration of which slots are live, a model constructor that carries it, and a decision about
what liveness means while a slot is being created or torn down. **Gabbro has never made that
decision, and a semantics nobody asked for is not a result.** The refusal stays, with a
measured ground.

### 15.4 What WAS built: `D024`, the last form of `threads` that stated nothing

Between `D022` (the binder used as a place or an index) and `D023` (the body never mentions
the binder) sat one shape nothing read, and it was **green against the checker of `6c835eb`**:

```bash
printf 'module p::tp {\nconst N : u32 = 8;\ntable Faden count N {\n slot {\n  zustand : u8,\n }\n}\nspec fn alle_klein() -> bool\n = forall t in threads : t < N;\n}\n' > /tmp/tp.gab
./target/debug/gabbro pruefe           /tmp/tp.gab   # 4 items, 0 errors, 0 hints
./target/debug/gabbro pflichten --lean /tmp/tp.gab   # total 0  goals 0  refused 0
```

**The binder as a plain NUMBER** — compared and computed with, never used as a place, so no
arm of `D022` can reach it, and the body mentions it, so `D023` is silent. And it is the one
of the three forms that makes a *claim*: `t < N` is true over the empty set, false over the
naturals, and nothing in Gabbro says which set `threads` is. *A statement whose truth value is
decided by an undeclared set is not a weak statement, it is an unstated one.* The proof
channel never even saw it: `total 0`.

`D024` refuses it, and **leaves `D023`'s vacuous form standing on purpose**. `D023`'s written
ground is that *"a refusal that makes a word of the grammar unwritable is a grammar change
wearing a rule's clothes"* — so the word keeps one writable shape, and `D023` goes on saying
what that shape is worth. Where `D022` has already spoken about the same quantifier, `D024` is
silent: two refusals for one fault is worse than one.

```bash
./instrumente/pruefe-kennungen.py       # 283 vergeben, D: 24 -- ALL PASS
./instrumente/pruefe-grammatiktafel.py  # GRUEN: 0 von 218 Terminalen UNGEDECKT
```

**The counter-direction is the whole tree.** Over all **686 `.gab` files** the rule falls in
**zero** that were clean before, because every `threads` quantifier the tree writes is the
vacuous one `D023` already hints at:

```bash
git ls-files '*.gab' | while read -r f; do
  ./target/debug/gabbro pruefe "$f" 2>&1 | grep -q D024 && echo "$f"; done   # empty
```

*A rule with one measured hole and no corpus site is the shape of a form nobody had probed* —
the 2026-09-07 census's own sentence about Trap 80, and the reason `GRAMMATIK-VOLLSTAENDIG`
derives its list from `parse.rs` and not from the corpus. The poison is
`beispiele/gift/690-threads-behauptet-ueber-keine-menge.gab`.

### 15.5 A refusal that pointed at the bad exit

`lean.rs`'s `quantified-threads` text read *"…write `slots of <the thread table>`, **or the
language needs a `threads over T`**"* — and §15.3 measures `threads over T` to be a
decoration. **A refusal must not send a reader to a synonym.** It now names the synonym as one
and says what the surface that carries more would have to do:

> `threads` — no declaration names the thread set (every other domain hangs on one); write
> `slots of <the thread table>`. A `threads over T` would be a SYNONYM of that and state
> nothing more — the surface that would carry more has to say which slots are LIVE, and
> Gabbro has no such declaration (`PLAN.md` §15).

*The same class as §11.1, one register further on:* a text that names a way out nobody had
measured is a second register over the design, and only one of the two was read.

### 15.6 Measured — and the register did not move, which is the honest result

Baseline and after are the same commands on the same tree, `ki-pc-fisch-101` unreachable,
`free -g` beside each: 31 GB total, 13–17 GB available, 20 cores.

| | before (`6c835eb`) | after |
|---|---|---|
| modules | 192 | **192** |
| Lean errors | 0 | **0** |
| `sorry` | 25 | **25** |
| `cargo test --no-fail-fast` | 426 / 0 | **427 / 0** (one new test) |
| refusal codes | 282 | **283** |
| `pruefe-deckung.py` | exit 0 | **exit 0** |
| `pruefe-sondendeckung.py` | exit 0 | **exit 0** |
| `pruefe-grammatiktafel.py` | 0 of 218 uncovered | **0 of 218** |

The Lean register, per tag, over the 128-file corpus — **identical in both columns**:

| tag | before | after |
|---|---|---|
| duties (total / goals / refused) | 113 / 65 / 48 | **113 / 65 / 48** |
| assumed | 39 | **39** |
| `quantified-threads` | 6 | **6** |
| `quantified-mappings` | 1 | **1** |
| `layout-buffer-length` | 1 | **1** |
| `slot-record-array` | 1 | **1** |

```bash
cd programmlogik && lake build              # Build completed successfully
#print axioms Gabbro.Coverage.the_sentence       -- [propext, Classical.choice, Quot.sound]
#print axioms Gabbro.Coverage.carried_discharges -- [propext, Classical.choice, Quot.sound]
```

**No `sorryAx` on either**, and `carried_discharges` builds with no `sorry`.

> **A run whose register does not move is a result and not a wasted day**, and the way to tell
> the two apart is the differential: §15.3 measured what the surface would have bought (six
> duties, at the price of a form that means nothing), and §15.4 measured what was bought
> instead (one green hole, closed). *A refusal with a measured ground is a result; a surface
> nobody asked for is not.*

### 15.7 What this run did NOT measure

* **Whether `D024`'s class is closed.** It closes the shape `GRAMMATIK-VOLLSTAENDIG` §1.1
  names for `threads`. The other three forms of §1 — a fractional bound on an integer type
  (§1.2), a `divergent … -> never` that returns (§1.3), an obligation that vanishes on a
  rename (§1.4) — are untouched, and §1.4 is still the sole measured instance of point 3.
* **Whether liveness is the right semantics for `threads`.** §15.3 D says it would mean
  something; it does not say it is what the owner wants, and no probe was written for it.
* **`traverse … over threads`.** The emitter refuses it by name (`C001`,
  `messung/proben/probe-vier-zellen.gab`), and this run did not touch that path — `D024` is a
  rule about quantifiers, and a traversal is not one.
* **The five other `Reason` tags.** Only `quantified-threads` was measured clause by clause;
  the inheritance finding of §15.2 may hold for others and was not checked.

---

## 16. Run 30 — the carried half gets a register, and it names eight forms (agent h, 2026-09-08)

`pruefe-deckung.py` was green, and its own header said what that green was worth:

> **What it does not cover, and this half is the honest one:** *that `Form` is the whole
> grammar.* The refusal half is mechanical because `lean.rs` names its refusals in one enum.
> **The CARRIED half has no such enum** — the emitter decides to carry a form by writing a
> term, at some fifty places, and there is no list to compare against. A form the grammar
> admits, the emitter carries, and `Form` never names would pass every check.

That is `W7` at its most expensive: **two registers over one thing, and only one of them
read.** This run built the missing one. *It found eight.*

### 16.1 The register, and why a new site cannot walk past it

`crates/gabbro-check/src/lean.rs` now carries `LeanCarried`: **54 variants, one per place
the emitter writes a term** — seven kinds of place, ten expression forms, six predicate
forms, five quantifier domains, twenty-five statement forms, and the block. Beside it
`CarriedForm`, which says what a decision carries: the `Form` constructors of
`Coverage.lean` whose lemma discharges it, or `Subterm` — *a literal `3` generates no
obligation; the clause it stands in does.* Eleven of the 54 are sub-terms and say so.

**The forcing is a fact about the TYPE and not about anybody's discipline.** `place_term`,
`expr_term`, `pred_term`, `domain_of`, `stmt_term` and `block_term` no longer return
`Result<String, LeanReason>` but `Result<Carried, LeanReason>`; `Carried` holds its string
in a private field **in a module of its own** — inside one module a private field is private
to nobody — and its only constructor is `LeanCarried::term`. *An `Ok(s)` with a bare
`String` does not compile.* A register a new site can bypass in silence buys nothing, and
this is the difference between a list and a rule.

The population itself is held by the same trick one level up: `LeanCarried::index` is an
exhaustive match, so a new variant does not compile without a number, and
`all_is_the_whole_population` then fails until it stands in `ALL`.

### 16.2 What no term names, and where that is written down

Ten of the forms `classify` calls carried are decided by the emitter **in the wiring** and
not by a term: there is no term for *"the callee's contract IS the duty proved over its
body"*, there is a wiring order. Seven such forms stand in `CARRIED_BY_WIRING` — form, the
emitter function that decides it, and why there is no term:

| form | site | why no term |
|---|---|---|
| `callChain` | `wiring_order` | an ORDER of hypotheses |
| `callFrame` | `openings` | the `writes` list becomes a frame hypothesis |
| `contractFromDuty` | `routine_goals` | the wiring itself |
| `recursionSelf` | `self_recursive` | the induction over `decreases` |
| `recursionCycle` | `wiring_order` | one induction over a shared measure |
| `recursionInLoop` | `rec_in_loop` | a recursive call in the routine's own ranged loop |
| `declaredRange` | `shape_conjunct` | a conjunct of the well-typedness, both directions |

The list is in `lean.rs` and not in the guard **because it is a statement about the
emitter**, and a test demands that every carried form stand in exactly one of the two
lists: *a new carried form must be classified; it cannot arrive unnoticed.*

### 16.3 The finding: eight forms the emitter carried and `Form` never named

The first run of the correspondence failed, and the failure is the result of the run:

```
carrying sites name forms that `classify` does not call carried:
  domain-reach names `quantReach`          stmt-invariant-suspension names `invariantSuspension`
  stmt-reason-match names `reasonMatch`    stmt-publish names `publishAtomic`
  stmt-return-call names `callResultReturned`  stmt-await names `awaitAtomic`
  stmt-call-with-error-exit names `callWithErrorExit`  stmt-critical-section names `criticalSection`
```

**Six of the eight are the CARRIED half of a form whose REFUSED half was in the register
all along** — and that is the shape of the blindness, not an accident of eight separate
oversights:

| form | refused when | carried when | the refusal was named |
|---|---|---|---|
| `let … else` | at a place (`let n = A else …`) | at a CALL | `let-else` |
| `publishes` | at a place with a suffix | at a bare atomic | `publish` |
| `awaits` | at a place with a suffix | at a bare atomic | `await` |
| `locks` | the fallback arm only | since 2026-08-28 | `concurrent-statement` |
| `match` | over anything but an option… | …or a `tagged`, **or a reason** | `match-not-option` |
| `narrow` | off a range | on a range (an `ite`) | `narrow` |

*The refusal was in the register because refusals have an enum; the carry was not because
carries had none.* The two that are not of this shape are `return f(a);` — `Stmt.retCall`,
a call shape whose three siblings were all named — and the `descendants of` / `ancestors of`
domain, an index range cut by a reach, which stood beside `quantSlots`, `quantElems`,
`quantQueue` and `quantChain` and was the fifth.

`narrow` is the one that needed no new constructor: the emitter writes an `ite` for it and
`controlFlow` discharges an `ite`. The register says so, and that is the honest half of the
mapping — a site names the form whose lemma covers it, not a form of its own.

### 16.4 The eight are now theorems, with no `sorry`

`Form` has **53 constructors** (was 45), **40 carried** (was 32), **40 discharge lemmas**
(was 32). The seven new statement lemmas stand in `Coverage.lean` §5.8b; `ReachDomainCarried`
is `IndexDomainCarried ∧ ChainDomainCarried`, which is the whole content of a cut domain.

* `ReasonMatchCarried` — where an arm carries the case's name the model runs it; where the
  subject is not a reason it is **stuck**, which is the honest outcome and not a silent
  fall-through.
* `CallResultReturnedCarried` — the callee's contract fires, the answer returned is the
  callee's, the caller's locals are untouched. The precondition is not a premise: `step` is
  stuck without it, as at every other call.
* `CallWithErrorExitCarried` — **two exits out of one call, and both of them named**: a
  `reason` answer runs the `else` block with the reason bound, any other value fills the
  binding.
* `InvariantSuspensionCarried`, `CriticalSectionCarried` — both are `exec ρ b s`, by `rfl`.
  *That is not a shortcut, it is the claim*: the duty at a `breaking` stands beside the
  block, and what makes the sequential reading at a `locks` sound is the lock passes.
* `PublishAtomicCarried` — a store at a `.global` place and nothing else moves.
* `AwaitAtomicCarried` — a read of the world into a binding, the world untouched.

### 16.5 The guard, and the register that is STILL read by nobody

`pruefe-deckung.py` gained checks 7–9 (the carried population, and the correspondence both
ways), six speech tests, and a probe that carries a `LeanCarried` of its own — **a `lean.rs`
without the carried register is now an ABORT and not a green half.** The same correspondence
runs as `cargo test -p gabbro-check --lib lean::deckung_tests`, reading `Coverage.lean` with
`include_str!` at COMPILE time: *a file that moves away takes the build down, where a guard
that read it at run time would report a missing file as a green run.*

**And the header names what is left, because an uncovered part named is worth more than a
guard that pretends:**

* **`parse.rs` against `Form` is a third register, and it has no guard.** A form the parser
  admits, `lean.rs` never writes a term for and `Form` never names would pass everything
  here. `pruefe-grammatiktafel.py` holds the EBNF against the grammar table; nothing holds
  either against `Form`.
* **That the MAPPING is the right one.** A site that named `store` where it should name
  `read` would pass — both are carried. What is mechanical is that the name exists and that
  nothing is left unnamed; which lemma actually covers a site is a reader's judgement.

### 16.6 Measured

Local, `free -g` beside it — 31 GB total, 12–17 GB available, 20 cores; `ki-pc-fisch-101`
unreachable through the jump host, so the memory is measured beside the run and not assumed.

| | before | after |
|---|---|---|
| `cargo test --no-fail-fast` | 430 passed, 0 failed | **435 passed, 0 failed** (five correspondence tests) |
| `lake build` | green | **green** |
| `sorry` in `Coverage.lean` | 0 | **0** |
| corpus modules / errors / `sorry` | 192 / 0 / 25 | **192 / 0 / 25** |
| `pruefe-deckung.py` | exit 0 — 42 reasons, 45 forms, 32 carried, 32 lemmas | **exit 0 — 42 reasons, 53 forms, 40 carried, 40 lemmas, 54 carrying sites (11 sub-term), 7 by wiring** |
| `mutiere-pruefer.py --anker` | 381 of 398 | **381 of 398** |

**The emitted corpus is BYTE-IDENTICAL.** Measured and not assumed: `all/` was generated
with the new binary, the change stashed, the binary rebuilt, `all/` generated again, and the
two directories compared file by file. *The register records what the emitter decides; it
does not change a decision.*

`#print axioms`, by hand:

```
'Gabbro.Coverage.the_sentence'             [propext, Classical.choice, Quot.sound]
'Gabbro.Coverage.carried_discharges'       [propext, Classical.choice, Quot.sound]
'Gabbro.Coverage.ownLogic_is_the_persons'  [propext, Classical.choice, Quot.sound]
```

The populations, counted from the source and not from the guard's own line: 54 variants in
`enum LeanCarried` and 54 entries in `ALL`; 53 constructors of `Form`, of which 40 carried;
33 distinct forms named by carrying sites plus 7 by wiring is **40, and the difference
against the carried set is empty**.

Guardians: `pruefe-todo.py` and `pruefe-waechter.py` byte-identical before and after (both
red before, on `DONE.md`'s poison count — not this run's). `pruefe-zahlen.py` keeps its
finding count; one already-red counter moved its MEASURED value (`Zeilenfortsetzungen`,
3538 → 3540), which is a total over the tree that any new line shifts. **Three mutation
anchors were re-aimed** — `lean-and-becomes-or`, `lean-record-field-becomes-a-slot`,
`lean-lock-loses-its-name` all quote lines this run rewrote; without that the anchor count
would have fallen 381 → 378, and *a mutation that measures nothing looks exactly like one
that passes.*

### 16.7 What this run did NOT measure

* **That the 33 named forms are the RIGHT ones for their sites.** See §16.5: the
  correspondence is over names, not over meanings.
* **`parse.rs` against `Form`.** Named in the guard's header and in §16.5, closed by nobody.
* **The wiring half of the emitter beyond its seven names.** `CARRIED_BY_WIRING` says which
  function decides a form; nothing checks that the function still does.
* **Points 1 and 3 of `messung/GRAMMATIK-VOLLSTAENDIG-2026-09-08.md` §0.** As in §13.8: this
  file answers point 2 and is silent about a form that MEANS NOTHING and about an obligation
  that vanishes on a rename.
* **§13's own numbers were not re-booked.** §13.2 reads 45 constructors and 86 expanded
  forms; that is the record of run 26 and stays what it was. §11's rule: *neither number is
  the tree's.*
