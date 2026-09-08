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
