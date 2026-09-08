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
   `RunsLoopIn`. Not started; it changes the invariant language.
2. **Refused forms** (13): quantifiers over `fields of`, `threads`, `mappings of`, a
   membership (`x in …`); a carrier that is not a table; the layout built-ins (`sizeof`,
   `lenof` over a buffer). Each needs a model domain it does not have. They stay refused
   with their tag; a refusal is not a `sorry`.
3. **Recursion inside a loop** (not wired): the loop's contract and the routine's
   self-contract in one induction. Named unwired in the register.
4. **`gabbro_calls` and hole goals** (measured, not fixed): a precondition hole opened for an
   inner call does not see a hypothesis added by a later instance; the innermost-first order
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
