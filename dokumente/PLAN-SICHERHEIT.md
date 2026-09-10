# The safety theorem — does the grammar cover every error except the person's logic?

*Written 2026-09-09. Step 1 is BUILT and green; steps 2–6 are planned, not built.*

> **The question, in one sentence:** does Gabbro reach the goal that grammar and syntax
> cover ALL errors, so that the only error a Gabbro program can still contain is the
> logic of the person who wrote it?

> **The answer, in one sentence:** **not as stated — and the folder already knows it.**
> *Grammar and syntax* cannot carry the sentence (a context-free grammar decides no
> range, no rank and no linearity); what carries it is the checker, and for the checker
> the folder had a classification (`Coverage.lean`) and 137 theorems about its RULES
> (`passlogik/`), but **no theorem about RUNS**. That theorem — *a body the checker
> accepts gets stuck only at a `requires` or an `invariant`* — now exists over the
> sequential core, 0 `sorry`, and its premises name exactly what stays outside:
> alias, memory model, termination, the axiom layer, foreign bodies, the emitter.

The sentence `BEWEIS.md`:18 states — *"Whoever proves a Gabbro program proves the LOGIC of
their program — and nothing else"* — is therefore true **as a theorem over the sequential
core of `Body.lean`**, and **false as a sentence about the language**, in six named places
(§2). Neither half is a surprise to this folder; what is new is that the first half is a
theorem and the second half is a list.

---

## 0. What "the only error is the user's logic" MEANS — as a proposition

A slogan is unfalsifiable; a proposition has a shape. The shape here is the oldest one in
type theory, *well-typed programs don't go wrong* (progress + preservation), and it needs
three things the folder has:

| | where it is | what it says |
|---|---|---|
| a **semantics** with a notion of *going wrong* | `programmlogik/Gabbro/Body.lean` — `eval … = none`, `Outcome.stuck` | a division by zero, a bit operator on a negative number, a value of the wrong shape, a call whose `requires` is false, a loop whose `invariant` is false: the model STOPS instead of inventing a value |
| a **checker** as an algorithm | NEW: `Gabbro/Sicherheit/Ausdruck.lean` (`schluss`), `Anweisung.lean` (`pruefe`) | written from `SPRACHE.md` §3/§7/§8, not from `crates/` — the same rule `passlogik/README.md` sets for itself: *the model must be able to CONTRADICT the Rust* |
| a **dividing line** between plumbing and logic | `Coverage.lean` §4 `IsOwnLogic`: `ensures`, `invariant`, `requires`, `reaches` | NEW: `LogikS`/`LogikB`, an inductive predicate whose only ground cases are a `requires` that fails at a call and an `invariant` that fails on entry |

The proposition:

```
theorem exec_sicher … :
    pruefeBlock P erg Δ b = some Δ' →        -- the checker accepts the body
    Welt P.D Γ s.world → WFU Δ s.local' →    -- the state lies in its declarations
    exec ρ b s = .stuck → LogikB ρ b s       -- stuck ⇒ at the person's own clause
```

`LogikB` has two ground constructors (`ruf`/`rufGebunden`/`rufSonst`/`rufZurueck` — one
`requires` at four call shapes — and `invariante`) and eleven that only pass the site down
into a sub-block. `logik_grundfaelle` states that as a theorem so a third source of
"logic" cannot be added silently.

**What the theorem does NOT say is the half a coverage claim usually skips**, and it is
written into the head of `Gabbro/Sicherheit.lean` (§2 below).

---

## 1. The state before this step — measured, with the file that says it

| claim in the folder | file | what stands behind it | what did NOT |
|---|---|---|---|
| "Gabbro proves everything except logic" | `SPRACHE.md`:615, `README.md`:34 | 12 passes, 285 diagnostics, 94 register sentences: **87 measured, 2 argued, 5 conjectured, 0 PROVED** | no sentence of the register is a theorem about a run |
| "nine of the eleven plumbing classes are carried today" | `README.md`:37 | `gabbro paesse`: 3 complete, 9 carried with a named residue | *race* at 3 of 28 forms rests on nothing (the alias); *refinement* hangs on the Isabelle semantics of a body |
| the checker's rules are sound | `passlogik/`, 137 theorems, 0 `sorry` | interval lattice, effect hull, rank order, termination measures, linearity, phases | its own README: *"137 theorems over a model whose load-bearing assumption is unmodelled"* — the statement descent is a premise in four of seven files; **no theorem mentions `exec`** |
| every form is carried, assumed or refused | `Coverage.lean` `the_sentence` | 45 forms + 42 refusal reasons, one verdict each, `classify_total` | true by construction of `classify`; **says nothing about whether an accepted program gets stuck** — the file's own §7 lists it |
| the model can get stuck | `Body.lean` `Outcome.stuck` | every stuck site is deliberate and commented | **no theorem excludes `stuck` for an accepted program** — the model had the notion and no safety theorem |
| the emitter is the trust base | `README.md`:12, `BEWEIS.md`:1497 | two silent failures, both closed, both with a poison probe | outside every model in the folder; `Form.checkerAndEmitterTrusted` |

So the honest reading of the folder before 2026-09-09: **the plumbing is carried by
passes whose rules are proved sound in isolation, classified as covered, and never
proved to compose into a run that does not go wrong.** That composition is the theorem
of this step.

---

## 2. What was built — step 1, green

```
programmlogik/Gabbro/Sicherheit/Ausdruck.lean    692 lines   14 theorems   expression half
programmlogik/Gabbro/Sicherheit/Anweisung.lean  1632 lines   36 theorems   statement half
programmlogik/Gabbro/Sicherheit.lean             ~185 lines    3 theorems   the sentence, 8 speech tests, `#print axioms`
```

`lake build` on Lean `v4.33.1` (the toolchain `passlogik/lean-toolchain` pins), no
`mathlib`, **0 `sorry`, 0 own `axiom`**, every `#print axioms` shows only `propext`,
`Classical.choice`, `Quot.sound`.

### 2.1 The expression half — `schluss_sicher`

`schluss D Δ e = some sh` is the checker's verdict: accepted, with shape `sh`. The theorem:
in a world that respects its declarations and locals that respect their scope, `eval s e`
is `some v` with `v.hasShape sh`. What the checker refuses, and the theorem therefore
never has to evaluate:

| refusal | rule in `gabbro-check` | in `schluss` |
|---|---|---|
| denominator whose range does not exclude zero | `M102` | `arith .div/.rem`: `0 < lo₂ ∨ hi₂ < 0` |
| bit operator / shift on a range with a negative part | `M137`/`M104` | `arith .band … .shr`: `0 ≤ lo₁ ∧ 0 ≤ lo₂` |
| index whose range leaves `0 ..< count` | `M103` | `.place`: `0 ≤ lo ∧ hi < count c` |
| result range through `+ − ×` | `M104` | `add`/`sub` by `omega`, `mul` by the four-corner product ported from `Bereich.lean` |
| a `tagged` value without a target type | `constructed-value` (`Coverage`) | `.tagOf` refused — the type comes from the target, never from the expression |

### 2.2 The statement half — `pruefe_sicher`, `pruefeBlock_sicher`

`pruefe P erg Δ st = some Δ'` threads the scope `Δ` (a list, so it is comparable) through a
statement; every store is held against the declared shape of its target (`passt` — `M104`
at the assignment), every `match` must name every case (`D005`/`M123`) with a binder that
fits the payload, every call must fit its signature and carry a `requires` that is a
`bool` under the parameter scope (so a precondition can only be FALSE, never
ill-shaped), a `let … else` must have an else block that ends in an exit
(`SYNTAX.md`:1029). The theorem, per outcome:

| `step` ends in | what holds afterwards |
|---|---|
| `running s'` | the world respects `Γ`, the locals respect `Δ'` |
| `returned s' v` | the world respects `Γ`, the value fits the routine's declared answer |
| `exited`/`left` | the world respects `Γ`, the locals respect the ENTRY scope |
| `stuck` | **impossible — unless `LogikS` holds** |

**And three mutations, run on 2026-09-09 before this file was written — a theorem with no
mutation against it is undamageable, not covered (`README.md`:254):**

| mutation | in | result |
|---|---|---|
| drop `M102` — `arith .div` answers `some .int` for every denominator | `schluss` | `schluss_sicher` **fails** (2 errors, the `div`/`rem` arms) |
| drop `M103` — `.place` no longer holds the index against `count` | `schluss` | `schluss_sicher` **fails** (the `.place` arm) |
| drop the exit condition on the else block of `let … else` | `pruefe` | `pruefe_sicher` **fails** (the `bindCallElse` arm) |

*Each is a one-line `sed` on a scratch copy; S5 makes them a probe.*

### 2.3 The premises — visible at the theorem, never an axiom

| | premise | what it is, one level down |
|---|---|---|
| S1 | `Deklariert D Γ` | `Γ` is the emitter's reading of the declarations: slot fields uniform in the index inside `0 ..< count` |
| S2 | `KettenWohlgeformt` | every `via` field is option-shaped **at every index** — forced by Finding 2 |
| U1 | `UmgebungOK` | every declared callee keeps the world well-formed and answers per its signature — *this very theorem for the callee's body* |
| U2 | `SchleifenOK` | every registered loop keeps the world and its scope — *this very theorem over `iterate`* |
| U3 | (in `binde`) | a name is never rebound with a DIFFERENT shape; `n = n + 1` is allowed, `let x = 1; let x = true;` is refused |
| U4 | (in `namenEindeutig`) | the cases of a `tagged` type have distinct names |

U1 and U2 are what step 2 discharges.

### 2.4 The findings — where the specification or the model gave way

**This is the actual yield, as in `passlogik/README.md`.** Each names the file it is about.

| # | finding | file:line | consequence |
|---|---|---|---|
| **1** | **Index out of range and width overflow are NOT errors in the model.** `World := Place → Value` is total — `σ (.slot c 999 f)` answers a value whatever `count` says; `binop .add` computes in `Int` with no width | `Body.lean`:147, :473 | the theorem carries these two classes only as **properties of the checker** (`schluss` demands the index inside the bound; `WF` keeps every stored value in its range), not as excluded faults of the semantics. *A program that indexes outside does not get stuck in this model — it reads.* For the full sentence `Body.lean` needs a fault outcome at the index (or `Place` must carry the bound) — step 3 |
| **2** | **`Shape.opt` carries no range.** `option index into T` is `present n` with arbitrary `n`; `chase` follows it out of the typed region | `Body.lean`:209, :428 | premise S2 quantifies over ALL indices instead of `0 ..< count` — the model cannot say "an option index is in range" |
| **3** | **The else block of `let … else` must end, and `Body.lean` does not demand it.** `SYNTAX.md`:1029 says *diverge or return*; `step` on an else block that falls off runs on with a binding that got no value | `Body.lean`:1287 | `endetMitAusgang` is a condition of the checker here; without it the theorem is false (the block would leave the scope) |
| **4** | **A `reason` has no `Shape`.** `Value.hasShape (.reason _) _ = false`, so a reason cannot stand in `Typing`/`WF` | `Body.lean`:251 | the scope here carries `Ge.grund` beside `Ge.form`; a reason in the WORLD (a `static` of a `reason` type) is untypeable in the model |
| **5** | **Division, remainder, bits and shifts come out as `.int` without a range**, while `typen.rs` computes bounds (`0 ≤ a/b ≤ a`, `x & m ≤ m`) | `Coverage.lean` `arithmeticBounds` = `carriedByTactic` | the general theorem is missing in BOTH places; the corpus is the only evidence for those bounds |
| **6** | **The seam.** `schluss`/`pruefe` are a checker THIS file wrote from the specification, not `gabbro-check` | `W16` | that both accept the same programs is measured by nothing — step 4 |

Findings 1 and 2 are the sharp ones: **they mean a safety theorem over today's `Body.lean`
is vacuous for the index class** — the very class `BEWEIS.md`'s table lists first.

---

## 3. What stays OUTSIDE the theorem — and cannot be put inside it by proving harder

These are not gaps of `exec_sicher`; they are limits of the semantics it stands over.
Each one the folder already names; here they stand in one list, with the sentence that
names them.

| class | why the theorem cannot reach it | the folder's own sentence |
|---|---|---|
| **alias** | `Body.lean` places are `DecidableEq` — *"that IS the alias freedom"* — so two names for the same bytes do not exist in the model | `SYNTAX.md`:537 *"not decidable at any single site without alias analysis"*; `messung/RACE.md`: 3 of 28 race forms rest on nothing, and those three are the alias; `udp-echo.gab` reads a stale checksum with 0 errors |
| **memory model, publication, `release`/`acquire`** | one world, sequential; `publish` is a store | `Body.lean`: *"costs no memory model"*; pass 7 residue A10; `release_stellt_sichtbarkeit_her` is `unfalsifiable` with a probe that already exists |
| **termination** | a loop is `ρ id`, its passes are the environment's business | `Terminierung.lean`: `forever_laeuft_ewig`; `S005`/`S008`/`K009` *necessary, not sufficient*; Finding 3 of `passlogik`: `retry … bounded` ends only if a pass costs something, and the spec does not say so |
| **the axiom layer** | `assume`/`axiom` are names with a class; the theorem quantifies over `ρ` | `SYNTAX.md`:1646 *"the largest unproved surface of the language — larger than the compiler"*; 27 falsifiers named, **0 runnable** (`BEWEIS.md`:119); `unfalsifiable` writable at sites the checker cannot see (`UNFALSIFIZIERBAR.md`) |
| **foreign bodies** | `extern fn`, `asm`, `entrust` — their contract is a hypothesis on `ρ` | `PLAN-VERIFIKATION.md` §2.3: *93 refusals become 93 named assumptions* — and U1 is exactly that hypothesis |
| **the emitter and the C** | the theorem ends at the Gabbro body | `README.md`:12 *"the emitter is the trust base, with a failure record of two — both silent"*; `BEWEIS.md` "which C" |
| **the checker implementation** | Finding 6 | `passlogik/README.md`: *"the seam between the model and `gabbro-check` is checked by nobody"* |
| **liveness, progress** | not a stuck-ness property at all | `SPRACHE.md`:341 *"no mechanism addresses it"* |

**So the sentence a finished proof would carry** is the one `BEWEIS.md`:359 already
drafted, now with the theorem's name in the first line:

```
plumbing-safe      by exec_sicher, under S1 S2 U1 U2        (sequential core, Body.lean)
memory-safe        under A1…An                              n ≈ 130, measured, ratchetable
alias-free         NOT CARRIED — 3 race forms rest on nothing
race-free          under c11_*                              2, with litmus probes
terminating        forever: no; traverse/retry: necessary conditions checked
functionally open  on O1…Ok                                 k UNKNOWN — the person's logic
```

---

## 4. The plan — six steps, two of them measurements

**S1 — The safety theorem over the sequential core.** BUILT 2026-09-09, above. What it
buys: the sentence *"stuck ⇒ own logic"* is a theorem, and six findings. What it costs:
nothing in `crates/`; three Lean files, no dependency.

**S2 — The program theorem: discharge U1 and U2.** *Build.* Today the callee's behaviour
is a premise (`UmgebungOK`). `Body.lean` already has the wiring: `Runs ρ f body`
(`ρ f` is the body), `RunsLoop`/`iterate` (`ρ id` is some sequence of passes). The step is
one induction:

* per routine `f` with `Runs ρ f body_f` and `pruefeBlock … body_f = some _`: from
  `pruefeBlock_sicher`, `ρ f` keeps `Welt` and answers per signature — **provided every
  callee inside does** (U1 for them). That is a fixpoint over the call graph: for an
  acyclic graph an induction over the order; for a cycle `K008`/`K009` give `decreases`,
  which makes the induction well-founded on the measure — the same shape
  `Coverage.lean` uses in `recursion_cycle_carried`.
* per loop: induction over `iterate`'s index list, using the `exited`/`left` rows of
  `Ergebnis` (they were put there for this).

Condition under which S2 counts: `UmgebungOK` and `SchleifenOK` disappear from
`exec_sicher`'s premises and are theorems (`umgebung_ok_of_runs`), and the theorem is
stated once over a `Programm` with a body table. **Falsifier:** a corpus unit with a
call cycle without `decreases` — the theorem must refuse it, not assume it.

**S3 — Make the two silent classes FAULTS.** *Build, in `Body.lean` — coordinated, the
Isabelle proofs rest on the big-step shape (`OFFEN.md` O1).* Finding 1: add an outcome
that the semantics reaches when an index leaves `0 ..< count c` or a store leaves a
declared width — the plumbing table of `BEWEIS.md`:32 as an enumeration
`Fehlerklasse := index | ueberlauf | nenner | gestalt | …`, and `Outcome.fehler k`.
Then `exec_sicher` becomes *stuck-or-fault ⇒ own logic*, and the index class is a
theorem instead of a checker property. Finding 2 with it: `Shape.opt` gets a range, or
`Shape.optIn lo hi`. **Falsifier:** `beispiele/gift/` files that index outside must
reach `fehler .index` under `exec` — today they reach a value.

Cheapest form, if `Body.lean` may not move: a *second* evaluator `evalF` beside `eval`
with the fault, and one theorem that `evalF = eval` wherever `evalF` reports no fault.

**S4 — The seam (Finding 6): witness pairs, not a proof.** *Build + measurement.* The
form `PLAN-VERIFIKATION.md` §3 chose for the export, for the same reason (size):
`gabbro lean` already writes a `Duty*.lean` per unit; let it also write

```
theorem checker_agrees : pruefeBlock P erg [] ⟨body⟩ = some _ := by decide
```

with `P` filled from the declarations. A unit the Rust checker accepts and `pruefe`
refuses (or the reverse) then fails LOUDLY at `lake build`, per unit, per run. What it
measures: the two checkers agree on the corpus — not that they are the same function.
**Numbers to report:** units accepted by both / by one only, with the refusing side named.
The first run will find differences (Finding 5 alone guarantees some: `pruefe` gives `/`
no range, `typen.rs` does), and each is either a rule `pruefe` lacks or a rule
`gabbro-check` has and the spec does not state — **both are findings, the second kind is
the expensive one.**

> **S4 status 2026-09-10: BUILT and measured** (`lean::witness`, `tests/seam.rs`; their
> tree untouched, every witness elaborates, zero non-`decide` errors). `beispiele/`
> (71 files, all Rust-accept): 189 routines, 119 witnessed (63%), 70 skipped by name
> (56 duty refusals, 14 unshaped-scope). Of the 119: **53 both-accept, 66 rust-only,
> 0 lean-only**; files 13 green / 36 red / 22 unwitnessed. `gift/` sample (14 files):
> 7 both-refuse (in-scope poisons fire both sides), 4 expected lean-accept outside
> `pruefe`'s domain (effects/measure/requires/ensures), 1 both-accept, **1 reverse
> finding (F10)**, 1 excluded vacuous (P034 recovery body is empty -- witnesses over
> unparsed files measure nothing). Ten findings, all with file:line: F1 `endetMitAusgang`
> lacks `-> never` (Anweisung:270, inst. 11a); F2 duty `#ret`-reuse vs `binde`-U3
> (Anweisung:102 vs lean.rs:2331, inst. 18/39); **F3 `schluss` index needs `IntIn`
> while `index into` params carry `.int` (Ausdruck:224, 34 inst. -- the largest)**;
> F4 div/rem/bits result `.int` vs `typen.rs` bounds (Ausdruck:166, = Finding 5,
> probe-measured); F5 no flow-sensitive narrowing (11 inst. + probes); F6 `.ret` has no
> `or R` rule though `UmgebungOK` states it (Anweisung:366, inst. 48); F7 unshaped
> (ptr/token) params invisible (Anweisung:199, 14 inst.); F8 static arrays as call args
> (Ausdruck:223, inst. 64); F9 record answers unbindable (Anweisung:331, inst. 21);
> F10 `someOf` never checks the option bound, reverse-found via gift/170 (M101 gap,
> Ausdruck:246). Deviations from the sketch, each load-bearing: `.isSome = true`
> (`= some _` leaves a metavariable `decide` cannot evaluate); entry is the parameter
> scope (`[]` refuses every routine that reads a parameter); loop variables are bound
> to `0` at entry (adapter A1 -- the model binds no loop variable, a convention gap
> for their lane); `#ret` replays as `.opt` (A2). Scope replay is exact by construction
> (`binde`-replay over the walk's push sequence) and green-proved on 3 loop files.
> Latent, unmeasured: op-call pres over unshaped op params (masked by F7 at every
> instance). Reproduce: ignored `seam::emit_corpus` (`SEAM_SRC`/`SEAM_OUT`), then
> `lake env lean` per file under `timeout`.

**S5 — The guardian.** *Cheap, first.* `instrumente/pruefe-sicherheit.sh`: `lake build`
in `programmlogik/`, `grep -c sorry` = 0 over `Gabbro/Sicherheit*`, `#print axioms`
contains no `sorryAx`, the eight speech tests of `Sicherheit.lean` present, and a ratchet
on the finding count (6, may fall, not rise without a diff in the guardian). Same shape as
`pruefe-lean-beweis.sh`; and the same problem V6 of `PLAN-VERIFIKATION.md` names — Lean
runs only where it is installed. *Until the guardian exists, every regression here is
invisible, which is the state `passlogik` was in until `Abnahme.lean`.*

**S6 — The classes outside the model, written into the sentence.** *Paper.* §3's table
becomes the artefact line `BEWEIS.md`:359 drafted: the theorem for the first row, the
assumption set for the second, **`NOT CARRIED` for the alias** until an alias analysis
exists (the folder's oldest open item), the necessary-condition status for termination.
That is the honest form of *"the only error is the user's logic"*: **true for the
sequential core under named premises, and a list for the rest.**

**Order and dependency:** S5 → S1 (done) → S2 → S4; S3 is independent and coordinated
with O1; S6 hangs on nothing and is the cheapest item with the largest effect on what the
README may claim. *No day estimates* (W7): S2 and S4 are builds with a known subject,
S3 is a decision about a shared file, S5 and S6 are writing.

---

## 5. The verdict on the question, row by row

| error class | carried by | proved here? | status |
|---|---|---|---|
| index in range | `M103` | `schluss_sicher` (checker side) — **not** as a fault of the model (Finding 1) | carried; theorem vacuous on the semantic side until S3 |
| no overflow | `M104` | range through `+ − ×` proved; `WF` preserved at every store; `/ % & \| ^ << >>` without range (Finding 5) | carried for the four; open for the rest |
| no division by zero | `M102` | `schluss_sicher`, `.div/.rem` | **proved** |
| no shape error, exhaustive `match` | `D005`/`M123`, `N`-passes | `pruefe_sicher`, `pruefeTags_sicher`, `pruefeArme_sicher` | **proved** |
| call fits signature, answer fits binding | `N028`/`N029`, `M1` | `bindCall`/`bindCallElse`/`retCall` cases | proved under U1 |
| frame / effects | `E005`/`E008`/`E010` | `Wirkung.lean` (rule), not here — `Body.lean` has no effect lists | outside this theorem |
| lock held, rank order | `H001`–`H017` | `Rang.lean` (rule); `locked` is the body's here | outside; `R1` open in `Rang.lean` |
| alias | — | — | **not carried** (3 race forms) |
| race / memory model | pairing + A10 | — | assumed by name |
| termination | `S005`/`S008`/`K009`, `forever` | `Terminierung.lean`: necessary, not sufficient | partially |
| phase, leafness, publication | passes 11, 6, 7 | `Phasen.lean` (rule) | outside |
| refinement | P6 | — | open (`README.md`:48) |
| `requires` false, `invariant` false, `ensures` | the person | **excluded by definition** — `LogikB`, `IsOwnLogic` | *the logic* |

**Three rows say "proved", three say "outside", one says "not carried", one says "the
logic".** That is the answer to the question with the source list beside it — and the
theorem is what turns the first three rows from register sentences into statements
about runs.

---

## 6. Commands

```bash
cd programmlogik && lake build                          # 8 jobs, ~40 s cold, prints the axiom lines
grep -c sorry Gabbro/Sicherheit/*.lean Gabbro/Sicherheit.lean   # 0 0 1 -- the 1 is the WORD in a comment of the head file, no `sorry` term
grep -c '^theorem' Gabbro/Sicherheit/*.lean Gabbro/Sicherheit.lean   # 14 36 3
lake env lean Gabbro/Sicherheit.lean                    # the eight speech tests, by `decide`
```

The build needs Lean `v4.33.1`; `passlogik/INSTALLATION.md` says where it runs and what it
costs. `Gabbro.lean` imports `Gabbro.Sicherheit`, so `lake build` of the default target
builds it.
