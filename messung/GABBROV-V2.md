# GabbroV V2 — the three rebookings, and the vacuity half

*Measured 2026-09-03 from tree `4e53df3`. `messung/GABBROV-V1.md` §6 costed two things and
built neither: a rebooking of three rows that are entered twice, and the cheap half of the
V2 gate. This file carries both. Every count below names the command that produced it.*

## The answer, up front

**The three rebookings are VERIFIED — and by a stronger witness than the one that was
offered.** The claim was that `PFLICHTEN.md` books three `progress` rows a second time as
logic obligations. It does. What nobody had checked is the other side: **the manifest the
binary emits does not double-book them at all.** `gabbro annahmen` lists all three names;
`gabbro pflichten` emits no obligation from any `progress` clause. *The tool already holds the
opinion the correction argues for; only the hand-kept document was wrong.*

**And the counts did not move the way arithmetic said they would.**

| | before | after | |
|---|---:|---:|---|
| `PFLICHTEN.md` total | 239 | **239** | *unchanged — the `K`/`L` column is machine-vs-subject, not obligation-vs-assumption, and the tree's own rule is that a discharged obligation still counts* |
| `K` / `L` | 173 / 66 | **173 / 66** | unchanged |
| `GABBROV.md` §1's figure | "164 K" | **163 K anchored, 173 total** | *it was already wrong before any rebooking* |
| GabbroV's obligation population | 66 | **63** | the three are discharged by the assumption layer |
| of those, **not sayable** | 10 | **8** | L42, L46 leave |
| of those, **sayable** | 56 | **55** | L66 leaves, from the other side |

**The vacuity check is built** — `programmlogik/gabbrov/V2.lean`, `lean` exit 0, no `sorry`,
no `native_decide`, with a **proved soundness theorem** rather than a bounded search.

```
of the 55 sayable obligations
  carrying a precondition at all      31
  VACUOUS                              0
  not vacuous, witness exhibited      31
  undecided                            0
  no precondition, nothing to check   24
```

**None is vacuous, and that is said plainly.** The check earns the result by being able to
fire: §2.4 drives it against a deliberately vacuous `requires` written for the purpose, and
shows the consequence in its sharpest form — ***an obligation whose postcondition is `False`
passes.***

**One finding beside the mandate:** `L44` and `L53` are **tautologies**. Their precondition is
satisfiable, so vacuity does not catch them, but their postcondition follows from the
precondition alone (`absent ≠ int 0` is a fact about the datatype). *`GABBROV-V1.md` proved
exactly that lemma to support the two rows, and it turns out to BE them.*

---

## 1. The three rebookings — verified, not taken over

`GABBROV.md` §5 and `GABBROV-V1.md` §6 claim that the ten fragments' three `progress` names
are **already** `assume` declarations, and that `PFLICHTEN.md` books each a **second** time as
a logic obligation. The claim was checked at three places rather than read.

### 1.1 The rule: a `progress` name MUST resolve to a declared `assume`

`SYNTAX.md`:1074, at the `forever` form:

> ***"`progress` names WHO ends it — an assumption about the environment, with a falsifier.
> The watchdog IS the falsifier."***

**And it is not only prose — the checker enforces it.**
`crates/gabbro-check/src/schleifen.rs`:221, `fortschritt_pruefen`:

```rust
match lg.annahmen.get(&z.text) {
    None        => absagen.schiebe(Absage::fehler("S003", …)),  // no declared assumption
    Some(false) => absagen.schiebe(Absage::fehler("S004", …)),  // unfalsifiable
    Some(true)  => {}
}
```

`S003` — *"`progress` names no declared assumption"* — is a hard error, and its note repeats
the rule: *"otherwise it is a hope with a keyword in front"*. `S004` adds that the assumption
must be falsifiable. **So the set of legal `progress` names is a subset of the declared
assumptions, by construction of the checker.**

### 1.2 Exactly THREE, and the count is against the FROZEN text

`PFLICHTEN.md`'s population is *"the ten ```gabbro blocks of `FRAGMENTE.md` @ `708beed`"*.
Counting `progress` in today's file gives **five** — and two of the five were written after
the freeze and are outside the population. The count has to be taken where the population is:

```
git show 708beed:dokumente/FRAGMENTE.md | grep -n "progress"
```

| frozen line | clause |
|---|---|
| 887 | `progress    device_completes_or_faults` |
| 981 | `progress    client_calls_or_endpoint_revoked` |
| 1656 | `progress token_verbraucht` |

*(884, 1239 are prose about the keyword, not clauses.)* **Three. The claim holds — but only
because it was checked at `708beed`; the same grep on `HEAD` answers five.**

| the `assume` in the source | `progress` at | `PFLICHTEN.md` row | anchor |
|---|---|---|---|
| `messung/fragmente/F04.gab`:33 `device_completes_or_faults` | :887 | **L42** (line 237) | 886 |
| `messung/fragmente/F05.gab`:87 `client_calls_or_endpoint_revoked` | :981 | **L46** (line 260) | 981 |
| `messung/fragmente/F10.gab`:62 `token_verbraucht` | :1656 | **L66** (line 383) | 1656 |

The `L42`/`L46`/`L66` numbering was **read off** rather than taken over: the `L` rows of
`PFLICHTEN.md` enumerated in file order with the tree's own `_zellen` parser put the three
progress rows at ordinals 42, 46 and 66 exactly. *`GABBROV-V1.md` gives L42's anchor as 887;
the row's own anchor is **886** — the `forever` head, not the `progress` line. One line, and
it is corrected here rather than carried.*

`F10.gab`:60 states the rule in its own words as the reason its `assume` is there at all:
*"`progress` nennt eine Annahme mit Falsifikator; ohne `assume` steht der Name in keinem
Manifest."*

### 1.3 The measurement nobody asked for: the EMITTED manifest does not double-book

`GABBROV.md` §2 rests the whole design on one sentence — ***"GabbroV does not read the Gabbro
program. It reads the manifest."*** So the question that decides what needs correcting is not
what `PFLICHTEN.md` says, but **what the binary emits.**

```
./target/debug/gabbro annahmen  messung/fragmente/F04.gab
./target/debug/gabbro pflichten messung/fragmente/F04.gab
```

| fragment | `gabbro annahmen` | `gabbro pflichten` |
|---|---|---|
| F04 | `A1 device_completes_or_faults  assume  ungedeckt` | **1 obligation**: `VirtioPci :: reg QUEUE_SIZE requires`. *No progress row.* |
| F05 | `A1 client_calls_or_endpoint_revoked  assume` | *no register — the fragment has errors (`N041`, `M134`)* |
| F10 | `A1 token_verbraucht  assume  ungedeckt` | **2 obligations**: `naechstes_token :: ensures #1`, `kerne_zaehlen :: loop invariant #1`. *No progress row.* |

> **So the double-booking is not in the manifest at all. It is only in the hand-kept
> document.** The assumption channel carries all three names; the obligation channel carries
> none of them. **The tool already holds the opinion the rebooking argues for** — what is
> wrong is `PFLICHTEN.md`, and nothing that GabbroV would ever read.
>
> *That sharpens `GABBROV.md` §5, which says the three are booked twice "here and under
> `obligation`". They are booked twice in `PFLICHTEN.md`'s `L` column and in the assumption
> manifest. `obligation`, as the binary emits it, was never one of the two places.*

**Verdict on claim 1: VERIFIED, and by a stronger witness than the one offered.**

### 1.4 `PFLICHTEN.md` is HAND-KEPT, so the file is the right place to edit

The mandate's caution — *if a tool produces it, the tool is what needs the change* — was
answered by search before any edit:

```
grep -rn "PFLICHTEN" --include=*.py --include=*.rs --include=*.sh .    # 14 files
```

Every one of the fourteen is a **reader**. No `write_text`, no `open(…, "w")`, no shell
redirection into `dokumente/PFLICHTEN.md` exists in the tree. **The file is hand-kept, and an
edit to it stands.**

### 1.5 The counts, re-measured and NOT subtracted

```
./instrumente/zaehle-pflichten.py --spalten
```

| | |
|---|---|
| anchored | 229 = **163 K** + **66 L** |
| lowering rows | 10 = 10 K + 0 L |
| **total** | **239 = 173 K + 66 L** |

> **The re-measurement caught a number that was already wrong, before any rebooking.**
> `GABBROV.md` §1 says ***"164 K against 66 L"***. The tree measures **163 K** anchored and
> **173 K** in total. `164` is neither. *It is, however, exactly what the counter's own speech
> probe produces when an escaped-pipe row is miscounted:* `Sprechprobe: ok (eine Zeile mit
> maskierter Pipe zaehlt mit: K 163 -> 164)`. **The mandate said re-measure rather than
> subtract; this is the row that shows why.**

### 1.6 And the `L` count does NOT move — the tree's own convention says so

The obvious move is to take the three rows out of the `L` column, and it is the wrong one.
**`PFLICHTEN.md`'s third column is not "obligation vs assumption".** Its own legend:

> **K / L** — plumbing / logic, by the criterion of `BEWEIS.md`: *mentions only the MACHINE →
> K; mentions the SUBJECT → L*

These three mention the device, the client, the token — the **subject**. They are `L` by the
criterion, and rebooking who *discharges* them does not change what they *mention*.

**And the file already has the rule for a discharged row**, stated in the counter's own
docstring:

> *"A struck-through class counts too — `~~K~~ **zu**` is a CLOSED obligation, not a removed
> one. That is the opposite rule from `gap:`, and on purpose: **a withdrawn gap is no
> obligation, a discharged obligation still is one.**"*

So: **239 / 173 / 66 stands after the rebooking, and that is a measurement, not a
preservation.** Re-run of `zaehle-pflichten.py --spalten` after the edit is in §1.8.

**What moves is the fourth column**, and it moves *into* the schema rather than out of it.
Column four's legend is *"a refusal code of a **present-day** pass, or a named gap"* — and
`S003`/`S004` are refusal codes of a present-day pass. The neighbouring row is already written
that way:

```
| 885–889 | the poll terminates and the overflow is NAMED | K | `S001`/`S002` |
| 886     | it ends because **the device** completes or faults | L | the human — … |
```

*Two adjacent rows about the same `forever` loop, one discharged by a pass and one by "the
human" — and the second has a pass too.*

### 1.7 So what does "10 → 8" mean, measured rather than asserted

It is **not** a statement about `PFLICHTEN.md`'s columns. It is a statement about **GabbroV's
obligation population**, which is the `L` rows minus the rows that are not obligations:

| | | source |
|---|---:|---|
| `L` rows of the ten fragments | 66 | `zaehle-pflichten.py --spalten` |
| of these, discharged by the assumption layer | 3 | L42, L46, L66 — §1.2 |
| **GabbroV's obligation population** | **63** | |
| of the 63, not sayable in the fragment | **8** | L11 L12 L13 · L24 L34 L50 L52 · L57 |
| of the 63, sayable | **55** | |

Read off `programmlogik/gabbrov/V1.lean`'s own census block rather than subtracted:
`nichtSagbar` lists ten in four classes; the class *"environment liveness — an `assumption`
(§5), not an `obligation`"* holds `["L42", "L46"]` and is the class that leaves. **8 remain,
in three classes.** L66 leaves from the *sayable* side, so the sayable count moves 56 → 55.

> **And the finding `GABBROV-V1.md` put under the ten survives intact.** The four ordering
> rows — L24, L34, L50, L52 — are untouched by any of this. *The rebooking makes the number
> smaller and the gap exactly as wide as it was.*

### 1.8 The edit, and the re-measurement AFTER it

The three rows now carry the rebooking in their fourth column, struck through rather than
overwritten (`~~the human~~ — **REBOOKED 2026-09-03** …`), each naming the `assume`, its
`falsifier`, `S003`/`S004`, and the two binary channels that disagree with the old entry.

```
./instrumente/zaehle-pflichten.py --spalten     # AFTER the edit
  verankert  229 = 163 K +  66 L
  insgesamt  239 = 173 K +  66 L
```

**Unchanged, and that is the result rather than a relief** — the class column was never the
thing that was wrong.

> **And a guard moved, from my own report file rather than from the rebooking.**
> `pruefe-zahlen.py` went red:
>
> ```
> BEFUND  TODO.md: „Dateien, die der Widerrufwaechter liest" steht als 182, der Lauf sagt 183
> ```
>
> **Cause measured by removing the file and re-running**, not guessed: `pruefe-widerruf.py`
> globs `messung/*.md` (`:263`) as well as `dokumente/*.md` (`:243`), so *this file* moves the
> count. `TODO.md`:556 carries it as a guarded number; corrected 182 → 183, and
> `pruefe-zahlen.py` is exit 0 again.
>
> *`GABBROV-V1.md` §2 hit the same thing one directory over, and wrote it down as the reach of
> a new `dokumente/*.md`. It is wider than that: **a new `messung/*.md` does it too.** The
> guard for the document you are adding is a number about a different guard's reach.*

---

## 2. Vacuity — the cheap half of V2, BUILT

`programmlogik/gabbrov/V2.lean` is the check. It sits beside `V1.lean`, outside the library,
imports `Gabbro.Body` and defines no second semantics — §8's rule, for §8's reason.

```
cd programmlogik && lake build Gabbro                # green
LEAN_PATH=.lake/build/lib/lean lean gabbrov/V2.lean  # exit 0, no `sorry`, no `native_decide`
```

### 2.1 The answer, with its denominator

| | | |
|---|---:|---|
| `L` rows of the ten fragments | 66 | `zaehle-pflichten.py --spalten` |
| sayable as a `Prop` (`V1`) | 56 | `V1.lean` |
| **less the row rebooked out of the obligation register (L66)** | −1 | §1 |
| **obligations the check applies to** | **55** | |
| of those, **carrying a precondition at all** | **31** | §2.3 |
| of those, **VACUOUS** | **0** | `#eval` in `V2.lean` |
| of those, **not vacuous, witness exhibited** | **31** | |
| of those, **undecided** | **0** | |
| carrying no precondition — nothing to check | 24 | |

> **NONE of the 31 is vacuous, and that is said plainly because it is the result.** A clean
> sweep over 31 obligations is a real finding, not an absence of one — *provided the check
> could have come out otherwise*, which is what §2.4 is for.

*Counting L66 as an obligation instead, the figures are **32 of 56**, and still 0 vacuous. The
denominator is given both ways because §1 moved it today.*

### 2.2 What the check IS

A precondition among the 66 that is not itself a quantified invariant is a conjunction of
constraints on places: `requires s.used`, `requires q.phase == DRIVER`, `requires cap != 0`.
So the check's object is that shape and no other:

```lean
inductive Atom where
  | eq (p : Place) (v : Value)
  | ne (p : Place) (v : Value)

def vacuous : Pre → Bool
  | []        => false
  | a :: rest => rest.any (clash a) || vacuous rest
```

`clash` is where the content sits: `eq p v` against `eq p u` with `v ≠ u`, and `eq p v`
against `ne p v`. **The fourth combination is expressly `false`** — two disequations on one
place are always jointly satisfiable, because `Value` has infinitely many inhabitants
(`.int n` for every `n`). *A checker that answered `true` there would be unsound in the
direction that costs something: it would condemn a real obligation as meaningless.*

**And that soundness is proved, not asserted:**

```lean
theorem vacuous_sound (pre : Pre) (h : vacuous pre = true) (w : World) : holds w pre = false
```

The verdict is thereby a statement about **every world there is**, not about the ones the
checker looked at. *That is the difference between this and a bounded search, and it is the
reason the `VACUOUS` outcome can be trusted while a search's silence cannot.*

The other direction is a **construction rather than a search**: `canon pre` binds every
`eq`-place to its value and leaves the rest `absent`, so the witness for a satisfiable
precondition is built from the precondition itself. Each row's witness is then checked by
`decide`.

**Three outcomes, because `GABBROV.md` §4 demands three and not two:** `vacuous`,
`notVacuous`, `undecided` — the last for a precondition outside the atom fragment. It is
named rather than approximated, which is §7's rule.

### 2.3 The 31, and how "has a precondition" was decided

A row has a precondition exactly when its `V1.lean` `Prop` carries an antecedent that
constrains a state — the antecedent of a top-level implication (`cdtWf s.world … → cdtWf
s'.world …`) or the guard inside a bounded quantifier (`allD d fun s => used = true → …`).
Both are preconditions in the sense that matters: **if nothing satisfies them, the consequent
holds for free.**

| | rows |
|---|---|
| **precondition, in the atom fragment** (27) | L01 L02 L06 L08 L10 L14 · L28 L31 L33 L35 · L36 L37 L38 L39 L40 · L43 L44 L47 L49 · L53 L56 L58 L59 L60 L61 L62 L63 |
| **precondition, a quantified INVARIANT** (4) | L05 L09 L16 (`cdt_wohlgeformt`) · L27 (`antwortpflicht_paarig`) |
| **no precondition** (24) | L03 L04 L07 L15 L17 L18 L19 L20 L21 L22 L23 L25 L26 L29 L30 L32 L41 L45 L48 L51 L54 L55 L64 L65 |

`L10` and `L60` are **case splits**, and each arm carries its own precondition — so the
register holds 30 entries over 28 rows, and both arms are checked. *An obligation whose second
arm is vacuous is half an obligation, and a check that only looked at the first would not see
it.*

**The four invariant-preconditions never reach the atom checker**, and the file says so rather
than stretching the checker to cover them. They are answered in the same currency — a world is
exhibited: `wCdt` has slots 1 and 2 reaching root 0 through `parent`, so `cdt_wohlgeformt` is
satisfiable and L05/L09/L16 are not vacuous; an endpoint with `caller` and `reply_owner` both
set meets `antwortpflicht_paarig`, and so does one with neither.

### 2.4 The speech test — and the check FIRES

*A vacuity check that has never said VACUOUS is an ornament* (`R11`), and a clean sweep over
31 rows is worth exactly what the check's ability to come out otherwise is worth. So it is
driven against a precondition written to be unsatisfiable.

**The vacuous obligation, written for the purpose.** F4 declares
`tagged type BufPhase = { Driver, Device }` and L41's obligation is that a buffer is in
exactly one of the two. This `requires` demands **both** — the shape a `requires` takes when a
conjunct is added to an existing one without reading it:

```lean
def preVac : Pre := [.eq (.slot "q" 3 "phase") (.int 0), .eq (.slot "q" 3 "phase") (.int 1)]

example : verdict preVac = Verdict.vacuous := by decide
theorem preVac_unsat : ∀ w : World, holds w preVac = false := vacuous_sound preVac (by decide)
```

**And here is why it matters, in the sharpest form the file could put it.** Take that
precondition and give the obligation the *worst possible* postcondition — `False`:

```lean
def LVac (s _s' : State) : Prop := holds s.world preVac = true → False

theorem LVac_passes : ∀ s s' : State, LVac s s'
```

***An obligation whose postcondition is `False` is a theorem.*** No program was consulted, no
body was executed. That is what a vacuity check is for, and it is why a `passed` without one
is worth nothing — §5's sentence, now with a witness under it.

**Both directions, because one direction is not a test:**

| probe | verdict | what it would catch |
|---|---|---|
| `preVac` — two `eq` on one place, different values | **vacuous** | the check can fire at all |
| `preVac2` — `eq p 0` and `ne p 0` | **vacuous** | a checker comparing only equations would miss it |
| `preSat` — `eq phase 0` and `ne phase 1` | **notVacuous** | a checker firing whenever a place repeats |
| `preTwoNe` — `ne x 0` and `ne x 1` | **notVacuous** | the `.ne`/`.ne` arm of `clash`; if it returned `true`, this line falls |

### 2.5 A neighbouring pathology the run found, and it is NOT vacuity

Vacuity is *"the precondition admits no state"*. **Two rows have the opposite defect**: the
precondition admits states, and the postcondition then follows from the precondition **alone**,
with no reference to any program.

`L44` and `L53` both say *"never read yet is distinguishable from zero"*, and both stand as

```
x = absent → x ≠ int 0
```

In the shared `Value` that is a theorem about the datatype — `absent` and `int 0` are different
constructors — and `V2.lean` proves both outright:

```lean
theorem L44_is_a_tautology (w : World) :
    w (.global "capacity") = .absent → w (.global "capacity") ≠ .int 0 := by
  intro h; rw [h]; decide
```

**They hold of the empty world**, which contains no program at all. *The obligation the
fragment MEANT is a statement about the model's expressiveness; what stands is a statement
about Lean's `Value`, and no program can fail it.*

> **`GABBROV-V1.md` was one step from this and stopped.** Its speech test proves
> `absent ≠ int 0` and calls it *"the distinction L44 and L53 rest on, proved rather than
> asserted"* — correct, and it is exactly the fact that makes the two rows say nothing. *A
> lemma proved to support two obligations turned out to BE them.*
>
> This is a finding for the owner, not a repair: the rows are the corpus's, and rewording them
> is a decision about what F5 and F7 meant. **Same family as vacuity — an obligation that
> cannot fail — and the reason it is booked separately is that the check of §2.2 does not and
> should not catch it.** A tautology detector is a different tool; naming the two rows costs
> nothing and building it costs V3.

---

## 3. What V2's EXPENSIVE half would still cost, after this

Nothing this run did makes `G5` cheaper, and the honest scheduling is that it made the gap
**more visible rather than smaller**.

| | |
|---|---|
| the assumption set | **8**, over the ten fragments (`gabbro annahmen`; F1, F3, F6–F9 declare none) |
| of the 8, carrying a `falsifier` | 7 — one is expressly `nicht-falsifizierbar` with its reason written out |
| of the 8, standing as a FORMULA | **0** |
| **plus, since today** | the three `progress` names are now *booked* where they always stood, so the assumption register is the register `G5` is about — and it is still eight prose sentences |

**The cost is unchanged and it is the formalisation.** Eight assumptions is nothing for a
solver *if they are formulas*; `"Ein Geraet, das einen Deskriptor genommen hat, meldet ihn
innerhalb der zugesagten Leseoperationen zurueck oder faultet"` is not one, and asking whether
it has a model is not yet a question.

**And V1's measurement of *why* it is harder than V1's own work now has a second witness.**
The assumptions speak about the world; two of the three rows rebooked today are exactly the
ones whose referent V1 could not reach, and §1 above shows the tree already treats them as
world-facing. *A fragment that cannot say "the flush completed before the reply" — the four
ordering rows, untouched — cannot say "the device reports back within N reads" either.*

> **What this run DOES change about the schedule:** the vacuity half is no longer an argument,
> it is a file with a proved soundness theorem and a firing demonstration. §10's V2 row can be
> split: *vacuity — done; satisfiability — a second V0, and it has not been started.*

---

## 4. What this lane did not measure, named rather than left out

* **Preconditions conjoined with the declared invariants.** §2.2 asks whether a `requires` is
  satisfiable *alone*. A precondition can be satisfiable alone and unsatisfiable together with
  a `table … invariant` — and that is the sharper question. It needs the invariants as
  premises, which is V3's shape.
* **Whether any of the 31 is PROVABLE.** Same disclaimer `V1.lean` carries about itself: a
  non-vacuous obligation is not a discharged one.
* **The `requires` conjuncts as the BINARY emits them.** §2.3's preconditions are read from
  `V1.lean`'s rows, which were read from `PFLICHTEN.md`. The manifest carries
  `blatt_loeschen requires #1` — a name, a kind and an ordinal — and `GABBROV-V1.md` §4
  already books that gap. *The vacuity check is built against the obligations as WRITTEN
  DOWN, and wiring it to the manifest waits on the manifest carrying its text.*
* **The second corpus.** Ten fragments chosen for difficulty are the right denominator for
  "can it be said", and the wrong one for "how often is a precondition vacuous in practice".
  **0 of 31 here does not predict 0 elsewhere.**

---

## 5. The runs behind every number above

| command | result |
|---|---|
| `./instrumente/zaehle-pflichten.py --spalten` | 229 = 163 K + 66 L; 239 = 173 K + 66 L |
| `./instrumente/pruefe-zahlen.py` | exit 0 |
| `./instrumente/pruefe-englisch.py` | ALL PASS; marks 7883 / 1069, unmoved |
| `./instrumente/zaehle-wortschatz.py` | 221 / 208 / 333, unmoved |
| the frozen fragment text at `708beed`, grepped for `progress` | three clauses |
| `./target/debug/gabbro annahmen messung/fragmente/F04.gab` | `A1 device_completes_or_faults` |
| `./target/debug/gabbro pflichten messung/fragmente/F04.gab` | 1 obligation, no progress row |
| `cd programmlogik && lake build Gabbro` | green |
| `LEAN_PATH=.lake/build/lib/lean lean gabbrov/V1.lean` | exit 0 |
| `LEAN_PATH=.lake/build/lib/lean lean gabbrov/V2.lean` | exit 0 |
| `cargo test --offline --no-fail-fast` | **399 passed, 0 failed**, 31 suites |

*Everything that computed ran on `ki-pc-fisch-101` in `gabbro-v2`, per `CLAUDE.md`. No poison
probe was added — the vacuous obligation of §2.4 is a Lean definition, not a corpus file, so no
number in the `663+` range was claimed.*
