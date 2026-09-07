# What is still open at the CHECKER and at the GRAMMAR — 2026-09-07

**Base:** `master` at `3c32aa6`. **Corpus** wherever "the corpus" appears below:

```bash
git ls-files 'beispiele/*.gab' | grep -v '/gift/'   # 70 files
```

**Provenance is marked on every row.** `[self]` means measured while writing this document,
with the command beside it. `[lane]` means a lane reported it and it is recorded here
*unverified by a second party*. The distinction is the point: three lanes ran today, and a
number that only one party has ever produced is a claim, not yet a measurement.

**Not a to-do list in priority order.** It is a census of what is open, cut by *where* the
gap sits — checker, grammar, prover channel, or the guards themselves.

---

## 1. The checker is SILENT and emits anyway — and this is a class, not three accidents

Three sites where `gabbro pruefe` reports **zero errors**, `gabbro emit` returns **0**, and
what comes out is either wrong C or C that means something the source did not say. **All
three were found today, and none of them is reachable from the corpus** — no program in the
tree has this shape, which is why a corpus-based measurement never saw them.

### 1.1 A quantifier domain has NO effect — all nine of them `[self]`

```bash
sed 's/in slots of Topologie/in threads/' beispiele/18-vorfahren.gab > /tmp/dom-c.gab
./target/debug/gabbro pruefe beispiele/18-vorfahren.gab   # 5 items, 0 errors, 0 hints
./target/debug/gabbro pruefe /tmp/dom-c.gab               # 5 items, 0 errors, 0 hints
./target/debug/gabbro emit  … ; md5sum                    # 4220717dff74105e8d12af740e7c7d3c — BOTH
```

The invariant reads `forall g in slots of Topologie : Topologie.slots[g].bereich <= 255`.
Changed to `forall g in threads : …` it **quantifies over threads and indexes slots**, and:
zero errors, zero hints, and **byte-identical C**.

> **The domain a user quantifies his invariant over is decoration.** Whatever he meant to
> say about `threads`, the compiler understood the same thing it understood about `slots` —
> and nothing anywhere told him. `[lane]` reports the same for all nine domains, by a
> differential over the derived grammar.

### 1.2 A fractional bound on an INTEGER type `[self]`

```bash
printf 'module p::r {\ntype T = u32 in 0.5 .. 1.5;\n}\n' > /tmp/float.gab
./target/debug/gabbro pruefe /tmp/float.gab   # 2 items, 0 errors, 0 hints
./target/debug/gabbro emit  /tmp/float.gab    # exit 0
```

### 1.3 `divergent … -> never` that returns `[self]`

```bash
printf 'module p::d {\ndivergent fn q() -> never\n    effects { pure }\n{\n    return;\n}\n}\n' > /tmp/never.gab
./target/debug/gabbro pruefe /tmp/never.gab   # 2 items, 0 errors, 1 hints
./target/debug/gabbro emit  /tmp/never.gab    # static _Noreturn void q(void) { … return; }
cc -std=c11 -Wall -Wextra -Werror -c /tmp/never.c   # exit 2
```

`cc` refuses on two counts (compiler locale is German here):

* `-Werror` — *„als »noreturn« deklarierte Funktion hat »return«-Anweisung"*
* `-Werror=attributes` — *„Attribut »const« an einer Funktion mit Rückgabetyp »void«"*

**The second one is NOT isolated**: this probe writes `effects { pure }`, and that is what
produces `__attribute__((const))` on a `void` function. Whether `pure` on a `void`-returning
routine is a defect in its own right **was not separated out here** and should not be counted
as a fourth finding until it is.

### 1.4 A `group` item is swallowed by error recovery `[lane]`

`faengt_item_an` omits `Kw::Group`, so after any earlier refusal a `group` item disappears
into recovery — 2 items where `lock`/`rcu` give 3.

### 1.5 Two holes that read a name and never its class `[self]`

`crates/gabbro-check/src/geteilt.rs:532` (`ein_kern`) and `:1468` (`H015`) resolve the
assumption **by name**. Neither reads the assumption's CLASS, so an unfalsifiable assumption
covers exactly as much as one carrying a probe.

### 1.6 M1 — 57 expressions still carry no type `[self]`

```bash
./target/debug/gabbro pruefe $(corpus) | grep -oE 'M1 saw …'   # 1278 total, 57 untyped — 95.54 %
```

Down from 84 today, denominator unchanged at 1278. `[lane]` names the remainder: **33** are
the double meaning of `Typ::Unbekannt` (a call returning nothing is not an untyped
expression), **19** bare `None`, **3** `lenof`, 1 match binder, 1 mixed-width add. Splitting
`Typ::Unbekannt` in two would remove 33 from the denominator *and* add four refusals — the
highest-value item on that list, and not started.

---

## 2. The grammar and syntax — where the FORM does not exist

| | gap | size | source |
|---|---|---|---|
| 2.1 | **Templates named in the spec with NO generator code** (`Stand::Entworfen`, `schablonen.rs:44-45`) | **8 of 21** | `[self]` `gabbro schablonen` |
| 2.2 | Forms the checker accepts and the emitter refuses by `C001` — incl. **an array and a record as a parameter type**, and the item kinds `format` and `walk` | **12** | `[lane]` |
| 2.3 | `B10` — `traverse … over queue`: the checker accepts, the emitter refuses by name | 1 | `[self]` `pruefe-notation.py` |
| 2.4 | ~~`B22` — a multi-line `claim` cannot be written~~ **REFUTED, see §8.2** — it has been writable since 2026-08-17 | **0** | `[self]` |
| 2.5 | **`ops` is not under-adopted, it is under-powered** — 50 of 55 hand-written write sites cannot be converted, 26 of 29 carriers. Walls: `M140` (9 carriers), `D010` (5), `D001` (12) | **91 %** | `[lane]`, verified by rewriting carriers |

On 2.5, one consequence is booked and easy to miss: **converting to `ops` MOVES an
obligation, it does not remove one** — every `ops` call charges the caller a `D012`
precondition at the call site.

---

## 3. The prover channel — what a user must prove BESIDES his own logic

```bash
./target/debug/gabbro pflichten --isabelle $(corpus)   # total 84  goals 1  refused 83
```

**One obligation of eighty-four becomes an Isabelle goal.** The 83 refusals, by class `[self]`:

| class | n | the reason, verbatim |
|---|---|---|
| `body-effect` | **27** | *"speaks about the world AFTER a body ran, and there is no Isabelle semantics of a Gabbro body"* |
| `foreign-body` | **21** | *"an `ensures` at a body Gabbro never sees: an ASSUMPTION, not a goal"* |
| `device-promise` | 18 | *"a promise at hardware Gabbro does not see"* |
| `lock-witness` | 11 | *"`Held(…)` — carried by the lock passes, not by a prover"* |
| `no-term` | 5 | *"the predicate uses a form this emitter has no Isabelle term for"* |
| `argument-not-stable` | 1 | *"the actual argument is neither a literal nor a parameter the body leaves alone"* |

**`no-term` and `argument-not-stable` are SILENT**: the syntax accepts the predicate, the
checker reports nothing, and the obligation leaves the proof channel with no diagnostic
anywhere. Same shape as §1, one layer up.

### 3.1 Six premises that no pass establishes

```bash
./target/debug/gabbro schablonen --gate   # 6 premises of PROVED templates have no pass
```

Ratchet tooth 3, and the tree's own words: *"a proof nothing establishes."* Four are named
as grammar or language gaps:

* **`consuming.leermenge`** — *"empty WHEN? … would need **a grammar line**: `by consuming`
  names no point in time."*
* **`accumulates.monoid`** — the quiescent point — *"would need the EXECUTION CONTEXTS —
  without them Gabbro does not say who runs concurrently."* **The conclusion holds and
  the REASON is refuted — §8.1.**
* **`consuming.ordnung`** (two premises) — no generator for `by consuming`, none for the
  witness order.
* **`table.induktion`** — the generator writes two edge premises per chaining field, not one.

> **The most dangerous of the four, in the register's own words:** *"`S005` checks that the
> MEASURE can move, not that the CHOICE is minimal; two different statements."* A pass that
> is green, named almost right, and establishes the neighbouring claim.

**These four premise texts are hand-written prose in `schablonen.rs`, and prose in this tree
has been stale before.** A lane is verifying all four against the checker's code as this is
written; until it reports, they stand as `[lane-prose]`, not as measurements. `gabbro
kontexte` exists as a subcommand and `kontexte.rs` is real, which is direct grounds to doubt
the `accumulates` premise as stated.

### 3.2 An invariant that no function owns

`gabbro pflichten` class `W`, **10 of 84**: *"Invariant owed by NO function — a `walk`, or a
`table`/`group` that no `maintains` names."* The grammar has `maintains`; nothing requires an
invariant to have an owner.

---

## 4. The guards themselves

### 4.1 `pruefe-grammatiktafel.py` has the wrong GRANULARITY — not the wrong source `[lane]`

Its population is *"the rules and terminals `dokumente/SYNTAX.md` carries"* (`:8`). The
expected defect was a document-vs-code divergence over **words**. **There is none** — every
EBNF terminal is implemented, every parser-decided word is in the EBNF.

> **The divergences live in COMBINATIONS, and the population is WORDS.** All 32 measured
> divergences are invisible to it, and **none of them lowers its green.**

A guard can read the right file, count the right things, come out green, and still be blind —
because the unit it counts is finer than the unit the defects live in. That is `W16` at a
level the tree had not booked before.

### 4.2 Three smaller defects in the same guard

* `:828` prints a hard-coded *"die anderen 213 sind reserviert"* `[self]`. Measured today:
  **17 reserved, 204 contextual** (`zaehle-wortschatz.py`). Stale by 196 since 2026-09-05.
* `:253` matches `ancestors` with a whitespace-sensitive regex `[lane]`.
* The `P006` note omits three item kinds `[lane]`.

---

## 5. Pending, and not settled here

* **`kanten-n041` is unmerged.** At merge: renumber poison `685`–`687` to `707`–`709` (lane 1
  already took 685/686 with different filenames — `git` reports no conflict and would leave
  two 685s), and reconcile `DONE.md`, `README.md`, `TODO.md` **by hand**. The
  merge-addition class, thirteenth booking.
* **`CLAUDE.md` books `375 von 376` valid mutations with ONE survivor.** Two lanes measured
  independently today: `392 of 396` and `391 of 395` — **four survivors**, both. The
  catalogue grew, the figure beside it did not. *Reported, not edited: it is the owner's file
  and its ratchet is the owner's.*
* **One claim unverified in either direction.** A lane reports that at the loop-label
  position 204 of 221 words still collide, only two sites in `parse.rs` (`:3293`, `:3335`)
  testing for a bare identifier. **A reproduction attempt while writing this failed** — all
  three probe spellings fell at `P001`, including the one that should pass, so the probe's
  `retry` form was wrong, not the claim. The figure 204 does match today's contextual-word
  count exactly, which is grounds to take it seriously and no substitute for a run.
* **`beispiele/` is still German** and `CLAUDE.md`'s language table does not name the
  directory. Owner's call.

---

## 6. The one sentence this census is for

Items **1.1**, **1.2**, **1.3**, and the `no-term`/`argument-not-stable` pair are one shape:

> **The checker says nothing and the compiler emits anyway.** Not a missing construct — a
> missing objection.

And **not one of them is reachable from the corpus.** There is no program in this tree that
quantifies over `threads` while indexing `slots`, none that puts a fractional bound on a
`u32`, none that returns from a `never`. They were found by deriving the grammar from
`parse.rs` and probing each form, and they are the argument for that method over a corpus:
**Trap 80 does not only make a corpus flattering, it makes it BLIND in a specific direction —
toward every shape nobody thought to write.**

---

## 7. Runs behind this document

| what | command | result |
|---|---|---|
| quantifier domain | `sed` variant + `pruefe` ×2 + `emit` ×2 + `md5sum` | both `0 errors`; C md5 identical |
| fractional integer bound | `gabbro pruefe` / `emit` on the probe | `2 items, 0 errors`; emit `0` |
| `never` that returns | `pruefe` / `emit` / `cc -Werror` | `0 errors`; `cc` exit 2, two `-Werror` classes |
| M1 coverage | `gabbro pruefe` over the corpus, summed | 1278 / 57 untyped, 95.54 % |
| obligations | `gabbro pflichten` over the corpus | 84, eight classes |
| obligations as goals | `gabbro pflichten --isabelle` over the corpus | `total 84  goals 1  refused 83` |
| templates | `gabbro schablonen` | 21: 10 proved, 3 CARRIED, 8 designed |
| premises without a pass | `gabbro schablonen --gate` | 6 |
| notation gaps | `python3 instrumente/pruefe-notation.py` | `B22` open; `B10` open |
| vocabulary | `python3 instrumente/zaehle-wortschatz.py` | 17 reserved, 204 contextual |
| stale literal | `sed -n '826,830p' instrumente/pruefe-grammatiktafel.py` | *"die anderen 213"* |
| assumption-class holes | `grep -n` in `geteilt.rs` | `:532`, `:1468` |

**NOT run for this document, and nothing above rests on them:** the mutation catalogue,
`pruefe-emission.sh`, `abnahme.py`, `isabelle build`, `cargo test`. The `[lane]` rows carry
their own runs in the lanes' own reports (`messung/KLEMPNEREI-2026-09-07.md`,
`messung/UNOWNED-EDGES-2026-09-07.md`, `messung/GRAMMATIK-AUS-DEM-CODE-2026-09-07.md`) and
were **not** re-run here.


---

## 8. Verified after this document was written — and two of its own rows fall

A lane took the four grammar/proof claims of §3 to the checker's code with the mandate to
**refute** them. Result: **one confirmed and understated, three narrower than stated.**
Recorded here rather than silently edited above, because a claim that moved and a claim that
was always right are not the same thing.

### 8.1 The `accumulates` premise — right conclusion, WRONG reason, and the tree had already said so

*"Without EXECUTION CONTEXTS Gabbro does not say who runs concurrently"* is **false**:
`crates/gabbro-check/src/kontexte.rs` has existed since 2026-08-19 and `gabbro kontexte`
prints a context count. **The tree booked that retraction on 2026-08-18** — `MESSUNGEN.md`
:9310, and `geteilt.rs:470` says of the identical sentence *"Der Satz war ueberholt und
niemand hat es gemerkt."* The premise line carrying it was **re-written on 2026-08-31**,
twelve days after its own retraction was on record.

> **The same binary prints the sentence and its retraction.** `gabbro paesse` says it "was
> overtaken by its own `entry` construct"; `gabbro schablonen --gate` still prints it.

The conclusion survives, with a different cause: `geteilt.rs:507` puts `accumulates` on
`H013`'s exemption list, and `H013` filters on `writes ` only (`:552`) — so a fold **reading**
while other cores write is structurally invisible. `gift/146` gives `[H013]`; the same shape
with `accumulates` gives **0 errors**.

### 8.2 `B22` is REFUTED, and its guard has reported it open for three weeks `[self]`

```bash
# pruefe-notation.py's own B22 probe:
./target/debug/gabbro pruefe <probe>
#   error: [N043] `measures n` names nothing declared
#   error: [D021] `n` in a `floor` is not declared here
```

**The probe fails on an undeclared `n`, not on the multi-line `claim`.** The decisive test is
a real file split across lines:

```bash
# 52-baugatter.gab, its one `claim` split over three lines:
./target/debug/gabbro pruefe   # 14 items, 0 errors, 0 hints -- identical to baseline
./target/debug/gabbro emit     # exit 0
```

`parse.rs:442`: *"«B22» geschlossen 2026-08-17: benachbarte Zeichenketten werden EINE."*
**`pruefe-notation.py` has counted a closed gap as open ever since**, because a probe that
errors for ANY reason reads as a gap. Same class as §4.1: a guard right about its number and
wrong about its sentence. **This lowers §2's grammar-gap count from 2 to 1 — `B10` alone.**

### 8.3 Invariant ownership is literal STRING EQUALITY `[self]`

`pflichten.rs:345-357` matches a `maintains` against an invariant by name text. So:

```bash
sed 's/maintains baum_wohlgeformt/maintains baum_bleibt_baum/' beispiele/01-tabelle.gab
./target/debug/gabbro pflichten   # 15 obligations -> 14
./target/debug/gabbro pruefe      # 0 errors
```

**An obligation disappears on a rename, silently.** And one statement ends up booked
simultaneously as owed and as unowned. The `84 / 10 / 70` figures of §3.2 are exact; the
class LABEL's stated cause is right for **7 of the 10**, not all ten.

### 8.4 Claim 4 was UNDERSTATED — `S005` does not check a neighbouring statement, it checks nothing

`decreases` is optional (`parse.rs:3244`) and `S005` returns before running when it is absent
(`schleifen.rs:326`). **The corpus's only clean `by consuming` site — `01-tabelle.gab:136` —
has no `decreases`.** So there, `S005` is not measuring the wrong thing; it is not measuring.
With `decreases opfer` added it stays silent and `ist_blatt(c,s)` remains open; with
`decreases NSLOTS` it fires. Minimality is untouched in all three.

**And a fifth thing nobody was looking for:** the certificate is blind to the entire
`consuming` family — `zeugnis.rs:845` keys on the domain and never on `t.abstieg`.
`01-tabelle.gab` uses `by consuming` three times and its certificate names **zero** of the
three templates behind it.

### 8.5 What this does to §6

Nothing. The three silent-emit sites of §1 stand, all three re-measured. But §8.1 and §8.2 add
a second shape beside them, and it is the older one in this tree:

> **A sentence that was retracted and kept being printed.** `B22` closed on 2026-08-17 and its
> guard has said "open" since. The `accumulates` reason was retracted on 2026-08-18 and was
> re-typed into the register on 2026-08-31. *Neither is a missing objection — both are an
> objection nobody withdrew.*
