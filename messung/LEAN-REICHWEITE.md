# The reach of the Lean channel — how far is the tool that proves an ARBITRARY Gabbro program?

*Measured 2026-09-02 at tree `a053d3a`, server `ki-pc-fisch-101`, directory `gabbro-le`.
`lean` at `~/.elan/bin/lean` (Lean 4 via `elan`), `isabelle` at `~/Isabelle2025-2/bin/isabelle`.
Every number below carries the command that produced it.*

## The answer

**It renders. It does not prove.** Over the 175-file corpus the checker's own obligation
register holds **100 obligations**, and **10** of them reach Lean as a goal — all ten go
through, so the honest headline is **10 %**. Add the Isabelle channel's single goal and the
union is **11 of 100**; the intersection is **zero**, so no obligation in this tree has ever
been stated by two provers. The other exporter, `gabbro lean` — the one a hand-written Lean
specification would be held against, and the one the word *arbitrary* really asks about —
emits **no theorem at all**: it carries 155 of the corpus's 296 routines that have a body
(52 %), **8 of 35 `requires` conjuncts** and **7 of 19 `ensures` conjuncts**, and 152 of
those 155 bodies promise literally `True`. For the most program-like file in the tree,
`messung/treiber/virtio-net.gab`, the numbers are 2 bodies of 6, **0 goals of 1 obligation**,
and not one clause conjunct. And a finding that was not in any register before this run:
**56 of the 61 places those exported bodies touch name a carrier that is absent from the
export's own place dictionary** — so `wellFormed`, the typing hypothesis, and any
specification a person writes from `places` speak about a region the program never writes.
That is shown three ways in Lean below, not argued.

**The sharpest single number is 10 of 44.** `programmlogik/Gabbro/Body.lean` exists to answer
exactly the obligations the Isabelle channel refuses as `body-effect` — *"speaks about the
world AFTER a body ran"* — and there are 44 of those. It answers ten. Everything else in this
file is that fraction, taken apart.

The line runs here: **`lean` type-checks a rendering, plus ten machine-generated goals.
It discharges nothing else.** 119 of the 124 modules `pruefe-lean-beweis.sh` compiles green
contain not one theorem.

---

## 1. The denominator of "arbitrary"

The corpus fed to both exporters is `beispiele/*.gab` (65) plus `messung/*/*.gab` (110) —
**175 files**. `beispiele/gift/*.gab` (432 more) is poison by construction; a file with
errors carries no export, so it is out of every denominator below by definition, not by
choice.

```
ssh ki-pc-fisch-101 'cd gabbro-le && ./instrumente/zaehle-lean.py --je-datei'
ssh ki-pc-fisch-101 'cd gabbro-le && ./instrumente/miss-lean-reichweite.py'
```

| | `pflichten --lean` (obligations) | `gabbro lean` (program) |
|---|---|---|
| files fed | 175 | 175 |
| files that yield anything | **124** | **124** |
| files with errors, so nothing | 51 | 51 |
| the unit counted | obligation | routine |
| total | **100** | **423** |
| carried | **10 goals** | **155 bodies** |
| refused by name | 90 | 268 |

**The 51 are not a shortfall of the exporter.** They are `messung/` probes and fragments
written to be rejected; `gabbro pruefe` refuses them and the export follows. What they do
mean is that "the whole `.gab` corpus" is a phrase with three different denominators in it,
and only one of them (175) is the one either exporter ever sees.

**`423` is the wrong denominator for a body.** 127 of the 268 refusals are `foreign-body` —
a routine with no Gabbro body at all, an `extern`. Nothing could be carried there. Against
routines that *have* a body:

> **155 of 296 routines with a body reach Lean — 52 %.** Against all declared routines it is
> 155 of 423, 37 %.

**And a body is all-or-nothing.** `lean::routines` runs `block_term` over the whole body and
files the FIRST form it cannot render as the reason for the entire routine (`lean.rs:1967`,
`?`-propagation). A routine of forty statements with one unrenderable form in it lands in
`refused` exactly like a routine of one. *So there is no "fraction of a body carried" to
measure: the fraction is 1 or 0, and the refusal histogram below is a table of first
failures, never of construct frequencies.* Reading it as the latter is the same error
`CLAUDE.md` books under "a measurement that stops at the first hit measures the wrong
question" — here it sits inside the emitter rather than inside a measuring script.

### The 33 reasons: which fire, how often, over what

`LeanReason::ALL` has 33 entries (`lean.rs:301`). **25 fire somewhere; 8 are silent over the
entire corpus.**

Why a ROUTINE is refused by `gabbro lean` (268, first failure each):

| reason | n | | reason | n |
|---|---:|---|---|---:|
| `foreign-body` | 127 | | `let-else` | 5 |
| `carrier-not-a-table` | 36 | | `exchange` | 4 |
| `loop` | 30 | | `float` | 4 |
| `narrow` | 11 | | `device-transition` | 4 |
| `generated-op` | 9 | | `observe` | 2 |
| `constructed-value` | 8 | | `other-value` | 2 |
| `no-term` | 7 | | `call-not-compositional` | 1 |
| `no-shape-for-field` | 6 | | | |
| `match-not-option` | 6 | | | |
| `call-in-expression` | 6 | | | |

Why a clause conjunct is dropped by `gabbro lean` — **the two lists are separate, and the
second is the one that decides what a caller may assume**:

| `requires` DROPPED (27) | n | | `ensures` NOT SAID (12) | n |
|---|---:|---|---|---:|
| `lock-witness` | 14 | | `quantified` | 10 |
| `quantified` | 10 | | `result-in-ensures` | 2 |
| `builtin` | 2 | | | |
| `call-in-expression` | 1 | | | |

Why an OBLIGATION is refused by `pflichten --lean` (90): `call-site` 24, `device-promise` 15,
`foreign-body` 12, `quantified` 10, `table-invariant` 9, `loop` 7, `walk-invariant` 5,
`carrier-not-a-table` 5, `no-shape-for-field` 2, `call-not-compositional` 1.

**The eight silent reasons, and they are not one thing:**

`await`, `compound-assignment`, `concurrent-statement`, `non-local-exit`, `old-state`,
`publish`, `result-in-body`, `spec-not-an-expression`.

* **`concurrent-statement` has no construction site at all.** `grep -n "LeanReason::Concurrent"
  crates/gabbro-check/src/lean.rs` returns exactly three hits: `tag()`, `sentence()`, and
  `ALL`. **No arm anywhere returns it.** It is unreachable code, not an unexercised guard —
  its own doc comment already says `LockStatement` took its work, and the arm stayed. A row
  that can only ever read `0` says the channel still owes something it does not; that is the
  reasoning `zaehle-lean.py` writes at the top of its own table, where it already struck
  `division-or-bits` and `result-in-ensures` for exactly this. **This is a third case of the
  same class, and `zaehle-lean.py` still carries rows for `publish`, `await` and
  `concurrent-statement` too.** *One line to remove, and `ALL` becomes 32. Named here, not
  built — this lane measures.*
* **`publish` and `await` are silent because the model GREW and the refusal stayed.**
  `publishes` appears in 15 corpus files and `awaits` in 12, and both are **carried**:
  `beispiele/05-nebenlaeufigkeit.gab` exports
  `(.publish "FARBE_FERTIG" (.lit (.bool true)) ["farbbericht"])` and
  `(.awaitLoad "fertig" "FARBE_FERTIG" ["farbbericht"])`. `Body.lean:445` models a release
  store as a plain store and says so, and licenses the visibility by an ASSUMPTION of the
  program's own axiom layer — `release_stellt_sichtbarkeit_her`, `unfalsifiable`, in
  `beispiele/06-annahmen.gab`. The two arms survive only for a `publishes` at a target with
  suffixes (`lean.rs:1188`, `1199`), which no corpus file has. *So the memory model is not
  refused here; it is assumed elsewhere, by name, where a reader can see it.*
* **The remaining five have live construction sites and no corpus site reaches them.**
  `+=` is in 18 files and is carried where the target is a local or a shaped field
  (`lean.rs:995`); `CompoundAssign` guards only `&=`/`|=` with no shape, and a `static`
  target. That is coverage, not death.

*The distinction matters for the owner's question: a reason that never fires because the
form is CARRIED tells you the channel is further along than the register suggests, and a
reason that never fires because nothing can reach it tells you the register is stale. Both
occur here.*

## 2. What the export actually CLAIMS — the three tiers, kept apart

```
ssh ki-pc-fisch-101 'cd le-probe && python3 split.py'
```

**Tier 1 — a GOAL, something to be proved.** `gabbro lean` emits **zero**. Its own header
says so: *"THIS FILE CARRIES NO SPECIFICATION."* The only goals in the tree come from
`pflichten --lean`: **10**, in 5 of 124 modules.

**Tier 2 — an ASSUMPTION, a premise the proof rests on.** This is the dangerous tier, and it
has three inhabitants in `gabbro lean`, all of them per routine:

| | n | over 155 carried bodies |
|---|---:|---|
| parameter-shape conjuncts in `_pre` (typing, read from the DECLARATION) | **122** | |
| `requires` clause conjuncts in `_pre` (what the caller grants) | **8** | of 35 stated, 23 % |
| `_pre` is `True` — nothing granted at all | **59** | 38 % |
| `ensures` clause conjuncts in `_post` (what a caller may assume) | **7** | of 19 stated, 37 % |
| `_post` is `True` — nothing promised at all | **152** | **98 %** |

> **152 of 155 exported bodies promise `True`.** A caller taking a call over the contract, as
> the export's own comment says a caller must, learns nothing whatever about 98 % of the
> program. That is the safe direction — a promise fewer makes a caller's goal harder, never
> wrong — but it is also the reason no compositional proof over this export could get off the
> ground.

**Tier 3 — DROPPED by name, and honest.** 27 `requires` conjuncts and 12 `ensures` conjuncts,
each written into the doc comment of the routine it belongs to, with its `LeanReason` tag.
Plus 268 refused routines, each on its own `-- REFUSED` line. **Nothing vanishes silently in
either exporter**, and both carry a balance line the guardians check
(`goals + refused = total`, `bodies + refused = routines`).

### The seam inside tier 2: `wellFormed` names a world the program never writes

**This is the finding of the run, and it was measured rather than reasoned.**

`gabbro lean` writes the carrier of a place from two different sources and never reconciles
them:

* `places`, `fields` and `wellFormed` come from `dictionary(&tab)` — the **table names**:
  `("Kappenraum", "benutzt", "isBool")`.
* a body's place comes from `field_shape`, which returns `base.to_string()` (`lean.rs:600`)
  — the **source name of the base**, so a routine reaching its table through a pointer
  parameter `c` emits `(.place "c" (.name "s") "benutzt")`.

`Gabbro.Body.Place.slot` carries the carrier as a `String` (`Body.lean:112`), so
`.slot "c" k f` and `.slot "Kappenraum" k f` are **different places**.

```
ssh ki-pc-fisch-101 'cd gabbro-le && ./instrumente/miss-lean-traeger.py'
```

| | |
|---|---:|
| files with an export | 124 |
| of those, with at least one place in a body or clause | 31 |
| every carrier IS in that export's own dictionary | **5** |
| at least one carrier is NOT | **26** |
| place mentions in bodies and clauses | 61 |
| of those, carrier NOT declared | **56** |

The undeclared carriers are exactly what one would expect of parameter names: `c` 16, `f` 8,
`e` 6, `k` 4, `v` 4, `r` 3, `s` 3, `p` 3, `puffer` 2, `h` 2, and six more. In
`beispiele/01-tabelle.gab` the dictionary reads `Kappenraum, Objekte` and every body and
every `_pre`/`_post` conjunct addresses `c`.

**Measured in Lean, three ways, over `beispiele/16-by-ops-am-feld.gab`** — whose export is two
routines, both carried, dictionary `Objekte`, body carrier `o`:

```
ssh ki-pc-fisch-101 'cd le-probe && LEAN_PATH=…/lib/lean:$PWD ~/.elan/bin/lean Probe.lean'
```

* **A — goes through.** `∀ k f, s'.world (.slot "Objekte" k f) = s.world (.slot "Objekte" k f)`
  after `belegen_body`. *The body provably leaves every declared place unchanged.*
* **B — goes through.** `s'.world (.slot "o" j "benutzt") = .bool true`. *The write lands on
  the parameter name.*
* **C — FALLS, and the poison direction is what makes A and B mean anything.** The
  specification a person would write from `places` — `s'.world (.slot "Objekte" j "benutzt")
  = .bool true` — leaves the goal
  `⊢ s.world (Place.slot "Objekte" j "benutzt") = Value.bool true`: **`lean` reduced the
  body's write away entirely, because it landed somewhere else.**

**Which direction is this?** Toward *unprovable*, not toward *falsely proved*: a
specification written from `places` fails, and a specification written against `"c"` gets no
`wellFormed` hypothesis and so has a harder goal. Both are the safe side. **But it is exactly
the hazard the export's own comment names** — *"a typo in that string is a specification about
a place that does not exist — vacuous rather than false, and vacuous reads like proved"* —
and here it is produced by construction rather than by a typo, for 56 of 61 places.

**And the guardian cannot see it.** `pruefe-lean-programm.sh` holds a *specification's*
places against the dictionary; nothing holds a *body's* against it. Its worked example,
`programmlogik/beispiel/betrieb.gab`, writes `Faecher.slots[f].belegt` — **the table name
directly**, with `f` an `index into Faecher` rather than a pointer. *The one worked example is
the one shape in which the gap cannot appear.* It reports `4 declared places` and green.

**The repair is not one line and is not attempted here.** Making `field_shape` return `tab`
would merge two pointer parameters aimed at one table into a single carrier — which is
precisely what the export's own header refuses (*"two different carrier names are two
different objects"*). The honest direction is the other one: build `wellFormed` from the
carriers the bodies actually address, per routine, the way `lean::module` already does from
`c.seen` (`lean.rs:1470`) — which is why the OBLIGATION channel has no such gap and its ten
theorems go through.

## 3. What green means at `pruefe-lean-beweis.sh`

```
ssh ki-pc-fisch-101 'cd gabbro-le && ./instrumente/pruefe-lean-beweis.sh'
==> 124 units -> 124 modules, 10 theorem(s) (51 without a register)
==> LEAN PROOF: 10 generated obligation(s) in 124 modules, LEAN GREEN     [exit 0]
```

Both halves of the two-way speech test fire, in both body shapes (bare and `breaking`): a
true theorem goes through, a false one falls. **So the instrument is speaking.** And then:

> **`lean` is type-checking a RENDERING, plus ten machine-generated goals. A file that
> compiles under `lean` is not a proved program.** Of the 124 modules that go green, **119
> contain not one theorem** — they consist of a body datum and a list of named refusals, and
> a module with no claim in it compiles for the same reason an empty file does. The five that
> do carry a theorem are `beispiele/01-tabelle.gab` (3), `53-zwei-orte.gab` (4),
> `03-format.gab` (1), `50-verfeinerung.gab` (1) and `messung/grammatik/messreihe.gab` (1).

The guardian says this itself, in its own closing lines, and the sentence is worth keeping:
*"what that does NOT mean: that the register is covered."* The distinction it draws is
between **valid Lean** (124 of 124) and **a discharged obligation** (10 of 100). Both are
real; only the second is a proof about a program.

`pruefe-lean-programm.sh` is green too — 4 bodies from 2 files, 5 hand-written theorems, 5 of
5 poisoned ones falling, and the undeclared place `Faecher.gewicht` correctly named. **That
guardian measures the PROGRAM export, and it is the only place in the tree where a
hand-written Lean specification is ever held against a Gabbro program.** Its subject is a
14-line and a 45-line file written for it.

## 4. The gap to "arbitrary", ranked by whether a real program has it

`foreign-body` (127) sits at the top of the histogram and is not a gap: an `extern` has no
body to carry. Below it, ranked by how surely a real systems program contains the form:

| rank | form | reason | in the corpus | can a driver avoid it? |
|---|---|---|---:|---|
| 1 | a LOOP — `traverse`, `retry`, `forever` | `loop` | 30 routines, 7 obligations | no |
| 2 | a place through a POINTER PARAMETER | *see §2* | 56 of 61 places | no |
| 3 | a CALL, taken over the contract | `call-not-compositional`, `call-in-expression` | 7 + 1 | no |
| 4 | a `transition` of a `device` — a register write | `device-transition` | 4 | not in a driver |
| 5 | a QUANTIFIER, `reaches`, a membership | `quantified` | 10 + 10 + 10 | rarely |
| 6 | a generated table operation | `generated-op` | 9 | avoidable |
| 7 | a record / `tagged` / device handle as a VALUE | `constructed-value` | 8 | avoidable |
| 8 | `narrow … to … else` | `narrow` | 11 | avoidable |
| 9 | a float | `float` | 4 | yes, in a kernel |

**The loop is the one that decides the question.** Gabbro carries the measure (`K008`/`K009`),
so termination is not the gap; what is missing is an INVARIANT, and *Gabbro has no word for
one at a loop* — `Traverse`/`Retry`/`Forever` carry no such field where `Tabelle` does. That
is a LANGUAGE gap, not an emitter gap, and it is the only entry in this table that cannot be
closed inside `lean.rs`.

### The two most program-like files, measured

**`beispiele/01-tabelle.gab`** — 177 lines, an intrusive tree over two tables:

| | |
|---|---|
| routines | 4 (3 with a body, 1 `extern`) |
| bodies carried | **2 of 3** |
| refused | `no-shape-for-field` (`blatt_loeschen`), `foreign-body` (`speicher_freigeben`) |
| obligations | 13 → **3 goals**, 10 refused |
| `requires` conjuncts | 3 dropped (`lock-witness` ×2, `call-in-expression`), 2 kept |
| places declared | 9, all under `Kappenraum` / `Objekte` |
| places addressed | all under `c` — **not one is in the dictionary** |

**`messung/treiber/virtio-net.gab`** — 254 lines, the nearest thing in the tree to a real
driver:

| | |
|---|---|
| routines | 8 (6 with a body, 2 `extern`) |
| bodies carried | **2 of 6** — `armieren`, `arp_stellen` |
| refused | `device-transition` ×4 (`stufe_anerkennen`, `stufe_treiber`, `stufe_merkmale`, `stufe_laeuft`), `foreign-body` ×2 |
| obligations | **1 → 0 goals**, 1 refused |
| `requires` / `ensures` conjuncts reaching Lean | **0 and 0** — both carried bodies have `_pre = True` and `_post = True` |
| places declared | 31 |

> **For the file that most resembles a program somebody would ship, the Lean export is two
> body data, thirty-one place declarations, and no claim of any kind.** Zero obligations
> reach a prover. *That is the most direct answer to the owner's question there is.*

## 5. The seam: do the two exporters agree about goal and assumption?

```
ssh ki-pc-fisch-101 'cd gabbro-le && ./instrumente/miss-lean-gegen-isabelle.py'
```

`lean::verdicts` and `refinement::verdicts` walk the SAME list from `pflichten::sammle`, in
the same order, numbering entries `duty_1 …`. So every obligation carries two verdicts:

| 100 obligations | Isabelle GOAL | Isabelle REFUSED |
|---|---:|---:|
| **Lean GOAL** | **0** | 10 |
| **Lean REFUSED** | 1 | 89 |

> **The intersection is empty.** Not one obligation in this tree is stated as a goal by both
> provers. The union is **11 of 100**.

The disjointness is by construction, and the exact shape of it is worth writing down. The
Isabelle channel's own histogram over the same 175 files — 100 obligations, **1 goal**, 99
refused — reads `body-effect` 44, `foreign-body` 17, `lock-witness` 15, `device-promise` 15,
`no-term` 7, `argument-not-stable` 1. And those 44 decompose exactly:

> **`body-effect` 44 = 30 `N`/`R` + 9 `E` + 5 `S`** — every obligation that speaks about the
> world after a body ran. **`programmlogik/Gabbro/Body.lean` exists to answer precisely those
> 44, and it answers 10.** That single sentence is the reach of the Lean channel, stated
> against the thing it was built for: **10 of 44, 23 %.**

The Lean channel attempts only `N` and `R` (`lean.rs::verdicts` refuses the other six kinds
in a `match p.art` before an expression is looked at, which is 70 of its 90 refusals) — so
the 9 `E` and 5 `S` are body-effect obligations that neither channel attempts at all.

**They also disagree about the NAME 62 times.** Where both refuse, the reason pair matches in
only 27 of 89 cases (`device-promise` 15, `foreign-body` 12). The rest are two different
sentences about one obligation — `quantified`/`body-effect` 10, `table-invariant`/`body-effect`
9, `loop`/`body-effect` 7, `call-site`/`lock-witness` 15, and six more. That is not itself a
defect: each channel names the thing IT is missing, and the two are missing different things.

**But one documented claim is false, and it is a claim about the other channel.**
`LeanReason::CallSite` carries, at the site, the sentence:

> *"A precondition at a call site. **Not a gap:** the Isabelle channel carries these, and
> twelve of them are discharged by the lock passes before any prover sees them."*

Measured, over the 24 obligations Lean refuses as `call-site`:

| | |
|---|---:|
| a GOAL in the Isabelle channel | **1** |
| refused by Isabelle as `lock-witness` | 15 |
| refused by Isabelle as `no-term` | 7 |
| refused by Isabelle as `argument-not-stable` | 1 |

**23 of 24 are refused by the channel that was named as carrying them.** The single one that
is a goal is `beispiele/21-verbundwert.gab` `duty_1`, `laenge_von :: fertig requires #1`. The
half of the sentence that survives is the count of lock witnesses, and even that has moved:
**15, not twelve.** *A comment that points at another module's behaviour is the one kind of
comment no test in this tree was checking — `instrumente/miss-lean-gegen-isabelle.py` now
checks this one.*

## What was built for this measurement, and what was not

Three tools, all of them measuring, none of them changing the product:

* `instrumente/miss-lean-reichweite.py` — `gabbro lean` over a corpus: header balance,
  refused routines by reason, dropped clause conjuncts by reason.
* `instrumente/miss-lean-traeger.py` — a body's carriers against the dictionary of the same
  export. **This is the tool that found §2.**
* `instrumente/miss-lean-gegen-isabelle.py` — the two exporters, obligation by obligation, and
  the `CallSite` claim held against the channel it names.

Each aborts rather than reports a partial number when its balance does not add up, and each
refuses with exit 2 (the setup is wrong, nothing was measured) rather than exit 1.

**One instrument WAS repaired, because a number this file quotes came out of it.**
`instrumente/zaehle-lean.py`'s kind table listed seven of `Art`'s eight letters — `W`,
`Walkinvariante`, was missing. The five `W` obligations were counted into its printed
`70 of 90` and appeared in no row: **the rows came to 65.** Its own balance check compares
only the SUM, and the sum was right, so nothing turned red. The row is added; the eight rows
now come to 90. *That is the fourth list over one set — `Art`, `LeanReason::ALL`, `GRUENDE`,
and this table — and the comment beside `walk-invariant` in that same file names only three.
The repair on 2026-09-01 reached the third and stopped one short.*

**Repairs found and deliberately NOT made** — this lane measures, and a measuring lane that
starts building stops measuring:

1. `LeanReason::Concurrent` is unreachable (no construction site). Removing it makes `ALL`
   32 and removes a row that can only read `0`. `zaehle-lean.py` carries the same dead row,
   plus `publish` and `await`, whose arms are alive but unreachable from the corpus.
2. `wellFormed` and the bodies disagree about the carrier (§2). Not one line; the direction
   is to build the dictionary from the carriers the bodies address, per routine, as
   `lean::module` already does.
3. `pruefe-lean-programm.sh` needs a second example whose routine reaches its table through a
   pointer parameter. Its present one cannot exhibit the gap.
4. The `LeanReason::CallSite` comment states something false about the Isabelle channel (§5).

*Nothing in the tree was changed by this run beyond the three tools and this file. The ratchets
were not touched.*
