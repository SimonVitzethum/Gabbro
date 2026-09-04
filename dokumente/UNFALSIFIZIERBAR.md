# The bar for `unfalsifiable` — written **before** a single row was classified

**The grammar already forces the tail.** `assume`, `axiom` and `retires` take either
`falsifier <probe>` or `unfalsifiable "<reason>"`, and the absence of both is a translation
error (`dokumente/SYNTAX.md`:1540). *That* a reason stands is therefore the parser's work and
not anybody's care — `messung/AXIOMSCHICHT.md` says so about its own count: *„Die Zahl misst
hier die Grammatik, nicht die Sorgfalt."*

**What the reason has to SAY has never been written down.** Until it is, `unfalsifiable` is
the cheapest exit from every assumption whose probe is expensive, dangerous or merely absent.

> `dokumente/PLAN.md` §`K100.2` predicts the category and its first member in the same
> sentence: *„**Zwei davon werden vermutlich unfalsifizierbar sein** — eine Sonde für „die MMU
> schreibt nur `A` und `D`" müsste die MMU anhalten."*
>
> `K100`'s gate is `A = 19`; the corpus stands at **44**. If *"unfalsifiable with a reason"*
> is defined while the classification runs, the gate closes by twenty-five assumptions
> becoming unfalsifiable — **and then it was not passed, it was emptied.**

**So the bar stands here first.** It was written against tree state `6a32f27`, on 2026-09-04,
**before any of the eight live `unfalsifiable` clauses had been looked at one by one** — the
register at the bottom of this file was filled in afterwards, from the bar, and its verdicts
can therefore be checked against criteria that did not know them.

---

## What a probe is — and therefore what falsifiability means here

A `falsifier` names an **external** program. `crates/gabbro-check/src/namen.rs`:3242 has held
it since 2026-08-19: *"`expects` names an EXTERNAL probe, like `assume … falsifier`: it does
not stand in Gabbro because it RUNS"*, and `sonden/README.md` gives it a three-valued
contract:

| return | means |
|---:|---|
| **0** | not refuted in this run — *and that is ALL it means* |
| **1** | **REFUTED**, or the probe proved itself blind |
| **77** | not runnable here — no device, no privilege, one core |

**Two consequences do most of the work below.**

* **Falsifiability is the RED direction.** An argument that no run could ever *confirm* the
  assumption says nothing about whether one could *refute* it. `sonden/README.md` found this
  in a live row and named it: *„Der Satz ist wahr, und er ist ein Argument über die GRÜNE
  Richtung. Falsifizierbarkeit ist die rote."*
* **"Not runnable here" already has a home, and it is not this category.** Return code **77**
  is the slot for *no device, no privilege, one core*. An assumption whose probe would return
  77 on today's bench is falsifiable and unrun — a different thing from unfalsifiable, and the
  distinction costs nothing because the slot exists.

---

## The two criteria

**A criterion that admits everything classifies nothing.** Each one below therefore carries a
test a reader can apply and a statement of **what fails it**. Both are written so the answer
can be *no*, and the register at the bottom records where it was.

### `U1` — the observation IS the violation

> There is no way to arrange the refuting observation without performing, as part of the
> arrangement, an instance of exactly what the assumption denies. A witness and a broken bench
> are then the same picture, and no probe can tell them apart **in principle**.

**The test.** Write down the probe's setup, step by step. If some step is itself an instance
of the event the assumption says does not happen, `U1` holds. If the probe can be a passive
reader — a snapshot and a compare, a counter, a fault handler, a timing difference — `U1`
fails.

**What fails it.** Everything a *read* can settle. A probe that only looks does not disturb
what it looks at, and then the arrangement is innocent of the outcome. **In particular a probe
that must merely be dangerous, privileged or slow does not pass `U1`** — see *Three things
that are not reasons* below.

*This is the criterion `PLAN.md` §`K100.2` names, and the shape it names is the right one: a
probe that would have to stop the machine it observes.*

### `U2` — the negation has no finite witness

> The refutation would have to be an infinite object. No bounded run distinguishes *never*
> from *not yet*, and the assumption names no bound that a run could exceed.

**The test.** Write the negation and ask what a witness of it looks like. *"An IPI is sent and
never arrives"* has no finite witness; *"a status register did not report `fertig` within the
promised read operations"* has one, and it is the read after the last.

**What fails it.** Every assumption that already names a bound. The corpus writes exactly
that bound in three sentences — *„tut es innerhalb der zugesagten Leseoperationen"*
(`geraet_antwortet`, `karte_antwortet`, `zaehlwerk_antwortet`) — and two more name one of
their own (`leser_holt_ab`, `eingabe_endet`). **So an unbounded liveness sentence here is a
choice, not a necessity.**

> **The rider, and it is what keeps `U2` from being a bin.** `U2` admits the sentence **as
> written**; it does not certify that the sentence had to be written that way. A row admitted
> under `U2` therefore carries a standing repair: *write the bound, and the row leaves this
> register.* **That is a fall of the ratchet anybody can buy** — which is what a category with
> an exit looks like.

---

## The four rejection rules

Each of these has already caught a live row. They are the half of the bar that says *no*.

### `R1` — a green-direction reason is not a reason

The reason explains why no run could ever **establish** the assumption. That is a true and
useful sentence about a different question. Falsifiability asks whether one observation could
**end** it.

**The test.** Name one observation that, made once, would kill the assumption for good. If you
can name it, `R1` fires, however true the written reason is.

*Found by `sonden/README.md` and `messung/RACE.md` §5.2 in `release_stellt_sichtbarkeit_her`
— and the probe for it was built the same day.*

### `R2` — a reason about the bench is not a reason about the sentence

*"qemu64 has no x2APIC"*, *"the effect is not observable on this machine"*, *"no device
here"*, *"no privilege here"*. These are statements about where the probe would run.

**The test.** Would the reason still be true on the machine the assumption's `arch` clause
names? If not, `R2` fires — and the row belongs to return code **77**, not to this category.

*`messung/AXIOMSCHICHT.md` already called this class the weakest of its six, in the same
words: the reason is „kein Grund über die Sache … sondern über die Testmaschine".*

### `R3` — the subject is not the environment

A probe measures the **environment** (`sonden/README.md`: *„Eine Sonde misst die Umgebung"*,
and: *„Keine Sonde, die den Prüfer ausführt"*). A sentence about the toolchain, about the
checker, or about the program's own text has no external probe **by construction**.

**The test.** Does the sentence mention a machine at all? If it does not, `R3` fires — and the
row is **not unfalsifiable, it is misfiled**. What can refute such a sentence is a pass, a
poison probe or a mutation, and all three exist.

### `R4` — if nothing observable rides on it, nothing rests on it

If **no** observation could distinguish the assumption's truth from its falsity, then no
program's behaviour depends on it either. Such a sentence is not an unfalsifiable load-bearing
assumption; it is **empty**, and it belongs in *not an assumption of the axiom layer*.

> **`R4` is why this category cannot become a refuge, and it is worth saying plainly:**
> *"unfalsifiable" and "load-bearing" pull against each other.* The only rows that can be both
> are the ones where the **consequence** is real and the **observation of the violation** is
> blocked because observing requires causing. That is `U1`, and it is the whole of the
> overlap. Everything that reaches this category by *"nothing could ever see it"* is thereby
> shown to carry no trust — and a row that carries no trust is not an exception to `A`, it is
> a subtraction from it.

#### `R4` is a HEURISTIC, and its exception has a name in this very file

**Tested on 2026-09-04, in the direction it had never been pushed.** *A rule that has only
ever been applied one way has not been tested* — so: construct an assumption that **nothing
can refute** and that something **genuinely rests on**. If it exists, `R4` is not sound.

**It exists, and it is row 1 of the register below.**

The slip is not in `R4`'s inference — that one is valid as written. *If* no observation
whatever distinguishes A from ¬A, then no program can behave differently under the two, and
nothing rests on it. **The slip is in applying it to a row because the row is
`unfalsifiable`.** This document says twice, in its own words, why that step does not carry:

> *„Der Satz ist wahr, und er ist ein Argument über die GRÜNE Richtung. Falsifizierbarkeit
> ist die rote."*

`unfalsifiable` quantifies over **refuting** observations. `R4`'s antecedent quantifies over
**all** of them. **The antecedent is strictly stronger than membership in the category it
polices**, so no row can be moved under `R4` merely for being in the category — it needs the
extra premise that nothing observes it in either direction, and that premise has to be argued
separately.

**And `U2` is exactly the class where the extra premise is FALSE.** Take `ipi_kommt_an` —
*„Ein gesendetes IPI erreicht den Zielkern in endlicher Zeit."* No bounded run refutes it;
*never* and *not yet* are the same picture. But every arrival **confirms** it, and a program
that waits on the acknowledgement **terminates if and only if the assumption holds**.
*Terminating versus hanging forever is as load-bearing as a program behaviour gets.* So: an
assumption nothing can refute, which something genuinely rests on. `R4` does not reach it,
and the register admits it under `U2` — correctly, and for a reason `R4` would have denied.

**Can it be built in Gabbro TODAY?** Yes, and the search for it is what turned up `O013`:

| construction | state |
|---|---|
| `retires t from boot unfalsifiable "…"` — layer S3 of the boot theorem rests on it | **was writable.** `beispiele/07` with the tail swapped checked `41 items, 0 errors, 0 hints`, exit=0. **Closed the same day by `O013`** |
| `assume ein_kern … unfalsifiable "…"` — buys every `H013` exemption | **writable.** `geteilt.rs`:532 asks `contains_key` and never the class |
| `assume gnadenfrist… unfalsifiable "…"` — carries the whole grace period of an `rcu … reclaims` | **writable.** `H015` collects `ItemArt::Assume` and never reads `a.klasse` |
| a wait loop with **no `progress` clause at all** | **writable, and no latch can ever close it.** `progress` is optional (`SYNTAX.md`:1002, 1012: `[ "progress" ident ]`), and one of the 19 loops in the clean corpus carries none — `beispiele/66-transport-rueckgabe.gab`:66 |

**So the honest statement, and it is worth more than the rule was.** Where the checker can
SEE that a construct rests on an assumption, `"unfalsifiable ⇒ carries nothing"` is true —
**and it is true by REFUSAL, not by inference.** `S004`, `N005`, `N031` and `O013` make the
counterexample unwritable at those four sites, which is why the bin came out nearly empty.
Everywhere else — at the two `geteilt.rs` sites, and at every dependency the text does not
name — the inference is simply invalid, and `U2` is the standing counterexample.

*`R4` should therefore be read as a consequence of the latches rather than as a piece of
reasoning: it names the shape the language enforces, and it does not license moving a row on
its own.* **Row 4 of the register (`mmu_schreibt_nur_a_und_d`) survives that correction** —
its argument is that a snapshot-compare settles the question, i.e. that the sentence is
observable in **both** directions, which is `R4`'s real antecedent and not the weak one.

---

## The category already has a PRICE, and it is not this document's invention

**`unfalsifiable` is not free in the checker either.** This section said *"two passes"* when
it was written on 2026-09-04. **It was FOUR by the end of the same day, and the fourth was
built because the enumeration was done properly:** every site in the grammar and in the
passes that lets a construct rest on an assumption, not the two that came to mind.

| code | site | what it says |
|---|---|---|
| `S004` | `progress <name>` | *"`progress …` rests on an unfalsifiable assumption"* — `crates/gabbro-check/src/schleifen.rs`:239. *„Eine unfalsifizierbare Fortschrittsannahme nimmt dem Wachhund seinen Gegenstand."* |
| `N005` | `entrust … assume <name>` | *"`entrust …` rests on an unfalsifiable assumption"* — `namen.rs`, with the note *"an assumption about foreign code that no probe can ever refute belongs in the certificate, not in a pass"* |
| `N031` | `atomic … observed by <name>` | *"`observed by …` names an assumption without a falsifier"* — `namen.rs`:4374. **This one was already there and this document did not know it**, which is why its population figure was one too low |
| `O013` | `retires <tok> from <space>` | *"… retires `t`, and the retirement rests on an unfalsifiable assumption"* — `phasen.rs`, built 2026-09-04. The clause declares its assumption INLINE instead of naming one, and until that day nothing read its class |

**Measured over the 44:** **twelve** are named by a `progress`, an `entrust` or an
`observed by`. *The eleven this section first claimed was the same measurement with `N031`
left out of the union.*

```bash
ssh … './target/release/gabbro annahmen beispiele/*.gab' | grep -E "^A[0-9]+" | cut -f2 | sort > /tmp/n44
{ grep -rhoE "progress [a-zA-Z_0-9]+"    beispiele/*.gab | sed 's/progress //'
  grep -rhoE "^[[:space:]]*assume [a-zA-Z_0-9]+;" beispiele/*.gab | sed 's/[^a-z_]*assume //;s/;//'
  grep -rhoE "observed by [a-zA-Z_0-9]+" beispiele/*.gab | sed 's/observed by //'; } | sort -u > /tmp/p
comm -12 /tmp/n44 /tmp/p | wc -l
# 12   -- the twelfth is `karte_liest_nach_dem_index`, beispiele/41-handschlag.gab:49
```

`O013` adds none of the 44: the assumption a `retires` carries is GENERATED out of the
clause (`stilllegung_<fn>_ist_unerreichbar`) and appears in `gabbro annahmen` per file, not
in the corpus-wide set this table counts. **Its price is paid all the same** — measured over
the whole tree, 648 `.gab`: four `retires` clauses, all four `falsifier`, so the rule refuses
nothing that stands today.

> **More than a quarter of the population cannot be binned at all**, and the refusal is older
> than this bar. *That is worth saying because it bounds what this document can be blamed for
> and what it can take credit for:* the language already priced the word at the sites where an
> assumption CARRIES something. What it never priced is the word standing alone — and 32 of
> the 44 stand alone.

### And the enumeration found two sites where the price is NOT charged

**Both are in `geteilt.rs`, both read an assumption and neither reads its class.** They are
named here rather than fixed because that file is another lane's; the repair is one line each.

| site | what it buys | what it asks | what it does not ask |
|---|---|---|---|
| `geteilt.rs`:532 | every `H013` exemption in the context matrix («K5.3») | `crate::annahmen(baum).contains_key("ein_kern")` | whether `ein_kern` is falsifiable. *The comment three lines above asserts it is:* „Die Annahme steht damit im Zeugnis und **hat einen Falsifikator**" |
| `geteilt.rs`:309–319 (`H015`) | the whole grace period of an `rcu … reclaims` | that SOME `assume` names the domain | `a.klasse`. **And its own note cites the model it is missing half of:** *"the assumption names WHO GUARANTEES it, **the way `progress` names who ends the loop**"* |

*Measured, so that the repair is known to be free:* one `ein_kern` in 648 `.gab`
(`beispiele/gift/231`, `falsifier sonde_zweiter_kern`) and three grace-period assumptions
(`beispiele/31`, `/42`, `gift/272`, all `falsifier sonde_leser_noch_drin`). **Neither repair
refuses a single file that stands today.**

---

## Three things that are **not** reasons

The bar `dokumente/AUSNAHMEN.md` sets for `E2` transfers whole: **structural, not difficult.**

| not a reason | why |
|---|---|
| **cost** | *"nobody has written it"* is a state of the tree, not of the sentence. |
| **danger** | a probe is allowed to be destructive — it lives OUTSIDE the tree of checked programs for exactly that reason, and returns 77 where it may not run. |
| **privilege** | ring 0, a second core and a real device are `77`, one and all. `messung/RACE.md` §5.4 already sorts 26 named probes by which of the three they need; not one of those rows is an argument about falsifiability. |

*If a better bench, a written probe or more time could move the row, it does not belong here —
the same test `AUSNAHMEN.md` states, and for the same reason.*

---

## The register

**Every `unfalsifiable` clause that stands in the tree has a row here, admitted or refused.**
The population is the non-poison corpus: `beispiele/*.gab` (which is what `A` is measured
over), `messung/**/*.gab`, and the entries the checker GENERATES. `beispiele/gift/` is
excluded on purpose — a poison file is a program built to be refused, and its assumptions are
not part of anybody's trust surface.

| # | assumption | site | verdict | rule | since |
|---|---|---|---|---|---|
| 1 | **ipi_kommt_an** | `beispiele/06-annahmen.gab`:76 | ADMITTED | `U2` | 2026-09-04 |
| 2 | **x2apic_zweischritt** | `beispiele/06-annahmen.gab`:72 | REFUSED | `R2` | 2026-09-04 |
| 3 | **wbinvd** | `beispiele/06-annahmen.gab`:84 | REFUSED | `R2` | 2026-09-04 |
| 4 | **mmu_schreibt_nur_a_und_d** | `beispiele/06-annahmen.gab`:190 | REFUSED | `R4` | 2026-09-04 |
| 5 | **release_stellt_sichtbarkeit_her** | `beispiele/06-annahmen.gab`:194 | REFUSED | `R1` | 2026-09-04 |
| 6 | **sperrabdruck_haelt_fremde_kerne_fern** | `crates/gabbro-check/src/manifest.rs`:167 | REFUSED | `R1` | 2026-09-04 |
| 7 | **gcmd_kein_rmw** | `messung/fragmente/F02.gab`:173 | REFUSED | `R1` | 2026-09-04 |
| 8 | **fach_zahl_passt_in_den_index** | `messung/einheit-proben/prog-vorrat.gab`:27 | REFUSED | `R3` | 2026-09-04 |

**8 rows of 8 clauses in the tree, 1 of them ADMITTED** —
`./instrumente/pruefe-unfalsifizierbar.py`, and both figures are ratchets in it.

The sentences behind the verdicts:

* **1 `ipi_kommt_an`** — *„Ein gesendetes IPI erreicht den Zielkern in endlicher Zeit."*
  Negate it and the witness is an infinite run. The written reason (*„Lebendigkeit fällt unter
  keinen Mechanismus dieser Sprache"*) is about **Gabbro** and would have fired `R3`; the
  sentence survives on `U2` instead, which is a different and better reason than the one it
  carries. **Its repair stands with it:** three neighbours bound the same shape with *„tut es
  innerhalb der zugesagten Leseoperationen"*, and a bound would move this row out. *And it is
  the ONE row that can be admitted at zero cost:* no `progress` and no `entrust` names it, so
  neither `S004` nor `N005` reaches it — **the assumption stands in the certificate and
  carries nothing.**
* **4 `mmu_schreibt_nur_a_und_d`** — the seed of `PLAN.md` §`K100.2`, and it does **not** pass
  the criterion that sentence names. A refutation needs a page-table entry to be *found*
  changed, not to be *watched* changing: snapshot the entry, run a workload, snapshot again,
  compare. Nothing in that setup stops the MMU, so `U1` fails. What is left over — a change
  the MMU makes and undoes inside one instruction — is `R4`: no program can depend on a
  difference no observation can make.
* **5, 6, 7** — three reasons that argue the green direction. Two are memory-model sentences
  (*„eine erfolgreiche Probe zeigt nur, dass die Umordnung diesmal ausblieb"*); the third,
  `gcmd_kein_rmw`, says a probe would have to open the window the mechanism defends. Opening
  it is the **experiment**, not the violation — the assumption asserts that an unwritten bit
  is cleared, and one write with one read-back settles it. **For 5 the probe already exists as
  a program** (`sonden/sonde_release_sichtbarkeit.c`, with a positive control that fell 3 079
  times), which is the sharpest single fact in this table: *the tree contains the refuting
  instrument for an assumption it books as unrefutable.*
* **8 `fach_zahl_passt_in_den_index`** — *„eine Sonde muesste den Uebersetzer selbst befragen,
  nicht die Maschine"*, and that is the rejection written out. It is a compile-time fact about
  a cross-unit bound, and the file says so itself: the `.gabi` does not carry it. It belongs
  to a pass, not to the axiom layer.

> **What this table does NOT say.** It does not say the eight sentences are false, nor that
> the seven refused ones are cheap. A refusal moves a row from *unfalsifiable* to *falsifiable
> and unprobed* — **which is the more expensive place to stand, not the cheaper one.** The
> refusals raise the debt; they do not discharge it.

---

## The guardian

```
./instrumente/pruefe-unfalsifizierbar.py
```

Three teeth, because each alone is satisfiable by accident.

1. **Set equality against the corpus.** Every `unfalsifiable` clause found in the tree has a
   row, and every row names a clause that is there. *A row cannot be created by editing this
   table, and a clause cannot be created without one.*
2. **Two ratchets, and the smaller one is the sharp one.** The **population** may fall and not
   rise; the **admitted** count may fall and not rise. Raising either is a diff in the
   guardian, which is what stops the category from filling up quietly.
3. **Every row names a rule that is defined above**, and the verdict has to match the letter:
   `ADMITTED` takes a `U`, `REFUSED` takes an `R`. *A fresh reason invented at the moment of
   classification has nowhere to go.*

*An empty table is a **refusal**, not a pass* — over zero rows all three teeth hold, and the
greenest run this guardian could produce would be the one where it looked at nothing.

**And what it does not do:** it does not decide whether a criterion was applied correctly.
That is the fourth column, and no script reads it. What it excludes is the one thing a script
can — that the category grows without anybody seeing it, and that a row stands under a reason
nobody wrote down. *The same division of labour `pruefe-ausnahmen.py` states about itself.*
