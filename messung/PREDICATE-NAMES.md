# The names a predicate may write — 19 positions × 20 kinds, measured

*Measured 2026-09-02 against the checker at `01d69b2`, then again against the repair. Every
number below names the file that recomputes it. Compute on `ki-pc-fisch-101`
(`gabbro-nr` for the repair, `gabbro-nr-vor` for the unchanged checker), the per-file
`gabbro pruefe` runs on the workstation — `free -g` there read 31 GB total, 21 GB available.*

> **The question this answers is not "is a check missing".** A predicate leaves this compiler
> as an ASSUMPTION: `gabbro lean` writes a `requires` into `<fn>_pre`, *"what the caller
> grants"*, and `gabbro pflichten --isabelle` books the rest as named refusals. A conjunct
> over a name that exists nowhere is therefore **a wrong proof object**, not a missing
> finding — and unlike a dropped conjunct, which the Lean channel names out loud, it is
> visible in no channel at all.

---

## 0 The result in one line

| | before | after |
|---|---:|---:|
| position × name-kind cells where a name nothing declares is accepted | **266 of 380** | **131 of 380** |
| predicate positions that resolve a name at all | **3 of 19** | **17 of 19** |
| `Has(…)` forms accepted, 11 written forms × 6 positions | **64 of 66** (`0 errors`) | **30 of 66** |

The three positions that had a reader were `ensures` (`M109`, `m1.rs`), a `format … where`
(`N032`, `namen.rs`) and a device promise (`N053`, `namen.rs`, built the same morning).

---

## 1 The method, and the correction it needed

The `W24` prelude, position by position: write the predicate with a name nothing declares,
run the **unchanged** checker, record the literal output. Nineteen positions — every place
the grammar produces a `pred` that a writer can fill with an arbitrary expression — against
twenty kinds of name.

**Eighteen of nineteen templates must check clean before a single case is run.** The
nineteenth, `fnptr … requires`, must fall at `N037`, because the form itself is refused. The
first run of the baseline found **fourteen templates that did not check clean**: a `format`
head written `: u64 le` instead of `endian little`, a `traverse` without `by unvisited`, a
`forever` whose `on_exceeded` named a function that returns, a `check` whose `can_fail` gave
no verdict. *A sweep over templates that do not parse measures the parse error, not the
question* — the lesson `fuzze-grenzen.py` paid for in `AUDIT-2026-09-02.md` §3.2, and it
came due again here.

### 1.1 The sharpening that changed the answer by 38 cells

The first sweep put the phantom name **alone** in the clause and counted every refusal as a
reader. **Two of them are not.**

```text
check … floor GIBTESNICHT == 1                       ->  N022
check … floor ZAEHLER >= 0 && GIBTESNICHT == 1       ->  0 errors, 0 hints

group … invariant GIBTESNICHT == 1                                    ->  U007
group … invariant (forall s in slots of Erste : …) && GIBTESNICHT == 1 ->  0 errors, 0 hints
```

`N022` asks whether a one-sidedly compared quantity has a `floor`; `U007` asks whether a
group invariant names at least two carriers of the group. **Neither asks whether the name
exists.** Put the phantom beside a legitimate conjunct and both go silent — *a rule that
only fires over an otherwise empty clause answers "is this clause about anything", not "does
this name exist".*

The counter-check in the same run: `M109`, `N032` and `N053` keep speaking under exactly the
same treatment. **Those three are readers, those two are not.**

Every cell in the tables below therefore carries `(<a legitimate conjunct>) && (<the
phantom>)`, and the baseline is the legitimate conjunct alone.

### 1.2 What is in the denominator

**19 positions** — the `Pred`-bearing slots of `ast.rs`, one per grammar production:
`fn … requires`, `fn … ensures`, the body of a `spec fn`, the `invariant` of a `table`, a
`walk` and a `group`, the `invariant` of all three loops, the `until` of a `retry`, the
`down` and `leaf` of a `walk`, `reg … requires`, `transition … requires`,
`axiom … requires`, `check … floor`, the `when` of a compare-exchange, the `where` of a
`format` field, and the contract at a function-pointer type.

**20 name kinds** — a bare name, a call, a field of a resolving carrier, an unknown carrier,
the place of a quantifier domain, the place of a `member` domain, `Has(F)`, `Held(L)`,
`old(x)`, `result`, `&f`, `sizeof`, `lenof`, `aligned`, a literal index past the declared
length, a `reason` case, a quantifier variable nothing binds, `Self` at a function, a device
register field, and `Has(<a lock of this unit>)`.

*Five of the twenty are legitimate in some position and must stay silent there* — that is
the counter-direction, and §4 lists which corpus file forces each.

---

## 2 The table, before

`.` is `0 errors, 0 hints`; a code in brackets is a HINT and not a refusal.

| position | bare name | call | field | carrier | domain | member | Has | Held | old | result | &f | sizeof | lenof | aligned | index | R::F | loose var | Self | reg.field | Has(lock) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| `fn … requires` | . | (E009) | . | . | D017 | D017 | (E009) | (E009) | . | . | . | . | . | . | M141 | . | . | . | . | (E009) |
| `fn … ensures` | M109 | (E009) | . | M109 | M109 | . | E009,M109 | E009,M109 | M109 | M109,M110 | M109 | M109 | M109 | M109 | M141 | . | M109 | M120 | M109 | E009,M109 |
| `spec fn` body | . | . | . | . | D017 | D017 | . | . | . | . | . | . | . | . | M141 | . | . | . | . | . |
| `table … invariant` | . | . | . | . | D017 | D017 | . | . | . | . | . | . | . | . | M141 | . | . | . | . | . |
| `group … invariant` | . | . | . | . | D017 | D017 | . | . | . | . | . | . | . | . | M141 | . | . | . | . | . |
| `walk … invariant` | . | . | . | . | D017 | D017 | . | . | . | . | . | . | . | . | M141 | . | . | . | . | . |
| `walk … down` | . | . | . | . | . | . | . | . | . | . | . | . | . | . | . | . | . | . | . | . |
| `walk … leaf` | . | . | . | . | . | . | . | . | . | . | . | . | . | . | . | . | . | . | . | . |
| `traverse … invariant` | . | . | . | . | D017 | D017 | . | . | . | . | . | . | . | . | M141 | . | . | . | . | . |
| `retry … invariant` | . | . | . | . | D017 | D017 | . | . | . | . | . | . | . | . | M141 | . | . | . | . | . |
| `retry … until` | . | (E009) | . | . | D017 | D017 | (E009) | (E009) | . | . | . | . | . | . | M141 | . | . | . | . | (E009) |
| `forever … invariant` | . | . | . | . | D017 | D017 | . | . | . | . | . | . | . | . | M141 | . | . | . | . | . |
| `reg … requires` | N053 | . | . | N053 | . | . | N053 | N053 | N053 | N053 | . | N053 | N053 | N053 | . | . | N053 | N053 | N053 | . |
| `transition … requires` | N053 | . | . | N053 | . | . | N053 | N053 | N053 | N053 | . | N053 | N053 | N053 | . | . | N053 | N053 | N053 | . |
| `axiom … requires` | . | . | . | . | . | . | . | . | . | . | . | . | . | . | . | . | . | . | . | . |
| `check … floor` | . | . | . | . | . | . | . | . | . | . | . | . | . | . | . | . | . | . | . | . |
| exchange `when` | . | E009,K003 | . | . | . | . | E009,K003 | E009,K003 | . | . | . | . | . | . | . | . | . | . | . | E009,K003 |
| `format … where` | N032 | N032 | N032 | N032 | N032 | . | N032 | N032 | . | N032 | N032 | . | . | N032 | N032 | . | N032 | . | N032 | N032 |
| `fnptr … requires` | N037 | N037 | N037 | N037 | N037 | N037 | N037 | N037 | N037 | N037 | N037 | N037 | N037 | N037 | N037 | N037 | N037 | N037 | N037 | N037 |

**Four positions were silent in all twenty kinds**: the `down` and the `leaf` of a `walk`,
the `requires` of an `axiom`, and the `floor` of a `check`. The first three are the
assumption tier's own clauses.

### 2.1 The two cells that named the whole finding

`beispiele/01-tabelle.gab`:90, the same line, two edits:

```text
requires gibt_es_nicht(s) == 0   ->  0 errors, 3 hints [E009]   Lean: DROPPED
requires GIBTESNICHT == 1        ->  0 errors, 0 hints          Lean: EXPORTED
```

The call form falls — as a hint, but it falls, and `gabbro lean` prints
*"DROPPED from the precondition (a hypothesis fewer makes the goal harder…)"*. The bare-name
form does neither. It misses the call graph entirely, and the Lean channel **can** say it:

```lean
∧ eval s (.bin .eq (.global "GIBTESNICHT") (.lit (.int 1))) = some (.bool true)
```

`Gabbro/Body.lean` carries the world as a TOTAL map, so `f_pre` is not vacuous but
*satisfiable* — a grant about a state no Gabbro program can be in. **The prover does not
check what the checker declined to look at; it assumes it.**

---

## 3 The repair

### 3.1 `D021` — the base name of a place in a predicate resolves

One rule, at the exhaustive position walk that `domaene.rs` already carries and `m1.rs`
already calls; `M141` stands in the same line of the same arm. The resolution is `D017`'s,
word for word — parameter or local, global, a resolvable type or constant, a `table`, a
`walk`, a `format`/`device` head, and (§4) a register of a device.

Four positions had to be hooked up first, and each was measured silent in all twenty kinds
before it was: the `down` and `leaf` of a `walk` (the binder is `it`), the `requires` of an
`axiom` (its parameters are its local view), the `floor` of a `check`, and the `when` of a
compare-exchange — the one position on the whole list that **runs**.

### 3.2 `N054` — a feature demand names ONE feature, and a feature is a bare name

§5. The other direction of the same tier, and the half that needs no list.

### 3.3 A defect repaired without a new refusal — `Has(F)` is not a call edge

There is no `PredArt::Has`: the form is spelled as a call and every reader matches on the
callee name. The call-graph collector did not, and the result was a **false hint on a
correct program**:

```text
impl fn jetzt() -> u64 requires Has(RDTSCP) effects { reads uhr } costs <= 40 ops
  -> hint: [E009] the call effects of `jetzt` are undecidable: `Has` is unknown to the graph
```

`requires Has(X)` at a function is exactly the form `N016` was built to propagate
(2026-08-19), and the effect hull read the same words as an edge to a function nobody
declared — then declared itself a LOWER BOUND for the whole function. *One construct, two
readers, and the second says the writer mistyped a name.*

`Held(L)` has the same shape **the moment brackets stand around it**: `(Held(L))` parses as
`PredArt::Klammer` over a comparison, and the lock demand becomes an ordinary call. Both are
now filtered at the collector (`lib.rs::ist_praedikatswort`), and the counter-direction is in
the speech test: a real unknown callee in a `requires` still makes the hull a lower bound.

> **That the bracketed `Held(L)` loses its lock demand at all is a finding of its own, and it
> is NOT repaired here.** It is a parser question — whether `Has`/`Held` should be predicate
> forms wherever a predicate may stand — and it belongs to whoever owns the lock pass.

### 3.4 What it found in the tree on its first day

`messung/fragmente/F01.gab`:189 writes

```gabbro
spec fn cdt_wohlgeformt(c : ptr<normal, r> CapSpace) -> bool
    effects { pure }
    = forall s in slots of c : c.slots[s] reaches WURZEL via parent;
```

byte for byte the excerpt's own line (`FRAGMENTE.md`:190) — and **no unit of that file
declared `WURZEL`.** `beispiele/01-tabelle.gab` carries the same predicate and declares the
constant inside its own `table`; the excerpt kept the use and lost the declaration.

*It was invisible for the same reason `QMAX` in `F04` was invisible until `N053` was built
that morning:* the name sat in a `spec fn` body, and `M109` reads only an `ensures`. One
ADDED line, the same treatment the `tree` edge and the `reason` above it already had.

---

## 4 The exemptions, and the file that forces each

A predicate legitimately names things a body cannot. **A resolver that started refusing those
would break correct programs**, so every exemption here is a measurement and not a taste.

| exempt | why | forced by |
|---|---|---|
| `result` | `ExprArt::Ergebnis` is its own variant; `alle_orte` never yields it | every `ensures` of the corpus |
| a `reason` case `R::F` | `ExprArt::Grund` is its own variant, and for the same reason | `beispiele/01`, `beispiele/43` |
| a quantifier variable | the quantifier declares it; it stands on `geb` | `beispiele/01`:78, and 53 corpus quantifier sites |
| a `traverse` variable, a `match` binder | declared by their own line — the false refusals of 2026-08-31 | `beispiele/04`, `beispiele/39` |
| `it` in a `walk` step | the declaration binds it and nothing else does | `beispiele/07-seitentabelle.gab`:28 |
| `Self` | the carrier question, and `M120` owns it | `beispiele/01`:78, every `table … invariant` |
| everything in `ensures` | `M109` reads every name of a postcondition; two refusals for one fault is worse than one | `programmlogik/beispiel/betrieb.gab` |
| the argument of `Held(…)` | a lock is not a value, and the form is spelled as a call | `beispiele/01-tabelle.gab`, `Held(KAPPEN)` at every `impl fn` |
| the argument of `Has(…)` | a machine feature is not a program name | `beispiele/11-grammatikbefunde.gab`, `Has(RDTSCP)` |
| a register of a device | declared in the unit; the four declaration maps carry device HEADS and not their registers | `messung/fragmente/F09.gab`:72, `down : roh when EINTRAG.PS == 0` |

**The last one is a measured repair of the rule and not a design decision.** `D021`'s first
build refused `EINTRAG`, and `EINTRAG` is a `reg` of `device Seitentabelle` in the same
file. *A refusal about a name the program declares is a refusal about the pass* — the
sentence `domaene.rs` already writes one rule up. Whether a walk step may reach for a device
register at all is a different question and belongs to whoever owns the walk lowering; this
rule asks only whether the name exists.

**The exemption of the two pseudo-calls is by NAME and not by site**, exactly as
`namen.rs::zusagenstelle` does it: a predicate that writes `Has(F)` and `F.x == 1` in one
breath exempts `F` in both. That is coarse, and it is coarse in the quiet direction.

---

## 5 `Has(…)` — checkable, and where the line runs

**Feature names are checked against nothing, and that was measured before it was decided.**
Eleven written forms across six predicate positions, the unchanged checker:

| form written | before | after |
|---|---|---|
| `Has(GIBTESNICHTAUFDERWELT)` | accepted (`E009` hint at a `fn`) | accepted |
| `Has(SPERRE)` — a lock of this unit | accepted | accepted |
| `Has(Platten)` — a table of this unit | accepted | accepted |
| `Has(GRENZE)` — a constant of this unit | accepted | accepted |
| `Has(rdtscp)` — lower case | accepted | accepted |
| `Has(7)` | accepted | **`N054`** |
| `Has(GRENZE + 1)` | accepted | **`N054`** |
| `Has()` | accepted | **`N054`** |
| `Has(fremd::RDTSCP)` | accepted | **`N054`** |
| `Has(Platten.slots)` | accepted | **`N054`** |
| `Has(RDTSCP, XSAVE)` | accepted (`N053` at a device, about the SECOND argument) | **`N054`** |

**64 of 66 cells gave `0 errors` before; 30 of 66 do now, and those 30 are exactly the five
bare-name forms × six positions.**

### 5.1 The half that is decidable, and why `Has(a, b)` is the sharpest of the five

`Has(RDTSCP, XSAVE)` reads as a demand for two features and is a demand for one.
`namen.rs::has_aus_pred` takes `argumente.first()` and has since 2026-08-19; the rest of the
list has never been read by anybody, in any pass. *A form whose second half is silently
dropped is the shape this folder pays for over and over.*

That half — the SHAPE — needs no list, no table and no new word, and it is what `N054` takes.

### 5.2 The half that is NOT decidable, and who would have to decide it

**Whether `RDTSCP` is a feature of the machine cannot be answered in this tree.**
`SPRACHE.md` (x86_64 assumption catalogue, A14) says where the answer would come from:

> **witnesses**: the CPUID probe is the only generator of `ghost Has(Feature)` (affine, like
> `Vis` — a capability does not expire)

That probe does not exist. No `mints Has(F)` form exists. **Nothing in the language declares
a feature name**, and the whole tree writes exactly one `Has(…)` site
(`beispiele/11-grammatikbefunde.gab`, `Has(RDTSCP)`).

So the name can be checked **only against a declared list**, and the owner's decision is
which of two shapes that list takes:

| shape | cost | precedent |
|---|---|---|
| **a house table in the checker, per `arch`** — the feature names of CPUID leaves 0/1/7, held the way `cnamen.rs::SIGNATUR` holds the names C has taken | **no new word**; the vocabulary ratchet does not move | `cnamen.rs` (`N041`), `erzeugernamen.rs` (`N042`) — both are tables, not passes, and both issue a refusal from `namen.rs` |
| **a language form that mints the witness** — a `features { … }` declaration, or `check`/`assume` establishing `Has(F)` | **a new word**, and the ratchet stands at 221 / 208 / 333 | none; `TODO.md` has carried *"that a `check` or an `assume` ESTABLISHES it is a form that does not exist"* since 2026-08-19 |

**This lane does not choose.** The first shape is available without touching the vocabulary
and has two precedents in the same file; the second is a language change and the ratchet says
no. *Naming it as the owner's call is the result, and the shape half is repaired regardless
of which way it goes.*

### 5.3 And a third thing about `Has`, measured and not repaired

`N016` propagates a feature demand out of an `Axiom` and a `Funktion` and out of nothing
else. **A `reg … requires Has(F)` or a `transition … requires Has(F)` demands a feature that
no caller carries onward** — `gabbro pflichten` books it as `D`, a device promise, and no
pass looks inside. That is the assumption tier working as designed; it is written here so
the design is a decision and not an oversight.

---

## 6 The table, after — and what is still silent

| position | silent before | silent after |
|---|---:|---:|
| `fn … requires` | 13 | 7 |
| `fn … ensures` | 3 | 3 |
| `spec fn` body | 17 | 8 |
| `table … invariant` | 17 | 8 |
| `group … invariant` | 17 | 8 |
| `walk … invariant` | 17 | 8 |
| `walk … down` | 20 | 8 |
| `walk … leaf` | 20 | 8 |
| `traverse … invariant` | 17 | 8 |
| `retry … invariant` | 17 | 8 |
| `retry … until` | 13 | 7 |
| `forever … invariant` | 17 | 8 |
| `reg … requires` | 8 | 8 |
| `transition … requires` | 8 | 8 |
| `axiom … requires` | 20 | 8 |
| `check … floor` | 20 | 8 |
| exchange `when` | 16 | 4 |
| `format … where` | 6 | 6 |
| `fnptr … requires` | 0 | 0 |

| name kind | silent before | silent after | who owns the rest |
|---|---:|---:|---|
| a bare name | 14 | **0** | — |
| an unknown carrier | 14 | **0** | — |
| `result` where none is returned | 14 | **0** | — |
| `aligned(<phantom>, 8)` | 14 | **0** | — |
| a quantifier variable nothing binds | 14 | **0** | — |
| a device register field | 14 | **0** | — |
| `old(<phantom>)` | 15 | 1 | — |
| `sizeof` / `lenof` | 15 | 1 | — |
| a domain place | 7 | 2 | `D017` |
| a `member` domain place | 9 | 4 | `D017` |
| a literal index past the length | 7 | 2 | `M141` |
| `Has(F)` / `Held(L)` / `Has(<lock>)` | 11 / 11 / 13 | 13 / 13 / 15 | **exempt by design — §4** |
| **a call to an undeclared function** | 13 | 13 | `E009`, and it is a HINT |
| **a field of a resolving carrier** | 17 | 17 | `D019` asks this at a domain and nobody in a comparison |
| **`&f`** | 16 | 16 | `M109` reads it in `ensures` only |
| **a `reason` case nothing declares** | 18 | 18 | nobody |
| **`Self` at a function, outside `ensures`** | 15 | 15 | `M120` runs on `ensures` only |

**Five residues, named.** Each is the same shape one level in: the base name resolves and the
thing hanging off it does not. They are measurements and not suspicions — every one of them
was driven, and none is closed by this lane.

---

## 7 The count

| | |
|---|---:|
| `cargo test --offline --no-fail-fast` | **397 probes, 0 red** (393 at `01d69b2` + 4) |
| `zaehle-gifttreffer.py` | **415 probes, 0 missing**, 348 hit alone (mark 271) |
| clean corpus | 108 files, **0** new refusals |
| new refusals | `D021`, `N054` |
| defects repaired without a new refusal | 1 — `Has`/`Held` as a call edge |
| new poison probes | `gift/647`, `648`, `649`, `650` |
| findings in the tree | 1 — `messung/fragmente/F01.gab`:189 |
| ratchets | `zaehle-wortschatz.py` 221/208/333 unmoved · `pruefe-zitate.py` 337 unmoved · `pruefe-saetze.py` 51 unmoved (both new codes carry a sentence) |
