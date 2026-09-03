# The obligation manifest — the completeness half, measured before anything was built

**Running report.** Every finding is committed with the run that produced it.

Measured on `master` @ `94c9ac5`, built on `ki-pc-fisch-101:gabbro-mf`
(`cargo build --offline`, 5.04 s).

---

## 1. The question that had to come first

`messung/gabbrov/manifest-lage.sh` established on 2026-09-03 that **four of ten fragments
emit no manifest at all** and that **10 obligation lines stand against a population of 63**.
It did not say *which* of the two causes each missing line has, and the two are not one
defect:

| cause | whose defect |
|---|---|
| the checker refuses the file, so there is no register to emit | **not the manifest.** Another lane is repairing exactly these four for `H = 0` |
| the file checks clean, the register is emitted, and the obligation is not in it | **the manifest drops it** |

A number that mixes the two is worth nothing. So: the split, with its denominator.

## 2. The split — 63 = 43 + 15 + 5

Search path, three commands, all re-runnable:

```
./messung/gabbrov/manifest-lage.sh                    # per fragment: register or not
./instrumente/zaehle-pflichten.py --spalten           # `L` rows per fragment
./instrumente/zaehle-pflichten.py --gabbrov           # the three rebooked `progress` rows
```

| fragment | population (`L` rows − rebooked) | register? | obligation lines | of the population, lines |
|---|---|---|---|---|
| F01 | 17 | **no** — 3 checker errors | — | 0 |
| F02 | 5 | yes | 5 | **5** |
| F03 | 13 | **no** — 27 checker errors | — | 0 |
| F04 | 7 − 1 = 6 | yes | 1 | 0 |
| F05 | 10 − 1 = 9 | **no** — 4 checker errors | — | 0 |
| F06 | 5 | yes | 1 | 0 |
| F07 | 1 | yes | 0 | 0 |
| F08 | 2 | yes | 1 | 0 |
| F09 | 4 | **no** — 1 checker error | — | 0 |
| F10 | 2 − 1 = 1 | yes | 2 | 0 |
| | **63** | | **10** | **5** |

```
population                                             63
  blocked upstream -- the fragment emits no register    43   (F01 17, F03 13, F05 9, F09 4)
  in a fragment that DOES emit a register               20
      of these, an obligation line exists                5   (F02, all five)
      of these, the manifest DROPS it                   15   (F04 6, F06 5, F07 1, F08 2, F10 1)
```

**43 + 15 + 5 = 63.** The three rebooked `progress` rows (`F04`:886, `F05`:981, `F10`:1656)
leave the population as assumptions, not as obligations —
`instrumente/zaehle-pflichten.py --gabbrov` names all three.

**So the manifest's own defect is 15 of 20, not 53 of 63.** The larger number is somebody
else's repair, and booking it here would be the `W16` shape at the bookkeeping layer: a
measurement that counts a neighbour's hole as its own.

## 3. The reverse direction, and it is the sharper half

The ten emitted lines are not ten of the population. Mapped by hand against
`dokumente/PFLICHTEN.md`, whose anchors point at **`FRAGMENTE.md` at `708beed`** (1 686
lines) and not at today's file:

| emitted line | its clause | row at `708beed` | class |
|---|---|---|---|
| `Vtd :: transition setze_rtp requires` | `requires GSTS…` | F2 454–455 | **L** |
| `Vtd :: transition scharf_te requires` | `requires GSTS…` | F2 457–458 | **L** |
| `Vtd :: transition setze_irtp requires` | `requires GSTS…` | F2 460–461 | **L** |
| `Vtd :: transition scharf_ire requires` | `requires GSTS…` | F2 463–464 | **L** |
| `Vtd :: transition scharf_qie requires` | `requires GSTS…` | F2 466–467 | **L** |
| `VirtioPci :: reg QUEUE_SIZE requires` | `requires QUEUE_SIZE <= QMAX` | F4 764 | K |
| `unberuehrt :: ensures #1` | `ensures result <= s.len` | F6 1084–1085 | K |
| `toeten :: aufloesen requires #1` | `requires Held(SCHEDS, shared)` | F8 1421 / 1436 by text; 1427–1430 by anchor | K, and see below |
| `naechstes_token :: ensures #1` | `ensures result <= 9` | **no row** | — |
| `kerne_zaehlen :: loop invariant #1` | `invariant tiefe <= MAXTIEFE` | **no row** | — |

**Five of ten state an obligation the population contains. Not one of the other five does.**

### The F8 line is the instructive one — an anchor without a text identifies as little as an ordinal without one

`toeten :: aufloesen requires #1` sits at `messung/fragmente/F08.gab`:21, which is frozen
line 1429 — **inside** the `L` row `1427–1430`. By anchor alone it looks like a hit. Its
clause is `requires Held(SCHEDS, shared)`, and that row's obligation is *"the revalidation —
the thread may have vanished between selection and deed"*. **The two are different
statements.** What the clause says is what `PFLICHTEN.md` books at rows 1421 and 1436, both
`K`, both discharged by `H001`/`H006`/`E006`.

*So the anchor field alone would not have settled this line, and the ordinal field settles
nothing at all.* **The text is the field that decides**, and this is the measured argument
for it — the same shape as `O3`'s ordinal defect, one field further out.

### The two F10 lines stand in no row at all — the two sources have drifted

`ensures result <= 9` and `invariant tiefe <= MAXTIEFE` are **not in `FRAGMENTE.md`
at `708beed`**; they were added to `messung/fragmente/F10.gab` afterwards (the file says why
at `:26` and `:46`). The manifest is emitted from `messung/fragmente/F*.gab`; the population
is counted from the frozen `.md`. **They are two coordinate systems, and a line can exist in
one and in no row of the other.**

*That is not an argument against either file.* It is the reason a completeness check has to
name which side it counts — and why the guard prints both sides rather than a ratio.

## 4. Which fifteen are dropped, and why the emitter cannot see ten of them

| fragment | dropped rows | the clause | why no line |
|---|---|---|---|
| F04 | 773, 774, 775–776, 777–779 | `transition ack \| drv \| featok \| drvok` | the register books a `transition` only when it carries a `requires`; these four carry `effects` and none |
| F04 | 780–782 | — | **gap «B26»**: no placeholder for the pre-state, the clause is not writable |
| F04 | 836 | — | no clause says it |
| F06 | 1070–1072 | — | **gap «B14»** |
| F06 | 1094 | — | a `return` inside a `traverse`; no clause |
| F06 | 1129–1141, 1145–1158 | `check … claim "…"` | a `claim` produces no obligation |
| F06 | 1160 | `counterprobe … expects …` | no obligation line |
| F07 | 1289–1291 | — | a property of the PHASE; no clause states it |
| F08 | 1427–1430, 1439–1442 | `match` over `aufloesen` | the correctness of the branch carries no clause |
| F10 | 1631–1632 | `magie : u32 where magie == MAGIE` | a `format … where` produces no obligation line |

**Ten of the fifteen have no clause in the source at all.** For those a manifest line would
have to be *invented* — refused, and named here instead. **Five have a clause the checker
reads and the register does not book**: the four `transition`s without `requires`, and the
`format … where`. Those five are a separate decision from this lane's — a `transition`
without `requires` states a protocol step, not a promise, and booking it would change what
the `D` count means.

*The distinction is why this section stands here rather than a single number: fifteen reads
as fifteen repairable drops, and at most five are.*

---

## 5. The reader census — taken before the writer moved

`AUFTRAG-GABBROV.md` §4 puts the order of a format change in three steps and calls it *half
the rule*. Step zero is counting the readers, because the failure `CLAUDE.md` records is not
a loud one: **seven guards read a document, four went silently blind when it moved.**

**Three readers parse the plain register text.** Counted by sweeping the tree for every
distinctive string the emitter writes (`Obligation register`, `What a HUMAN still owes`,
`no generated proof obligation`, `obligations:`, each of the eight kind headings, the ` :: `
entry form, `has errors -- no register`):

| reader | what it reads | what a silent format change would do |
|---|---|---|
| `crates/gabbro-check/tests/beispiele.rs`:535 | three substrings of the F04 register | red, loudly — a test |
| `instrumente/pruefe-zahlen.py`:71 (`PFLICHTEN_SUMME`) | the `== N obligations: …` header, summed over `beispiele/*.gab` | **silent**: the pattern stops matching, the sum becomes `0`, and `0` travels to a green report |
| `messung/gabbrov/manifest-lage.sh`:39,44 | `no register` and `^== N obligations` | **silent**: every fragment reads as `0 obligations` — the very number this script exists to report |

**Two of the three go silently wrong**, and both in the direction that makes the manifest
look *emptier* than it is.

**Six tools and one test module read the SAME register through a different serialisation**
and are untouched by a change to `pflichten::zeige` — `refinement::verdicts` (`--isabelle`)
and `lean::verdicts` (`--lean`) both walk `pflichten::sammle`:

`instrumente/zaehle-p6.py` · `instrumente/pruefe-p6-beweis.sh` · `instrumente/zaehle-lean.py`
· `instrumente/pruefe-lean-beweis.sh` · `instrumente/miss-lean-gegen-isabelle.py` ·
`instrumente/miss-lean-reichweite.py` · `crates/gabbro-check/tests/rechenwerk.rs`

**Two registries know the subcommand and its flags** without reading the format:
`crates/gabbro-cli/tests/fahnen.rs`, `crates/gabbro-cli/tests/erstnamen.rs`.

*So: **3** readers to prepare, **7** siblings that share the register but not the text, **2**
registries. The number that mattered was three, and it was small enough that the ordering
rule cost almost nothing — which is the argument for keeping it, not against it.*

### Step 1 — the version field, and both silent readers now refuse

`pflichten::MANIFESTFASSUNG` writes `-- manifest-version 1` as **line one**, before the file
name. All three readers gained a gate on the same day, and the two silent ones were
speech-tested against a fabricated `-- manifest-version 99`:

```
GABBRO=/tmp/fakegabbro ./messung/gabbrov/manifest-lage.sh      -> exit 2, "NOTHING was measured"
<the awk of PFLICHTEN_SUMME over the same input>               -> exit 3, "nothing summed"
```

`cargo test --offline --no-fail-fast` **at this step**: **401 passed, 0 failed** (400 at
`94c9ac5`, plus the new `das_register_traegt_seine_fassung_auf_zeile_eins`);
`pruefe-zahlen.py` green. *This is a running report, so each step states the run it was
measured at — §8 carries the figure for the finished tree.*

### Step 2 — every reader on both formats, before either moved

Widened to `{1, 2}` **while the emitter still writes 1**. That order is the rule: a reader
taught the new format *after* the writer moved has a window in between in which it reports a
number out of a format it cannot read.

* `instrumente/pruefe-zahlen.py` — `FASSUNGEN_BEKANNT = "1, 2"`
* `messung/gabbrov/manifest-lage.sh` — `FASSUNGEN_BEKANNT="1 2"`
* `crates/gabbro-check/tests/beispiele.rs` — reads through the Rust API, where a format
  change is a **compile error** and not a silent one. The ordering rule exists against
  silence, so the compiler is its gate here and the version test pins the line.

Both text readers sum the `== N obligations:` header, and that header is unchanged across
the two formats — so both parse to the same figure today. *The gate is for the change after
this one, and that is exactly when a version field is worth having.*

### `E1`, wired in — `instrumente/pruefe-manifest.py`

`AUFTRAG-GABBROV.md` §5: *"E1 is WIRED INTO the tool, not hung beside it: the run ends with
a comparison of the two line counts and aborts on a divergence. A tool that does not check
its own completeness has none."* There are **two** comparisons and they live in two places,
because one of them needs a document the compiler has never heard of:

| | where | what it holds |
|---|---|---|
| **inner** | `pflichten.rs::zeige` itself, plus a read-back in the guard | what the emitter **wrote** against what it **counted** — the check against a new obligation kind quietly missing from the print loop while the header already counts it |
| **outer** | the guard | what the manifest **carries** against the **population** it is about — `dokumente/PFLICHTEN.md`, which `gabbro` neither reads nor should |

The guard carries three speech probes, and they run before it measures anything:

```
beide Fassungen:      ok (v1 und v2 ergeben dieselben zwei Zeilen)
unbekannte Fassung:   ok (v99 und eine fehlende Zeile fallen beide)
unterschlagene Zeile: ok (Kopfzahl und Zeilenzahl laufen auseinander)
```

**And it is red on today's tree, which is the point:**

```
GabbroV's obligation population                        63
obligation lines the manifest carries                  10
NOT carried                                            53
   of which: fragments with NO register at all         4 of 10

E1 GEFALLEN: 53 of 63 obligations reach no manifest line.        exit 1
```

Return code `1` and not `2`: everything was measured and something is open — the tree has to
change, not the setup (`zaehle-p6.py`'s sixth requirement). It joins the two guards already
red at `master`, and it goes green when the manifest carries its subject.

*The guard never prints the bare 53.* The split between blocked and dropped is a judgement
over `PFLICHTEN.md` and not a measurement, so the tool points at §2 of this file for it
rather than inventing a number it cannot derive.

**Carried numbers, all measured by removing the file and putting it back** — not added and
not chosen: `pruefe-widerruf.py` 190 → 191 files, `pruefe-waechter.py` 53 → 54 guards that
can abort mid-run, 312 → 320 exits behind the first, 58 → 59 instruments carrying all five
requirements, 30 → 31 guardians in `README.md`.

### Step 3 — the format, and `O3` closed at the line

`MANIFESTFASSUNG = 2`. Each obligation is now the record `SPRACHE.md` §15 sketched, tab
separated after the keyword:

```
obligation<TAB>name<TAB>class<TAB>anchor<TAB>state<TAB>obligation text
```

The kind headings stay above the records, so the three readers that grep them keep working.

**The counter-check `OFFEN.md` `O3` asks for.** Swap the first and third `ensures` conjunct
of `beispiele/01-tabelle.gab`, normalise the file name away, and diff:

```
15c15
< obligation  aushaengen :: ensures #1  N  SRC:91  open  c.slots[s].elter == None
> obligation  aushaengen :: ensures #1  N  SRC:91  open  c.slots[s].naechstes == None
17c17
< obligation  aushaengen :: ensures #3  N  SRC:93  open  c.slots[s].naechstes == None
> obligation  aushaengen :: ensures #3  N  SRC:93  open  c.slots[s].elter == None
```

Two lines differ where none did before. **And note what does NOT differ: the name and the
anchor.** `ensures #1` still names one thing before the swap and another after, and
`SRC:91` still points at the first conjunct's line, whichever conjunct that is.

> **So §15's sentence needs its own correction, and this is the measured form of it.**
> *"The ratchet runs over names; exchange is visible."* — the second half does not follow
> from the first. A ratchet over the NAME still cannot see this swap; a ratchet over the
> **line** can, and only because the text field is in it. **The name is not an identifier
> and the text is not decoration** — whoever wires the ratchet takes the line.

*The prior lane's warning was exactly right and is now demonstrated rather than argued:*
`--lean` carries the disambiguating term under an ambiguous name, and copying that shape
would have inherited the defect.

### What the fields cost, measured over the whole corpus

110 obligation lines over `beispiele/`, `messung/fragmente/`, `messung/*/` and
`programmlogik/*/`:

| | |
|---|---|
| lines with an anchor | **110 of 110** |
| lines with a text | **110 of 110** |
| texts truncated | **0** (longest 106 characters; the limit is 400) |
| duplicate names within one unit | **0** |
| duplicate whole lines within one unit | **0** |

**Two of these were not free, and both were found by measuring rather than by design.**

* **Six of 110 texts were cut mid-clause** at the certificate's 72-character limit —
  including two `forall x in chain(…)` postconditions and a `!exists m in mappings of …`,
  the ones that say the most. `zeremonie::schnitt` now names its limit at the call site
  (`schnitt_bis`); the folding stays in one place, only the stopping point varies. *One
  routine, two limits is not the thing "one site, one cut" forbids — two routines is.*
* **Four `maintains` lines came out with `--` as their text**, and the reason was a lookup
  that was too narrow: `antwortpflicht_paarig` (twice), `kind_zeigt_zurueck` and
  `belegt_hat_adresse` are `invariant <name> … : <pred>` at a `table` or a `group`, not
  `spec fn`s. *An empty field with a reason is honest; an empty field whose reason is that
  the lookup was too narrow is a hole wearing a reason's clothes.* Three producers now, and
  the corpus has no `--` left.

### The duplicate name is latent, not absent

A body with two calls to the same callee produces two obligations whose names are
byte-identical (`caller :: callee requires #1`, twice). **No unit in the tree has such a pair
today** — measured per file, not over the concatenation, which is why the anchor for a `V`
obligation is the **call site** and not the callee's clause. *The field closes the duplicate
before it is written rather than after somebody meets it.*

### `E1` inside the tool

`zeige` now counts the records it wrote and compares them against `sammle`'s length. It
catches what the balance `debug_assert` cannot: the print loop walks a fixed list of eight
kinds, so a ninth added to `Art` and forgotten there would be **counted in the header and
printed in no line**. On divergence the register says `E1 FAILED` and
`gabbro pflichten` exits non-zero — a hard check and not a `debug_assert`, because a release
build that loses a kind loses it in the artefact a stranger reads.

---

## 6. The counter-check — five real rows, read without the source

`AUFTRAG-GABBROV.md` §4: *"Counter-check on five real lines from `PFLICHTEN.md`, one of them
from F1 with table identity: the text must be understandable without looking at the source."*
Drawn across four fragments and both classes, and the F1 row is the one that decides the
question.

| # | `PFLICHTEN.md` row | the manifest line, verbatim from the run |
|---|---|---|
| 1 | **F2 454–455** `setze_rtp` — TE off or RTPS already set (L) | `Vtd :: transition setze_rtp requires` · `D` · `F02.gab:79` · `open` · **`GSTS.TES == 0 \|\| GSTS.RTPS == 1`** |
| 2 | **F2 463–464** `scharf_ire` — IRTPS set and CFIS clear (L) | `Vtd :: transition scharf_ire requires` · `D` · `F02.gab:88` · `open` · **`GSTS.IRTPS == 1 && GSTS.CFIS == 0`** |
| 3 | **F4 764** the device's `QUEUE_SIZE` lies below QMAX (K) | `VirtioPci :: reg QUEUE_SIZE requires` · `D` · `F04.gab:82` · `open` · **`QUEUE_SIZE <= QMAX`** |
| 4 | **F6 1084–1085** the returned depth does not exceed the stack (K) | `unberuehrt :: ensures #1` · `N` · `F06.gab:191` · `open` · **`result <= s.len`** |
| 5 | **F1 188–190** `cdt_wohlgeformt` — every slot reaches the root via `parent` (**L, table identity**) | `aushaengen :: baum_wohlgeformt` · `E` · `01-tabelle.gab:94` · `open` · **`forall s in slots of c : c.slots[s] reaches WURZEL via elter`** |

**Rows 1–4 read without the source, and rows 1 and 2 are the sharpest case:** before this
change both were the string `Vtd :: transition <name> requires` and nothing else — a reader
could not tell *"TE off or RTPS already set"* from *"IRTPS set and CFIS clear"* without
opening the file. Now the two conditions stand side by side in the artefact.

**Row 5 needs its caveat said out loud, twice over.**

1. **F1 emits no register at all** — three standing checker errors, and another lane is
   repairing them. So the line above is measured at F1's clean sibling in the corpus,
   `beispiele/01-tabelle.gab`, which carries the same statement under German names
   (`baum_wohlgeformt` / `elter` for `cdt_wohlgeformt` / `parent`). *The construct, the
   lookup and the field are the same; the fragment is not.*
2. **This row is the one the text field could NOT have carried by cutting its own clause.**
   The clause is `maintains baum_wohlgeformt` — a NAME. Cutting it would have printed the
   name a second time, and the reader would still be in the dark. The wording comes from
   the `spec fn` the name refers to, resolved inside the unit. *That is why the lookup
   exists, and row 5 is the reason it had to.*

**And the honest limit of row 5**: `forall s in slots of c : c.slots[s] reaches WURZEL via
elter` is understandable, but `WURZEL` is a constant and `slots of c` a domain — both
declared in the same unit, neither in the line. **The text is self-contained down to the
identifiers, not below them.** Resolving those too would inline the unit into every line;
what the field promises is that the *statement* is there, not that the vocabulary is.

## 7. What is still empty, and why

| field | empty where | reason |
|---|---|---|
| **anchor** | nowhere in the corpus (0 of 110) | — |
| **anchor** | every line, when the run has no source | `gabbro pflichten` always has one; the API caller may not, and then the register says so once instead of printing an empty cell per line |
| **text** | nowhere in the corpus (0 of 110) | — |
| **text** | a `maintains I` / `refines g` whose name is no `spec fn` with a predicate body and no `table`/`group` invariant in the unit | the wording is not in this unit. **The name is not printed a second time to fill the column** — an anchor that points at the wrong line is worse than none, and so is a text that repeats the name |
| **state** | never | one value today, `open`, and the register's own second line has said so since the day it existed. It is written out because the reader on the other side writes `passed`/`refuted`/`open` back, and a field that appears only once something is written into it cannot be read before then |
| **the anchor of the call site**, for the 7 kinds that are not `V` | always | those seven arise AT their clause, so there is nothing else to point at |
| **the `L`/`K` class of `PFLICHTEN.md`** | every line | deliberate, and it stays. The register's own closing lines say why: *the K/A/W classification is a JUDGEMENT*, and a tool that guessed would be the silent answer this folder writes against |

---

## 8. The runs

| | |
|---|---|
| `cargo test --offline --no-fail-fast` | **402 passed, 0 failed** (400 at `94c9ac5`, plus two new probes) |
| `./instrumente/abnahme.py` (full, `ki-pc-fisch-101`) | **ROT: 3 of 51 measuring guards report a finding** — `pruefe-grammatiktafel.py` and `zaehle-karten.py`, both already red at `master` and neither this lane's, **plus `pruefe-manifest.py`, which is red by construction until the manifest carries its subject** |
| `./instrumente/pruefe-manifest.py` | exit `1`, three speech probes green, `53 of 63 obligations reach no manifest line` |
| `./instrumente/mutiere-pruefer.py --anker` | **384 of 384** |
| `pruefe-zahlen.py` · `-todo` · `-englisch` · `-waechter` · `-widerruf` · `-kennungen` · `-zitate` | green |

**Two mutations touch this work, and one of them is new:**

* `eine-art-wird-gezaehlt-und-nicht-gedruckt` — drops `Art::Nachbedingung` from `zeige`'s
  print list. **Exactly the shape the inner `E1` exists for**, and the balance
  `debug_assert` beside it does not see it, because the header still adds up while the body
  is short. Measured: it compiles and it is caught.
* `geraetezusage-wird-nicht-gezaehlt` — carried over, because the line it pinned now needs
  the clause's span. **`--anker` reported it the same day and by name**, which is what that
  mode is for: a mutation whose anchor has moved measures nothing and reads like coverage.

**Numbers carried, every one by removing the cause and putting it back**, never by adding:
`pruefe-widerruf.py` 190 → 191 files · guards that can abort mid-run 53 → 54 · exits behind
the first 312 → 320 · instruments carrying all five requirements 58 → 59 · `README.md`
guardians 30 → 31 · mutation catalogue 383 → 384 · line continuations 3191 → 3203.

*If a second lane moves any of these for a different file today, the merged truth is one
higher and is to be re-measured there — not added and not chosen.*
